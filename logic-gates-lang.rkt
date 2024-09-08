#lang racket

; frontend language for logic circuit DSL

(module+ test (require rackunit))
(provide)
(require (for-syntax racket/list racket/match syntax/parse)
         syntax-spec
         "./logic-gates.rkt"
         (prefix-in rt: "./logic-gates.rkt"))

(syntax-spec
  (binding-class wire-var)
  (binding-class module-name
                 #:binding-space logic-module)
  (extension-class module-macro
                   #:binding-space logic-module)
  (nonterminal/exporting module-expr
    #:allow-extension module-macro
    #:binding-space logic-module
    (begin e:module-expr ...+)
    #:binding (re-export e)
    (define-wire x:wire-var)
    #:binding (export x)
    (#%module-app m:module-name x:wire-var ...)
    (~> (m:id x:id ...)
        #'(#%module-app m x ...)))
  (nonterminal wire-type
    #:binding-space logic-wire-type
    in
    out
    inout)

  (host-interface/definition
    (define-module/core (m:module-name [x:wire-var (~datum :) t:wire-type] ...)
      body:module-expr)
    #:binding [(export m) (scope (bind x) (import body))]
    #:lhs [#'m]
    #:rhs [(define ts (for/list ([t (attribute t)]) (parse-type t)))
           (for ([x (attribute x)]
                 [t ts])
             (declare-wire-type! x t))
           (declare-module-type! #'m ts)
           (check-expr #'body)
           #'(compile-define-module (m x ...) body)])
  (host-interface/definition
    (define-gate (m:module-name x:racket-var ...) body:racket-expr ...+)
    #:binding [(export m) (scope (bind x) body)]
    #:lhs [#'m]
    #:rhs [#'(compile-define-gate (m x ...) body ...)])
  (host-interface/definition
    (define-circuit/core c:racket-var body:module-expr)
    #:binding [(export c) (scope (import body))]
    #:lhs [#'c]
    #:rhs [ #'(compile-define-circuit c body)])
  (host-interface/definition
    (define-input x:wire-var)
    #:binding (export x)
    #:lhs [#'x]
    #:rhs [#'(compile-define-input x)])
  (host-interface/definition
    (define-output x:wire-var)
    #:binding (export x)
    #:lhs [#'x]
    #:rhs [#'(compile-define-output x)])
  (host-interface/expression
    (set-input! x:wire-var e:racket-expr)
    #'(compile-set-input! x e))
  (host-interface/expression
    (get-output circ:racket-expr x:wire-var)
    #'(compile-get-output circ x)))

; type-checking

(begin-for-syntax
  (define-persistent-symbol-table module-types)
  ; wire types need to be global because of define-input and and define-output
  (define-persistent-symbol-table wire-types)

  ; a WireType is one of
  ; 'in
  ; 'out
  ; 'inout

  ; a ModuleType is a (Listof WireType)

  (define (parse-type stx)
    (syntax->datum stx))

  ; wire-var Type -> Void
  (define (declare-wire-type! x t)
    (symbol-table-set! wire-types x t))

  ; module-var Type -> Void
  (define (declare-module-type! x t)
    (symbol-table-set! module-types x t))

  ; module-expr -> Void
  (define (check-expr e)
    (define es (flatten-begins e))
    (for ([e es])
      (syntax-parse e
        #:datum-literals (define-wire)
        [(define-wire x)
         (declare-wire-type! #'x 'inout)]
        [_ (void)]))
    (for ([e es])
      (syntax-parse e
        #:datum-literals (#%module-app)
        [(#%module-app m x ...)
         (define expected-ts (symbol-table-ref module-types #'m))
         (unless (= (length expected-ts) (length (attribute x)))
           (raise-syntax-error
            (syntax->datum #'m)
            (format "arity error: expected ~a arguments, but got ~a" (length expected-ts) (length (attribute x)))
            this-syntax))
         (define actual-ts (for/list ([x (attribute x)]) (symbol-table-ref wire-types x)))
         (for ([expected expected-ts]
               [actual actual-ts]
               [x (attribute x)])
           (unless (subtype? actual expected)
             (raise-syntax-error (syntax->datum #'m)
                                 (format "type mismatch: expected a wire of type ~a, but got a wire of type ~a" expected actual)
                                 this-syntax
                                 x)))]
        [_ (void)])))

  ; module-expr -> (Listof module-expr)
  (define (flatten-begins stx)
    (syntax-parse stx
      #:datum-literals (begin define-wire #%module-app)
      [(begin e ...+)
       (define ess (map flatten-begins (attribute e)))
       (append* ess)]
      [_ (list this-syntax)]))

  ; Type Type -> Boolean
  (define (subtype? a b)
    (match (list a b)
      [(or (list 'inout _)
           (list 'in 'in)
           (list 'out 'out))
       #t]
      [_ #f])))

; compilation

#|
module exprs return module objects with interface ports
module definitions emit nullary procedures that produce modules

(define-module (nand a b out)
  (define-wire tmp)
  (and a b tmp)
  (not tmp out))
~>
(define (nand)
  (match-define (module and-ports and-circ) (and))
  (match-define (module not-ports not-circ) (not))
  connect-things-up-and-return-module)

(define (and-rt)
  (define a (input-port))
  (define b (input-port))
  (define out (output-port))
  (define gat (gate (list a b) out (lambda ...)))
  (define circ (circuit (list gate (list) (seteq))))
  (module (list a b c) circ))

alternatively, what if we actually take in the arguments?
but what gets passed?
if modules were procedures, the values they'd get passed are either local wires, interface inputs, or interface outputs
when we hit a gate, we'll have access to these values, whatever they are. Can the gate then construct a circuit that connects to things outside of itself based on these values?

when an input/output hits a gate, one runtime wire should be created
when a local wire hits a gate, idk what can happen.
what if a local wire's value is a list of its runtime wires, it can just add all appropriate connecting runtime wires
but then those new wires will need to get back to the local wire's creator before the next module instantiation.
the local wire could just have mutation.
then a module instantiation would only have to return a circuit, but that circuit would have "dangling wires" connecting to ports outside of it.
I don't like that, but alternatives seem like a pain.
|#

; An Input is a
(struct input [port [value #:mutable]])
; where
; port is an output port
; value is a boolean
; represents a top-level input
; port is an output port because the input's value flows into the circuit

; An Output is a
(struct output [port])
; where
; in is an input port
; represents a top-level output
; port is an input port so the circuit can flow into it with a value

; A ModuleArgument is one of
; An Input
; An Output
(struct local-wire [inputs outputs])
; where
; inputs is a mutable seteq of input ports
; outputs is a mutable seteq of output ports
; represents internal connections between ports

; module applications produce circuits.
; modules are procedures that take in ModuleArguments and return a circuit.
; this circuit contains wires that connect to ports mentioned in the ModuleArguments,
; which are not associated with gates in the circuit.
; this procedure is also expected to mutate local wires with new connections

(define-syntax compile-define-module
  (syntax-parser
    [(_ (m x ...) body)
     (define bodies (flatten-begins #'body))
     (define/syntax-parse
       (((~datum define-wire) wire-name)
        ...
        ((~datum #%module-app) rator rand ...)
        ...)
       (sort-module-exprs bodies))
     #'(lambda (x ...)
         (define wire-name (local-wire (mutable-set)))
         ...
         (apply circuit-union
                (list (rator rand ...)
                      ...)))]))

(begin-for-syntax
  ; (Listof module-expr) -> (Listof module-expr)
  (define (sort-module-exprs bodies)
    (sort bodies <
          (syntax-parser
            #:datum-literals (define-wire #%module-app)
            [(define-wire . _) 0]
            [(#%module-app . _) 1]))))

(define-syntax compile-define-gate
  (syntax-parser
    [(_ (m x ...) body ...)
     (define/syntax-parse (x-value ...) (generate-temporaries (attribute x)))
     (define/syntax-parse (x-port ...) (generate-temporaries (attribute x)))
     #'(lambda (x ... out)
         (define x-port (input-port))
         ...
         (define out-port (output-port))
         (define proc (lambda (x-value ...) body ...))
         (define gat (gate (list x-port ...) out-port proc))
         (circuit (list gat)
                  (module-gate-wires (list x ... out) (list x-port ... out-port))
                  (seteq)))]))

; (Listof ModuleArgument) (Listof Port) -> (Listof Wire)
; take in a gate's module arguments and its ports and generate the appropriate wires.
; also updates local wires.
(define (module-gate-wires args ports)
  (append* (for/list ([arg args]
                      [prt ports])
             (match arg
               [(input out _)
                (unless (input-port? prt)
                  (error "runtime port type error. output passed to gate input"))
                (list (wire out prt))]
               [(output in)
                (unless (output-port? prt)
                  (error "runtime port type error. input passed to gate output"))
                (list (wire prt in))]
               [(local-wire inputs outputs)
                (cond
                  [(input-port? prt)
                   (local-wire-add-input! prt)
                   (for/list ([out outputs])
                     (wire out prt))]
                  [else
                   (local-wire-add-output! prt)
                   (for/list ([in inputs])
                     (wire prt in))])]))))

(define (local-wire-add-input! wir in)
  (set-add! (local-wire-inputs wir) in))

(define (local-wire-add-output! wir out)
  (set-add! (local-wire-outputs wir) out))

(begin-for-syntax
  (define-persistent-symbol-set input-names)
  (define (input-name? id) (symbol-set-member? input-names id)))

(define-syntax compile-define-input
  (syntax-parser
    [(_ x)
     (symbol-set-add! input-names #'x)
     #'(input (output-port) #f)]))

(define-syntax-rule
  (compile-define-output x)
  (output (input-port)))

(define-syntax-rule
  (compile-set-input! x v)
  (set-input-value! x v))

(define
  (compile-get-output circ x)
  (circuit-port-powered? circ (output-port x)))

(define-syntax compile-define-circuit
  (syntax-parser
    [(_ c body)
     (define free-ids (free-identifiers #'body))
     (define/syntax-parse (in ...) (filter input-name? free-ids))
     #'(let ()
         (define in-gates
           (list (gate (list) (input-port in) (lambda () (input-value in)))
                 ...))
         (define in-circ
           (circuit in-gates (list) (seteq)))
         (define-module (m)
           body)
         (circuit-union in-circ (m)))]))

; sugar

(define-syntax define-module
  (syntax-parser
    [(_ (m (~or x [y (~datum :) t]) ...) body ...)
     #'(define-module/core (m [(~? x y) : (~? t inout)] ...)
         (begin body ...))]))

(define-syntax-rule
  (define-circuit c body ...)
  (define-circuit/core c (begin body ...)))

(module+ test
  (test-case "not"
    2

    #;(set-input! in #f)
    #;(circuit-run! circ)
    #;(check-equal? (get-output circ out) #t)))
; in here, we get `not` not bound
(let ()
  (define-gate (not a) (not a))
  (define-input in)
  (define-output out)
  (define-circuit circ (not in out))
  2)

; out here, we get `a` not bout
(define-gate (not a) (not a))
(define-input in)
(define-output out)
(define-circuit circ (not in out))
