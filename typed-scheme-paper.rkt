#lang racket

(require syntax-spec
         (for-syntax syntax/parse racket/match))

; following along with https://www.cs.tufts.edu/~nr/cs257/archive/sam-tobin-hochstadt/typed-racket-popl-08.pdf

(syntax-spec
  (binding-class typed-var #:binding-space ts)
  (extension-class typed-macro #:binding-space ts)
  (extension-class type-macro #:binding-space ts/type)

  (nonterminal typed-expr
    #:allow-extension typed-macro
    #:binding-space ts
    (~> x:id
        #:when (hash-has-key? builtins (syntax->datum #'x))
        #'(rkt x))
    ; for builtins only
    (rkt e:racket-expr)
    x:typed-var
    (if cnd:typed-expr thn:typed-expr els:typed-expr)
    (lambda ([x:typed-var (~datum :) t:type-expr]) body:typed-expr)
    #:binding (scope (bind x) body)
    b:boolean
    n:number
    (~> (f arg) #'(#%app f arg))
    (#%app f:typed-expr arg:typed-expr))

  (nonterminal type-expr
    #:allow-extension type-macro
    #:binding-space ts/type
    Top
    Bottom
    Number
    b:boolean
    (-> arg-type:type-expr ret-type:type-expr)
    (-> arg-type:type-expr latent-predicate:type-expr ret-type:type-expr)
    (U type:type-expr ...+))

  (host-interface/expression
    (typed-scheme e:typed-expr)
    (typecheck #'e)
    #'(compile-expr e))

  (host-interface/expression
    (infer e:typed-expr)
    (define-values (t pred) (infer-type #'e))
    #`'#,(list (type->datum t) (visible-predicate->datum pred))))

(define-syntax compile-expr
  (syntax-parser
    #:datum-literals (rkt if lambda : #%app)
    [(~or e:id e:number e:boolean) #'e]
    [(rkt e) #'e]
    [(if cnd thn els)
     #'(if (compile-expr cnd)
           (compile-expr thn)
           (compile-expr els))]
    [(lambda ([x : _]) body)
     #'(lambda (x) (compile-expr body))]
    [(#%app f e)
     #'((compile-expr f) (compile-expr e))]))

(define-syntax-rule
  ; new must be an id
  (define-type-alias new old)
  (define-dsl-syntax new type-macro
    (syntax-parser
      [_ #'old])))
(define-type-alias Any Top)
(define-type-alias Never Bottom)
(define-type-alias Boolean (U #t #f))

; Represents the result of a program
(define (value? v)
  (or (boolean? v) (number? v) (procedure? v)))

(begin-for-syntax
  ;; data definitions ;;

  ; Universal supertype. any
  (struct top [] #:transparent)
  ; Universal subtype. never
  (struct bottom [] #:transparent)
  (struct union-type [members] #:transparent)
  ; Function type. Predicate communicates type information about the argument
  (struct function-type [arg-type predicate ret-type])
  (struct number-type [] #:transparent)
  (define (boolean-type) (union-type (list #t #f)))
  ; Represents the type of an expression
  (define (type? v)
    (match v
      [(or (struct* top ())
           (struct* bottom ())
           (union-type (list (? type?) ...))
           (function-type (? type?) (? latent-predicate?) (? type?))
           #t
           #f
           (struct* number-type ()))
       #t]
      [_ #f]))

  ; Represents an empty predicate. Denoted as a dot in the paper.
  (struct nothing [] #:transparent)
  ; If a type, then the function returning true means the argument is of the type, and false means it's not.
  ; Otherwise, no type information is communicated.
  (define (latent-predicate? v)
    (or (type? v) (nothing? v)))

  ; The expression returns a boolean representing whether var is of type.
  (struct annotation [var type] #:transparent)
  ; Represents type-relevant information that an expression's result tells us.
  ; Although visible is in the name, this is NOT in the surface syntax.
  (define (visible-predicate? v)
    (match v
      [(or
        ; the expression evaluates to whether the variable is of that type
        (annotation (? symbol?) (? type?))
        ; the expression evaluates to the value of a variable
        (? symbol?)
        ; the expression evaluates to #t
        #t
        ; the expression evaluates to #f
        #f
        ; no extra type-relevant information
        (? nothing?))
       #t]
      [_ #f]))

  ; typed-expr -> void
  ; ensure the expression is well-typed.
  (define (typecheck stx)
    (infer-type stx)
    (void))

  ; an Env is an (immutable-symbol-table/c type?)

  ; Env typed-var type? -> Env
  (define (extend-type-env type-env x t)
    (symbol-table-set type-env x t #:allow-overwrite? #t))
  ; Env typed-var -> type?
  (define (lookup-type type-env x)
    (symbol-table-ref type-env x
                      (lambda ()
                        (raise-syntax-error (syntax->datum x) "unbound identifier" x)))
    #;(hash-ref builtins (syntax->datum x)
              (lambda ()
                (symbol-table-ref type-env x
                                  (lambda ()
                                    (raise-syntax-error (syntax->datum x) "unbound identifier" x))))))

  ; Env visible-predicate? -> Env
  ; Update the environment to reflect that the predicate holds
  (define (type-env-add env pred)
    (match pred
      ; this may have intro scope weirdness, probably fine
      [(annotation x t) (extend-type-env env x (restrict-type (lookup-type env x) t))]
      [(? identifier? x) (extend-type-env env x (remove-type (lookup-type env x) #f))]
      [_ env]))

  ; Env visible-predicate? -> Env
  ; Update the environment to reflect that the predicate does not hold.
  (define (type-env-subtract env pred)
    (match pred
      ; this may have intro scope weirdness, probably fine
      [(annotation x t) (extend-type-env env x (remove-type (lookup-type env x) t))]
      [(? identifier? x) (extend-type-env env x #f)]
      [_ env]))

  ; type? type? -> type?
  ; x:t1 is in the env. x is t2 is known to hold. update x's type.
  ; like intersection
  (define (restrict-type t1 t2)
    (if (subtype? t1 t2)
        ; the env already has a more precise type for x
        t1
        (match t2
          [(union-type types)
           (union-type (for/list ([t2 types]) (restrict-type t1 t2)))]
          ; t2 is more precise than t1 (or a completely different type)
          [_ t2])))

  ; type? type? -> type?
  ; x:t1 is in the env. x is t2 is known to not hold. update x's type.
  ; like subtracting t2 from t1
  (define (remove-type t1 t2)
    (if (subtype? t1 t2)
        ; t1 <: t2 and x is not t2, so x can't be anything
        (bottom)
        (match t2
          [(union-type types)
           (union-type (for/list ([t2 types]) (remove-type t1 t2)))]
          ; nothing to subtract from t1
          [_ t1])))

  (define builtins
    (hasheq
      'add1 (function-type (number-type) (nothing) (number-type))
      'not (function-type (top) (nothing) (boolean-type))
      'procedure? (function-type (top)  (function-type (bottom) (nothing) (boolean-type)) (bottom))
      'number? (function-type (top) (number-type) (boolean-type))
      'boolean? (function-type (top) (boolean-type) (boolean-type))))

  ; typed-expr -> (values type? visible-predicate?)
  (define (infer-type stx [env (immutable-symbol-table)])
    (syntax-parse stx
      #:datum-literals (rkt if lambda : #%app)
      ; T-Abs
      [x:id (values (lookup-type env #'x) #'x)]
      ; T-Const
      [(rkt (#%host-expression x:id))
       (values (hash-ref builtins (syntax->datum #'x)
                         (lambda () (raise-syntax-error #f "unknown builtin" #'x)))
               #t)]
      [(rkt _) (values (top)
                       (nothing))]
      ; T-Num
      [n:number (values (number-type) #t)]
      ; T-True T-False
      [b:boolean (values (syntax->datum #'b) (syntax->datum #'b))]
      ; T-Abs T-AbsPred
      [(lambda ([x : type-expr]) body)
       (define arg-type (parse-type #'type-expr))
       (define env^ (extend-type-env env #'x arg-type))
       (define-values (ret-type visible-pred) (infer-type #'body env^))
       (define latent-pred
         (match visible-pred
           [(annotation annot-var annot-type)
            (if (compiled-identifier=? annot-var #'x)
                ; T-AbsPred
                annot-type
                ; T-Abs
                (nothing))]
           ; T-Abs
           [_ (nothing)]))
       (values (function-type arg-type latent-pred ret-type)
               #t)]
      ; T-App T-AppPred T-AppPredTrue T-AppPredFalse
      [(#%app rator rand)
       (define-values (rator-type retor-pred) (infer-type #'rator env))
       (define-values (rand-type rand-pred) (infer-type #'rand env))
       (match rator-type
         [(function-type arg-type latent-pred ret-type)
          (assert-subtype! rand-type arg-type #'rand)
          (define visible-pred
            (cond
              ; T-AppPred
              [(and (type? latent-pred)
                    (identifier? rand-pred))
               (annotation rand-pred latent-pred)]
              ; T-AppPredTrue T-AppPredFalse
              [(type? latent-pred)
               (if (subtype? rand-type latent-pred)
                   #t
                   ; T-AppPredFalse
                   ; TODO make this #f once you figure out what v closed means
                   (nothing))]
              ; T-App
              [else (nothing)]))
          (values ret-type visible-pred)]
         [_ (raise-syntax-error #f "type error: application of a non-procedure" this-syntax #'rator)])]
      ; T-If T-IfTrue T-IfFalse
      [(if cnd thn els)
       (define-values (cnd-type cnd-pred) (infer-type #'cnd env))
       (define-values (thn-type thn-pred) (infer-type #'thn (type-env-add env cnd-pred)))
       (define-values (els-type els-pred) (infer-type #'els (type-env-subtract env cnd-pred)))
       (match cnd-pred
         ; T-IfTrue
         ; TODO shouldn't you be able to use thn-pred instead of nothing?
         [#t (values thn-type (nothing))]
         ; T-IfFalse
         [#f (values els-type (nothing))]
         ; T-If
         [_
          (define visible-predicate (combine-predicate cnd-pred thn-pred els-pred))
          (values (smart-union thn-type els-type)
                  visible-predicate)])]))

  ; type? type? -> boolean?
  (define (subtype? t1 t2)
    (with-handlers ([exn:fail:syntax:type-mismatch? (lambda (_) #f)])
      (assert-subtype! t1 t2 #f)
      #t))

  (struct exn:fail:syntax:type-mismatch exn:fail:syntax [] #:transparent)
  ; type? type? (or #f typed-expr) -> void?
  (define (assert-subtype! t1 t2 stx)
    (match* (t1 t2)
      [((bottom) _) (void)]
      [(_ (top)) (void)]
      [(#t #t) (void)]
      [(#f #f) (void)]
      [((number-type) (number-type)) (void)]
      [((function-type arg-type1 latent-predicate1 ret-type1)
        (function-type arg-type2 latent-predicate2 ret-type2))
       (assert-subtype! arg-type2 arg-type1 stx)
       (unless (or (equal? latent-predicate1 latent-predicate2)
                   (equal? (nothing) latent-predicate2))
         (raise-type-mismatch latent-predicate1 latent-predicate2 stx))
       (assert-subtype! ret-type1 arg-type2 stx)]
      [(_ (union-type t2s))
       (unless (for/or ([t2 t2s]) (subtype? t1 t2))
         (raise-type-mismatch t1 t2 stx))]
      [((union-type t1s) _)
       (for ([t1 t1s])
         (assert-subtype! t1 t2 stx))]
      [(_ _) (raise-type-mismatch t1 t2 stx)]))

  ; type? type? -> type?
  ; collapses something like (smart-union #t (U #t #f)) to (U #t #f).
  ; doesn't go deep.
  (define (smart-union t1 t2)
    (cond
      [(subtype? t1 t2)
       t2]
      [(subtype? t2 t1)
       t1]
      [else (union-type (list t1 t2))]))

  ; visible-predicate? visible-predicate? visible-predicate? -> visible-predicate?
  ; combine predicates for an if
  (define (combine-predicate cnd-pred thn-pred els-pred)
    (match* (cnd-pred thn-pred els-pred)
      ; like (if e (number? x) (number? x))
      [(_ pred pred) pred]
      ; like (or (e1 : x is t1) (e2 : x is t2))
      [((annotation x1 t1) #t (annotation x2 t2))
       #:when (compiled-identifier=? x1 x2)
       (annotation x1 (smart-union t1 t2))]
      ; cnd is known to be true
      [(#t pred _) pred]
      ; cnd is known to be false
      [(#f _ pred) pred]
      ; (if (number? x) #t #f) is same as (number? x)
      [(pred #t #f) pred]
      [(_ _ _) (nothing)]))

  ; type? type? (or #f typed-expr) -> void?
  (define (raise-type-mismatch t1 t2 stx)
    (raise-syntax-error #f (format "type mismatch: expected ~a, but got ~a" (type->datum t1) (type->datum t2)) stx #:exn exn:fail:syntax:type-mismatch))

  ; type-expr -> type?
  (define (parse-type stx)
    (syntax-parse stx
      #:datum-literals (Top Bottom Number Boolean -> U)
      [Number (number-type)]
      [Top (top)]
      [Bottom (bottom)]
      [#t #t]
      [#f #f]
      [(U t ...) (union-type (map parse-type (attribute t)))]
      [(-> arg-type ret-type)
       (function-type (parse-type #'arg-type) (nothing) (parse-type #'ret-type))]
      [(-> arg-type latent-type ret-type)
       (function-type (parse-type #'arg-type) (parse-type #'latent-type) (parse-type #'ret-type))]))

  ; type? -> Any
  (define (type->datum type)
    (match type
      [(number-type) 'Number]
      [(top) 'Top]
      [(bottom) 'Bottom]
      [(? boolean?) type]
      [(union-type types) (cons 'U (map type->datum types))]
      [(function-type arg-type (nothing) ret-type)
       (list '-> (type->datum arg-type) (type->datum ret-type))]
      [(function-type arg-type latent-type ret-type)
       (list '-> (type->datum arg-type) (type->datum latent-type) (type->datum ret-type))]))

  ; visible-predicate? -> Any
  (define (visible-predicate->datum pred)
    (match pred
      [(annotation x t)
       (list (syntax->datum x) ': (type->datum t))]
      [(? identifier? x) (syntax->datum x)]
      [#t #t]
      [#f #f]
      [(nothing) '*])))

(module+ test
  (require rackunit)
  (define-syntax-rule
    (check-infer e t pred)
    (check-equal? (infer e)
                  (list 't 'pred)))
  (check-infer 1
               Number
               #t)
  (check-infer #t
               #t
               #t)
  (check-infer #f
               #f
               #f)
  (check-infer (lambda ([x : Number]) x)
               (-> Number Number)
               #t)
  (check-infer ((lambda ([x : Number]) x)
                2)
               Number
               *)
  (check-infer (lambda ([x : Boolean]) x)
               (-> (U #t #f) (U #t #f))
               #t)
  (check-infer add1
               (-> Number Number)
               #t)
  (check-infer (lambda ([x : Any])
                 (if (number? x)
                     x
                     1))
               (-> Top Number)
               #t)
  (check-infer (lambda ([x : Any]) (number? x))
               (-> Top Number (U #t #f))
               #t)
  (define-dsl-syntax let typed-macro
    (syntax-rules (:)
      [(let ([(x : t) e]) body)
       ((lambda ([x : t]) e)
        body)]))
  (define-dsl-syntax or typed-macro
    (syntax-rules ()
      [(or) #t]
      [(or e) e]
      ; has re-evaluation of a, but oh well. no nice let in the language.
      [(or a b ...) (if a a (or b ...))]))
  (check-infer (or 1 2)
               Number
               *)
  (check-infer (if 1 1 2)
               Number
               *)
  ; IfTrue
  (check-infer (if 1 #t 2)
               #t
               *))
