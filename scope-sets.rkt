#lang racket

(module+ test (require rackunit))
(require racket/hash)

; little language with hygienig macros using scope sets
; following https://www.youtube.com/watch?v=Or_yKiI3Ha4&t=3s
; grammar:
; <expr> = (lambda (<id>) <expr>)
;        | <id>
;        | (<expr> ...+)
;        | (quote <datum>)
;        | (let-syntax ([<id> <expr>]) <expr>)
;        | (quote-syntax <datum>)

(struct stx [e scopes] #:transparent)
; where
; e is a symbol
; scopes is a set of scopes
(module+ test
  (define sc1 (scope 'sc1))
  (define sc2 (scope 'sc2))
  (define sc3 (scope 'sc3)))

; a binding is a gensym

; an expansion environment, or env, is a (hash binding (or variable transformer))
(define empty-env (hash))
(define (env-extend env k v) (hash-set env k v))
(define (env-lookup env binding) (hash-ref env binding #f))
(define variable (gensym 'variable))

; a transformer is a (stx -> stx)

(define (scope [sym 'sc])
  (gensym sym))

(define (identifier? s)
  (stx? s))

(define (datum->stx v)
  (cond
    [(stx? v) v]
    [(symbol? v) (stx v (set))]
    [(list? v) (map datum->stx v)]
    [else v]))

(define (stx->datum s)
  (cond
    [(stx? s) (stx-e s)]
    [(list? s) (map stx->datum s)]
    [else s]))

; stx scope ((set-of scope) scope -> (set-of scope))
(define (adjust-scope s sc op)
  (cond
    [(stx? s)
     (stx
      (stx-e s)
      (op (stx-scopes s) sc))]
    [(list? s)
     (map (lambda (e) (adjust-scope e sc op)) s)]
    [else s]))

(define (add-scope s sc) (adjust-scope s sc set-add))
(define (flip-scope s sc) (adjust-scope s sc (lambda (scs sc) (if (set-member? scs sc)
                                                                  (set-remove scs sc)
                                                                  (set-add scs sc)))))

(module+ test
  (check-equal? (add-scope (list (stx 'x (set))
                                 (stx 'y (set sc1)))
                           sc1)
                (list (stx 'x (set sc1))
                      (stx 'y (set sc1))))
  (check-equal? (flip-scope (list (stx 'x (set))
                                  (stx 'y (set sc1)))
                            sc1)
                (list (stx 'x (set sc1))
                      (stx 'y (set)))))

; bindings
; maps identifiers to bindings. note identifiers are stx objects
(define all-bindings (make-hash))
; identifier binding -> void
(define (add-binding! id binding)
  (hash-set! all-bindings id binding))

; identifier -> (or #f binding)
(define (resolve id)
  (define candidate-ids
    (find-all-matching-bindings id))
  (cond
    [(pair? candidate-ids)
     (define max-id
       (argmax (compose set-count stx-scopes)
               candidate-ids))
     (check-unambiguous max-id candidate-ids)
     (hash-ref all-bindings max-id)]
    [else #f]))

; identifier -> (list-of identifier)
; find all bindings of the same name with scope sets that id's scope set is a superset of
(define (find-all-matching-bindings id)
  (for/list ([c-id (in-hash-keys all-bindings)]
             #:when (and (eq? (stx-e c-id) (stx-e id))
                         (subset? (stx-scopes c-id)
                                  (stx-scopes id))))
    c-id))

; identifier (list-of identifier) -> void
(define (check-unambiguous max-id candidate-ids)
  (for ([candidate-id candidate-ids])
    (unless (subset? (stx-scopes candidate-id)
                     (stx-scopes max-id))
      (error 'check-unambiguous "ambiguous: ~a" max-id))))

(define core-scope (scope 'core))

(define core-forms
  (set 'lambda 'let-syntax 'quote 'quote-syntax))
(define core-primitives
  (set 'datum->syntax 'syntax->datum 'syntax-e 'list 'cons 'first 'second 'rest 'map))
(for ([sym (set-union core-forms core-primitives)])
  ; bound to their own name as a binding
  (add-binding! (stx sym (set core-scope)) sym))
(define (introduce s)
  (add-scope s core-scope))

; expansion

(define (expand-datum datum)
  (expand (introduce (datum->stx datum))))

(define (expand s [env empty-env])
  (cond
    [(identifier? s)
     (expand-identifier s env)]
    [(and (pair? s)
          (identifier? (first s)))
     ; application of identifier, maybe a macro
     (expand-id-application-form s env)]
    [(list? s)
     ; application of non-identifier
     (expand-app s env)]
    [else
     (error "bad syntax: " s)]))

(define (expand-identifier s env)
  (define binding (resolve s))
  (cond
    [(not binding) (error "unbound variable: " s)]
    [(set-member? core-primitives binding) s]
    [(set-member? core-forms binding) (error (format "~a: bad syntax" binding))]
    [else
     (define v (env-lookup env binding))
     (cond
       [(eq? v variable) s]
       ; an identifier used outside of its context
       [(not v) (error "out of context: " s)]
       ; like a macro used as an identifier. TODO support this
       [else (error "bad syntax: " s)])]))

; might be a macro invocation, or just a regular application
(define (expand-id-application-form s env)
  (define binding (resolve (first s)))
  (case binding
    [(lambda) (expand-lambda s env)]
    [(let-syntax) (expand-let-syntax s env)]
    [(quote) s]
    [(quote-syntax) s]
    [else
     (define v (env-lookup env binding))
     (cond
       [(procedure? v)
        ; apply macro then recur
        (expand (apply-transformer v s) env)]
       [else
        ; function call
        (expand-app s env)])]))

; applies transformer to syntax and handles intro scopes
(define (apply-transformer t s)
  ; no need for use site since no recursion
  (define intro-scope (scope 'intro))
  (define intro-s (add-scope s intro-scope))
  (define transformed-s (t intro-s))
  (flip-scope transformed-s intro-scope))

(define (expand-app s env)
  ; just expand each subform
  (map (lambda (sub-s) (expand sub-s env))
       s))

(define (expand-lambda s env)
  (match-define `(,lambda-id (,arg-id) ,body) s)
  ; create lambda scope
  (define sc (scope 'lambda))
  ; paint it onto arg-id
  (define id (add-scope arg-id sc))
  ; bind id
  (define binding (gensym (stx-e arg-id)))
  (add-binding! id binding)
  ; add binding to env
  (define body-env (env-extend env binding variable))
  ; expand function body after adding scope
  (define exp-body (expand (add-scope body sc)
                           body-env))
  ; rebuild expanded form
  `(,lambda-id (,id) ,exp-body))

(define (expand-let-syntax s env)
  (match-define `(,let-syntax-id ([,lhs-id ,rhs]) ,body) s)
  ; ceate let-syntax scope
  (define sc (scope 'let-syntax))
  ; add new scope to the identifier
  (define id (add-scope lhs-id sc))
  ; bind id
  (define binding (gensym (stx-e lhs-id)))
  (add-binding! id binding)
  ; evaluate transformer
  (define rhs-val (eval-for-syntax-binding (stx-e lhs-id) rhs))
  ; map binding to its value
  (define body-env (env-extend env binding rhs-val))
  ; expand body
  (expand (add-scope body sc) body-env))

(define (eval-for-syntax-binding who-sym rhs)
  ; TODO syntax-rules
  #;(eval-compiled (compile (expand rhs empty-env)))
  (match rhs
    [`(,syntax-rules-id ()
        ,clauses
        ...)
     (lambda (s) (run-syntax-rules who-sym s clauses))]
    [_ (error 'let-syntax "~a: bad syntax. macro definitions must use syntax-rules" who-sym)]))

; syntax-rules
; copy paste modified from declare-syntax.rkt

; an Env is a (Hash Symbol (cons Natural SExp))
; mapping a name to its ellipsis depth and the source SExp

; a Pat is one of
; identifier
; ()
; (Pat . Pat)
; (Pat ooo)
; ooo means an ellipsis in the pattern itself
; So ellipsis can only appear at the end of a pattern
; Represents a syntax pattern

; A Template is one of
; Pat
; (Pat ooo . Pat)
; It's a Pat but ellipsis doesn't have to appear at the very end

; Symbol SExpr (Listof (List Pat Template)) -> SExpr
(define (run-syntax-rules who-sym expr clauses)
  (match clauses
    [(cons (list pat tmp) rest-clauses)
     (if (pattern-matches? pat expr)
         (let ([env (pattern-match pat expr)])
           (template-expand tmp env))
         (run-syntax-rules who-sym expr rest-clauses))]
    [_ (error who-sym "bad syntax")]))

; Pat SExpr -> Boolean
; Does the pattern match the expr?
(define (pattern-matches? pat expr)
  (match (list pat expr)
    [(stx '... _) (error 'declare-syntax "invalid use of ellipsis")]
    [(list (? identifier?) _) #t]
    [(list '() '()) #t]
    [(list (list pat (stx '... _))
           (? list? exprs))
     (andmap (lambda (expr) (pattern-matches? pat expr))
             exprs)]
    [(list (cons car-pat cdr-pat)
           (cons car-expr cdr-expr))
     (and (pattern-matches? car-pat car-expr)
          (pattern-matches? cdr-pat cdr-expr))]
    [_ #f]))

; Pat SExpr -> Env
; Build up the environment mapping pattern variables to
; parts of the input SExpr.
; Assumes the pattern matches.
(define (pattern-match pat expr [depth 0])
  (match (list pat expr)
    [(list (? identifier? id) expr)
     (hasheq (stx-e id) (cons depth expr))]
    [(list '() '()) (hasheq)]
    [(list (list pat (stx '... _))
           exprs)
     (define envs
       (for/list ([expr exprs])
         (pattern-match pat expr (add1 depth))))
     (define env^ (combine-envs envs))
     ; this is necessary in case expr is '(). You'd get an empty environment.
     (for/hasheq ([(id depth) (in-hash (pattern-bound-vars pat (add1 depth)))])
       (values id (hash-ref env^ id (cons depth '()))))]
    [(list (cons car-pat cdr-pat)
           (cons car-expr cdr-expr))
     (hash-union (pattern-match car-pat car-expr depth)
                 (pattern-match cdr-pat cdr-expr depth)
                 #:combine/key (lambda (id _ __) (error 'declare-syntax "duplicate pattern variable ~a" id)))]
    [_ (error 'pattern-match "pattern didn't match")]))

; (Listof Env) -> Env
; combines the environments of an ellipsis sub-pattern's matches
(define (combine-envs envs)
  (define envs^
    (for/list ([env envs])
      (hash-map/copy env
                     (lambda (k v)
                       (match v
                         [(cons depth expr)
                          (values k (cons depth (list expr)))])))))
  (apply hash-union
         (hasheq)
         envs^
         #:combine (lambda (info1 info2) (cons (car info1) (append (cdr info1) (cdr info2))))))

; Pat -> (Listof Symbol)
(define (pattern-bound-vars pat depth)
  (match pat
    [(? identifier? id)
     (hasheq (stx-e id) depth)]
    ['()
     (hasheq)]
    [(list pat (stx '... _))
     (pattern-bound-vars pat (add1 depth))]
    [(cons car-pat cdr-pat)
     (hash-union (pattern-bound-vars car-pat depth)
                 (pattern-bound-vars cdr-pat depth))]
    [_ (error 'pattern-bound-vars "invalid pattern: ~a" pat)]))

; Template Env -> Expr
(define (template-expand tmp env)
  (match tmp
    [(? identifier? id)
     (define info (hash-ref env (stx-e id) #f))
     (match info
       ; unbound identifier in template expands to itself
       [#f id]
       [(cons depth expr)
        (unless (zero? depth)
          (error 'declare-syntax "missing ellipsis with pattern variable in template: ~a" id))
        expr])]
    ['() '()]
    [(list* tmp (stx '... _) cdr-tmp)
     (foldr cons
            (template-expand cdr-tmp env)
            (template-expand/ellipsis tmp env))]
    [(cons car-tmp cdr-tmp)
     (cons (template-expand car-tmp env)
           (template-expand cdr-tmp env))]))

; Template Env -> (Listof SExpr)
; expand an ellipsis sub-template for each expr in the env
(define (template-expand/ellipsis tmp env)
  (define fvs (template-free-variables tmp))
  (define filtered-env
    (for/hasheq ([(id v) (in-hash env)]
                 #:when (member id fvs))
      (values id v)))
  (define envs (env-split filtered-env))
  (for/list ([env envs])
    (template-expand tmp env)))

; Template -> (Listof Symbol)
(define (template-free-variables tmp)
  (match tmp
    [(? identifier? id) (list (stx-e id))]
    ['() '()]
    [(or (list* tmp (stx '... _) cdr-tmp)
         (cons tmp cdr-tmp))
     (append (template-free-variables tmp)
             (template-free-variables cdr-tmp))]))

; Env -> (Listof Env)
; Split an environment containing deep variables into an environment per match
(define (env-split env)
  (define repetition-length (env-repetition-length env))
  (for/list ([i (in-range repetition-length)])
    (for/hasheq ([(id info) (in-hash env)])
      (match info
        [(cons 0 _) (values id info)]
        [(cons n exprs)
         (values id (cons (sub1 n) (list-ref exprs i)))]))))

; Env -> Natural
; How many times does the (ellipsis-template-filitered) environment repeat?
; Should be the same for all deep vars. Error if not.
(define (env-repetition-length env)
  (define repetition-length #f)
  (for ([(id info) (in-hash env)])
    (match-define (cons depth exprs) info)
    (unless (zero? depth)
      (cond
        [repetition-length
         (unless (= repetition-length (length exprs))
           (error 'declare-syntax "incompatible ellipsis match counts for template"))]
        [else (set! repetition-length (length exprs))])))
  (unless repetition-length
    (error 'declare-syntax "too many ellipses in template"))
  repetition-length)

; end syntax-rules

; compile expanded stx to racket datum
(define (compile s)
  (cond
    [(identifier? s) (resolve s)]
    [else
     (case (and (identifier? (first s)) (resolve (first s)))
       [(lambda)
        (match-define `(,lambda-id (,id) ,body) s)
        `(lambda (,(resolve id)) ,(compile body))]
       [(quote)
        (match-define `(,quote-id ,datum) s)
        `(quote ,(stx->datum datum))]
       [(quote-syntax)
        (match-define `(,quote-syntax-id ,datum) s)
        `(quote ,datum)]
       [else
        ; function call
        (map compile s)])]))

(define namespace (make-base-namespace))
(eval '(require racket/list) namespace)
(namespace-set-variable-value! 'datum->syntax
                               datum->stx
                               #t namespace)
(namespace-set-variable-value! 'syntax->datum
                               stx->datum
                               #t namespace)
(namespace-set-variable-value! 'syntax-e
                               stx-e
                               #t namespace)
; datum -> any
(define (eval-compiled s) (eval s namespace))


(define (eval-top datum)
  (eval-compiled (compile (expand-datum datum))))

(module+ test
  (define racket-namespace (make-base-namespace))
  (eval '(require racket/list) racket-namespace)
  (define (eval-racket datum) (eval datum racket-namespace))
  (define-syntax-rule (teval datum) (check-equal? (eval-top 'datum) (eval-racket 'datum)))
  (teval ((lambda (x) x) 'x))
  (teval (let-syntax ([m (syntax-rules () [(m) 'foo])]) (m)))
  (teval (let-syntax ([let (syntax-rules () [(let ([x e]) body) ((lambda (x) body) e)])])
           (let ([x 'foo])
             x)))
  (teval (let-syntax ([let (syntax-rules () [(let ([x e]) body) ((lambda (x) body) e)])])
           (let-syntax ([let* (syntax-rules ()
                                [(let* () e) e]
                                [(let* ([x e] pair ...) body)
                                 (let ([x e])
                                   (let* (pair ...)
                                     body))])])
             (let* ([x 'foo]
                    [y x])
               y))))
  ; name capture with or macro
  (teval (let-syntax ([let (syntax-rules () [(let ([x e]) body) ((lambda (x) body) e)])])
           ; we don't have if in our language, so stupid-or always returns b
           ; this is just to test hygiene anyway
           (let-syntax ([stupid-or (syntax-rules () [(stupid-or a b) (let ([x a]) b)])])
             (let ([x 'foo])
               (stupid-or '#f x)))))
  ; macro-defining macro
  (teval (let-syntax ([let-syntax-rule (syntax-rules () [(let-syntax-rule ([(name pat ...) tmp])
                                                           body)
                                                         (let-syntax ([name (syntax-rules () [(name pat ...) tmp])])
                                                           body)])])
           (let-syntax-rule ([(quote-list e ...) (quote (e ...))])
              (quote-list foo bar))))
  ; refer to local variable in template
  (teval (let-syntax ([let (syntax-rules () [(let ([x e]) body) ((lambda (x) body) e)])])
           (let ([x 'good])
             (let-syntax ([give-x (syntax-rules () [(give-x) x])])
               (let ([x 'bad])
                 (give-x)))))))
