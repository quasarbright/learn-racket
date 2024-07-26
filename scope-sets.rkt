#lang racket

(module+ test (require rackunit))

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
    [(list? s) (map (stx->datum s))]
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
  (define rhs-val (eval-for-syntax-binding rhs))
  ; map binding to its value
  (define body-env (env-extend env binding rhs-val))
  ; expand body
  (expand (add-scope body sc) body-env))

(define (eval-for-syntax-binding rhs)
  ; TODO syntax-rules
  (eval-compiled (compile (expand rhs empty-env))))

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
  (check-equal? (eval-top '(let-syntax ([let (lambda (s) (list (list (quote-syntax lambda) (list (first (first (second s)))) (second (rest s)))
                                                               (second (first (second s)))))])
                             (let ([x 'foo])
                               x)))
                'foo))
