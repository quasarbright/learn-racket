#lang racket

;; A lambda calculus interpreter that operates on expanded syntax,
;; using syntax-spec
;;
;; Benefits:
;; - grammar and binding checking
;; - hygienic macros, syntactic sugar
;; - interpreter/static checks only have to worry about core forms
;; - static checks have access to binding information (this example language has no static checks)
;; - easy to report runtime error source location since we evaluate syntax
;; Drawbacks:
;; - not sure if substitution would work bc of scopes on expanded syntax. might be fine
;; - interpreter helpers need expanded syntax, which might make it hard to unit test them

(module+ test (require rackunit))
(require syntax-spec-v3
         syntax/parse
         (for-syntax syntax/parse
                     racket/syntax-srcloc)
         racket/syntax-srcloc
         (for-template syntax-spec-v3)
         syntax/id-table
         syntax/macro-testing)

(syntax-spec
  (binding-class lc-var #:binding-space lc)
  (extension-class lc-macro #:binding-space lc)
  (nonterminal lc-expr
    #:binding-space lc
    #:allow-extension lc-macro
    n:number
    (+ e1:lc-expr e2:lc-expr)
    x:lc-var
    (lambda (x:lc-var) e:lc-expr)
    #:binding (scope (bind x) e)
    (~> (e1 e2)
        ;; this is necessary to preserve source location, properties, etc.
        (datum->syntax this-syntax (syntax-e #'(#%app e1 e2)) this-syntax this-syntax this-syntax))
    (#%app e1:lc-expr e2:lc-expr))

  (host-interface/expression
    (lc-expand e:lc-expr)
    #'#'e))

(define-dsl-syntax let lc-macro
  (syntax-rules ()
    [(let ([x rhs]) body)
     ((lambda (x) body) rhs)]))

(define-syntax-rule (lc e)
  (lc-eval (lc-expand e) empty-env))

;;; runtime

;; An Env is a (ImmutableBoundIdTable Value)
(define empty-env (make-immutable-bound-id-table))
;; Env Identifier -> Value
(define (env-lookup env x)
  (bound-id-table-ref env x))
;; Env Identifier Value -> Void
(define (env-extend env x v)
  (bound-id-table-set env x v))
;; TODO ask michael if this makes any sense

;; A Value is one of
;; a Number
;; a Value -> Value

;; Syntax Env -> Value
(define (lc-eval stx env)
  (syntax-parse stx
    #:datum-literals (+ lambda #%app)
    [n:number
     (syntax->datum #'n)]
    [(+ e1 e2)
     (define v1 (lc-eval #'e1 env))
     (unless (number? v1)
       (lc-error this-syntax "+ expects number"))
     (define v2 (lc-eval #'e2 env))
     (unless (number? v2)
       (lc-error this-syntax "+ expects number"))
     (+ v1 v2)]
    [x:id
     ;; guaranteed bound
     (env-lookup env #'x)]
    [(lambda (x:id) e:expr)
     (lambda (v) (lc-eval #'e (env-extend env #'x v)))]
    [(#%app e1 e2)
     (match (lc-eval #'e1 env)
       [(? procedure? f)
        (f (lc-eval #'e2 env))]
       [_
        (lc-error this-syntax "applied non-function")])]))

;; Syntax String -> Void
;; raise (runtime) error with source location reported
(define (lc-error stx msg)
  (define loc (syntax-srcloc stx))
  (if loc
      (raise-user-error (format "~a: ~a" (srcloc->string loc) msg))
      (raise-user-error 'lc msg)))

(module+ test
  (define-syntax-rule (teval e) (check-equal? (lc e) e))
  (define-syntax-rule (t-runtime-error msg e)
    (check-exn
     msg
     (lambda ()
       (lc e))))
  (define-syntax-rule (t-expand-error msg e)
    (check-exn
     msg
     (lambda ()
       (convert-compile-time-error (lc e)))))
  (teval 1)
  (teval (+ 1 1))
  (teval ((lambda (x) x) 1))
  (teval (let ([x 1]) (+ x x)))
  (test-case "hygiene"
    ;; basic shadow
    (teval (let ([x 1])
             (let ([x 2])
               x)))
    ;; macro "shadows", should not actually shadow
    (define-dsl-syntax m lc-macro
      (syntax-rules ()
        [(m e)
         (let ([x 2]) e)]))
    (check-equal? (lc (let ([x 1]) (m x)))
                  1)
    ;; macro ref to macro binding not shadowable from use site
    (define-dsl-syntax m2 lc-macro
      (syntax-rules ()
        [(m2 ([x rhs]))
         (let ([y 1])
           (let ([x rhs])
             y))]))
    (check-equal? (lc (m2 ([y 2])))
                  1))
  ;; errors
  (t-expand-error
   #rx"not bound"
   x)
  (t-expand-error
   ;; actual decent grammatical error message
   #rx"lambda: unexpected term"
   (lambda (x y) x))
  (t-runtime-error
   ;; source location for runtime error
   #px".*\\.rkt:\\d*:\\d*: applied non-function"
   (1 2)))
