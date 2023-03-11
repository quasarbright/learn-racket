#lang racket/base

#|
an interpreter for a language with:
recursive definition contexts
(non-hygienic) macros
quasiquoting
lexical scope
|#

(require racket/list
         racket/function
         racket/match
         (only-in racket/base (eval racket-eval)))

(define-namespace-anchor anc)
(define ns (namespace-anchor->namespace anc))

; an env is a (listof (hash-of varname value))
; each frame maps varname to value
; first frame is most recent and has shadowing priority

; a varname is a symbol

; a value is one of
; atomic data
; (value ... -> value)
; closure
; void

; a closure is a
(struct closure [argnames body env is-macro?] #:transparent)
; argnames: (listof varname)
; body: (listof expr)
; env: env
; is-macro: boolean

(define (empty-env) '())

; env varname value -> void
; declare and initialize variable in this frame. must not already be bound in this frame
(define (env-bind! env k v)
  (define frame (first env))
  (if (hash-has-key? frame k)
      (error 'env-bind! "name ~v already bound" k)
      (hash-set! frame k v)))

; env [(hash-of varname value)] -> env
; add an empty frame to the env
(define (env-add-frame env [frame (make-hasheq)]) (cons frame env))

; env varname -> value
; look up value of var k
(define (env-lookup env k)
  (if (null? env)
      (error (format "unbound variable ~v" k))
      (hash-ref (first env) k (lambda () (env-lookup (rest env) k)))))

; env varname value -> value
; set the variable's value. It must already be bound
(define (env-set! env k v)
  (if (null? env)
      (error (format "set!: unbound variable ~v" k))
      (if (hash-has-key? (first env) k)
          (hash-set! (first env) k v)
          (env-set! (rest env) k v))))

; expr env -> value
(define (eval expr env)
  (define (recur expr) (eval expr env))
  (match expr
    [(? (disjoin number? string? boolean? null?)) expr]
    [(? symbol? var) (env-lookup env var)]
    [(cons (or 'define 'define-syntax) _)
     (error "definitions are not allowed in an expression context")]
    [(list 'eval expr) (recur (recur expr))]
    [`(if ,cnd ,thn ,els)
     (if (recur cnd)
         (recur thn)
         (recur els))]
    [`(quote ,datum) datum]
    [`(quasiquote ,datum) (eval-quasi datum env 1)]
    [`(begin . ,exprs)
     (if (null? exprs)
         (void)
         (for/last ([expr exprs])
           (recur expr)))]
    [(list 'let (list (list vars exprs) ...) body ...)
     (let ([env (env-add-frame env (make-hasheq (map cons vars (map recur exprs))))])
       (eval-body body env))]
    [`(set! ,var ,expr)
     (define val (recur expr))
     (env-set! env var val)
     (void)]
    [(list 'lambda (list vars ...) exprs ...)
     (closure vars exprs env #f)]
    [(cons func args)
     (define func^ (recur func))
     (match func^
       [(closure argnames body func-env is-macro?)
        (if is-macro?
            (recur (apply-function argnames
                                   (list expr)
                                   func-env
                                   body))
            (apply-function argnames
                            (map recur args)
                            func-env
                            body))]
       [(? procedure?)
        ; built-in
        (define args^ (map recur args))
        (apply func^ args^)]
       [_ (error (format "application expected procedure but received ~v" func^))])]))

; (listof varname) (listof val) env (listof expr) -> value
(define (apply-function argnames args env body)
  (unless (= (length argnames) (length args))
    (error "arity error: expected ~v but received ~v"
           (length argnames)
           (length args)))
  (define env^
    (env-add-frame env
                   (make-hasheq (map cons argnames args))))
  (eval-body body env^))

; (listof expr) env -> value
; evaluates body in a recursive definition context.
(define (eval-body body env)
  (let ([body (splice-begins body)])
    (if (null? body)
        (void)
        (let ([env (env-add-frame env)])
          (for/last ([expr body])
            (eval-body-expr expr env))))))

(define (splice-begins exprs)
  (if (null? exprs)
      exprs
      (match (first exprs)
        [(cons 'begin sub-exprs)
         (append (splice-begins sub-exprs) (splice-begins (rest exprs)))]
        [expr (cons expr (splice-begins (rest exprs)))])))

; like eval, but allow definitions
(define (eval-body-expr expr env)
  (match expr
    [(list 'define var body ...)
     (env-bind! env var (eval-body body env))
     (void)]
    [(list 'define-syntax var body ...)
     (define transformer (eval-body body env))
     (define transformer^
       (if (closure? transformer)
           (struct-copy closure transformer [is-macro? #t])
           transformer))
     (env-bind! env var transformer^)
     (void)]
    [_ (eval expr env)]))

; level is number of enclosing quasiquotes - the number of enclosung unquotes or unquote-splicings
(define (eval-quasi expr env level)
  (let* ((recurf (lambda (f) (lambda (e) (eval-quasi e env (f level)))))
         (recur (recurf values))
         (recur+1 (recurf add1))
         (recur-1 (recurf sub1)))
    (match expr
      ; TODO unquote-splicing
      [(list 'unquote datum)
       (if (= level 1)
           (eval datum env)
           (list 'unquote (recur-1 datum)))]
      [(cons 'unquote-splicing datum)
       (if (= level 1)
           (error 'quasiquote "invalid context for unquote-splicing")
           (list 'unquote-splicing (recur-1 datum)))]
      [`(quasiquote ,datum) (list 'quasiquote (recur+1 datum))]
      [(cons car-datum cdr-datum)
       (match car-datum
         [(list 'unquote-splicing datum)
          (if (= level 1)
              (append (eval datum env)
                      (recur cdr-datum))
              (cons (list 'unquote-splicing (recur-1 datum))
                    (recur cdr-datum)))]
         [_ (cons (recur car-datum)
                  (recur cdr-datum))])]
      [_ expr])))

(define-syntax-rule
  (make-builtins name ...)
  (list (make-hasheq)
        (make-hasheq (list (cons 'name name) ...))))

; TODO some built-in macros. easiest way might be a prelude.
(define initial-env
  (make-builtins + * equal? list cons car cdr null? cons? gensym first second third rest list-ref length < <= > >=))

(define (eval-top expr)
  (eval expr initial-env))

(module+ test
  (require rackunit)
  (define-syntax-rule (teval e) (check-equal? (eval-top 'e) (racket-eval 'e ns)))
  (teval 1)
  (teval (if 1 2 3))
  (teval (if #f 2 3))
  (teval 'x)
  (teval (begin 1 2))
  (teval (let ([x 1]) x))
  (teval (let ([x 1]) (set! x 2) x))
  (teval (list 1))
  (teval ((lambda (x) x) 1))
  (teval (+ 1 2))
  (teval ((lambda (x) (+ x 1)) 2))
  ; simple definition
  (teval (let () (define x 1) x))
  (teval (let ()
           (begin (begin (define x 1)))
           (begin (define y 2))
           (list x y)))
  ; simple macro
  (check-equal? (eval-top '(let () (define-syntax m (lambda (expr) 2)) (m)))
                2)
  (check-equal? (eval-top '(let () (define-syntax m (lambda (expr) (list 'quote expr))) (m 2)))
                '(m 2))
  ; macro in terms of macro
  (check-equal? (eval-top '(let ()
                             (define-syntax m1 (lambda (expr)
                                                 (list 'm2 (list (car (cdr expr))
                                                                 (car (cdr expr))))))
                             (define-syntax m2 (lambda (expr) (list 'quote (car (cdr expr)))))
                             (m1 2)))
                '(2 2))
  ; closures
  (teval (let ()
           (define x 1)
           (define f (lambda () (set! x (+ 1 x)) x))
           (let ([x 3])
             (list (f) (f)))))
  ; recursion
  (teval (let ()
           (define fac
             (lambda (n)
               (if (equal? 0 n)
                   1
                   (* n (fac (+ -1 n))))))
           (fac 5)))
  ; mutual recursion
  (teval (let ()
           (define even?
             (lambda (n)
               (if (equal? 0 n)
                   #t
                   (odd? (+ -1 n)))))
           (define odd?
             (lambda (n)
               (if (equal? 1 n)
                   #t
                   (even? (+ -1 n)))))
           (even? 10)))
  ; quasiquote
  (teval (let ((x 2)) `,x))
  (teval (let ((x 2)) `(x ,x)))
  (teval (let ((x 2)) `',x))
  (teval (let ((x 2)) ``,x))
  (teval `(lambda (x) x))
  (teval (let ((x 2)) ``,,x))
  (teval (let ((x 2)) ``,(,x)))
  (teval (let ((x 2)) `(`,(,x))))
  (teval `(1 `,(+ 1 ,(+ 2 3)) 4)) ; stolen from racket quasiquoting docs
  (teval `(,1 2 3)) ; stolen from racket docs
  ; unquote-splicing
  (teval `(,@(list 1 2) 3))
  (teval `(`,@(list 1 2) 3))
  (teval `(`,@(,@(list 1 2)) 3))
  (teval `(1 ```,,@,,@(list (+ 1 2)) 4)) ; stolen from racket docs
  ; swap macro
  (check-equal?
   (eval-top '(let ()
                (define-syntax swap!
                  (lambda (stx)
                    (define x (second stx))
                    (define y (third stx))
                    (define tmp (gensym))
                    `(let ([,tmp ,x])
                       (set! ,x ,y)
                       (set! ,y ,tmp))))
                (define x 1)
                (define y 2)
                (swap! x y)
                (list x y)))
   '(2 1))
  ; TODO match macro
  )
