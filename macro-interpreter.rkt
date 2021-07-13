#lang racket

(define-namespace-anchor anc)
(define ns (namespace-anchor->namespace anc))

(require (only-in racket/base (eval racket-eval)))

(define (lookup-env env x)
  (let ((v (assoc x env))) (if v (cdr v) (error (string-append "unbound: " (symbol->string x))))))

(define empty-env '())

(define (cons-env x e env) (cons (cons x e) env))

(define (prepend-env xs es env) (foldr cons-env env xs es))

(define builtins '(* + equal?))

(define (lookup-builtin x) (let ((v (member x builtins))) (if v (racket-eval (car v) ns) v))) 


(define (eval env e)
  (let ((recur (lambda (arg) (eval env arg))))
    (match e
      [x #:when (symbol? x) (or (lookup-builtin x) (lookup-env env x))] ; var ref
      [`(,(or 'lambda 'λ) (,argnames ...) ,body) e] ; lambda (need this case to prevent it being recognized as application)
      [`(let ((,xs ,es) ...) ,body) (eval (prepend-env xs es env) body)] ; let binding(s)
      [`(if ,cnd ,thn ,els) (if (recur cnd) (recur thn) (recur els))] ; if
      [`(quote ,datum) datum] ; quote
      [`(quasiquote ,datum) (eval-quasi env 1 datum)] ; quasi (escapable) quote
      [(list f args ...) (app env (recur f) (map recur args))] ; application
      [_ e] ; literal
      )))

(define (app env f args)
  (match f
    [`(,(or 'lambda 'λ) (,argnames ...) ,body) (eval (prepend-env argnames args env) body)] ; lambda
    [_ (apply f args)] ; built-in
    ))

;; evaluate a quasi-quoted expression (special case is unquote). level indicates the number of enclosing quotes. At 1, an unquote will escape
(define (eval-quasi env level e)
  (let* ((recurf (lambda (f) (lambda (e) (eval-quasi env (f level) e))))
         (recur (recurf values))
         (recur+1 (recurf add1))
         (recur-1 (recurf sub1)))
    (match e
      [(list 'unquote datum) (if (= level 1) (eval env datum) (list 'unquote (recur-1 datum)))]
      [`(quasiquote ,datum) (list 'quasiquote (recur+1 datum))]
      [`(,es ...) (map recur es)] ; no unquote-splicing yet
      [_ e]
      )))

(check-equal? (eval-quasi (cons-env 'x 2 empty-env) 1 ',x) 2)

(require rackunit)

(check-equal? (eval empty-env '(lambda (x) x)) '(lambda (x) x))
(check-equal? (eval empty-env '((lambda (x) x) 1)) 1)

(define-syntax-rule (thunk e) (lambda () e))
(check-exn (lambda (e) (string=? (exn-message e) "unbound: x")) (thunk (eval empty-env 'x)))

(check-equal? (eval empty-env '(let ((x 2)) x)) 2)
(check-equal? (eval empty-env '(* 2 3)) 6)
(check-equal? (eval empty-env '(let ((x 2) (y 3)) (* x y 5))) 30)
(check-equal? (eval empty-env '(if #t 1 2)) 1)
(check-equal? (eval empty-env '(if #f 1 2)) 2)
(check-equal? (eval empty-env '(quote x)) 'x)
(check-equal? (eval empty-env `(if #t 1 2)) (racket-eval `(if #t 1 2) ns))
(define-syntax-rule (teval e) (check-equal? (eval empty-env e) (racket-eval e ns)))

(teval '(quote x))
(teval '(quote (+ 1 2)))
(teval '(quote (quote x)))
(teval ''x)
(teval '`x)
(teval '(let ((x 2)) `,x))
(teval '(let ((x 2)) `(x ,x)))
(teval '(let ((x 2)) `',x))
(teval '(let ((x 2)) ``,x))
(teval '`(lambda (x) x))
(teval '(let ((x 2)) ``,,x))
(teval '(let ((x 2)) ``,(,x)))
(teval '(let ((x 2)) `(`,(,x))))
(teval '`(1 `,(+ 1 ,(+ 2 3)) 4)) ; stolen from racket quasiquoting docs
(teval '`(,1 2 3)) ; stolen from racket docs