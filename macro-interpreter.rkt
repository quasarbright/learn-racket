#lang racket

(define-namespace-anchor anc)
(define ns (namespace-anchor->namespace anc))

(require (only-in racket/base (eval racket-eval)))

(define (lookup-env env x)
  (let ((v (assoc x env))) (if v (cdr v) (error (string-append "unbound: " (symbol->string x))))))

(define empty-env '())

(define (cons-env x e env) (cons (cons x e) env))

(define (prepend-env xs es env) (foldr cons-env env xs es))

(define builtins `((* ,*) (+ ,+) (equal? ,equal?) (list ,list) (cons ,cons)))

(define (lookup-builtin x) (let ((v (assoc x builtins))) (if v (second v) v)))

(require racket/struct)
(struct closure (argnames body env) #:inspector #f)

(define (eval env e)
  (let ((recur (lambda (arg) (eval env arg))))
    (match e
      [x #:when (symbol? x) (or (lookup-builtin x) (lookup-env env x))] ; var ref
      [`(eval ,datum-expr) (recur (recur datum-expr))] ; evaluate the value of datum-expr as a datum
      [`(,(or 'lambda 'λ) (,argnames ...) ,body) (closure argnames body env)] ; lambda (need this case to prevent it being recognized as application)
      [`(let ((,xs ,es) ...) ,body) (eval (prepend-env xs (map recur es) env) body)] ; let binding(s) TODO no dups
      [`(if ,cnd ,thn ,els) (if (recur cnd) (recur thn) (recur els))] ; if
      [`(quote ,datum) datum] ; quote
      [`(quasiquote ,datum) (eval-quasi env 1 datum)] ; quasi quote (escapable with unquote)
      [`(begin ,es ..1) (last (map recur es))] ; begin (evals all exprs, last one gets returned)
      [`(letmacro (,name ,f) ,e) (recur (expand-macro 0 name (recur f) e))] ; macro definition. immediately expands in body
      [(list 'unquote _) (error "unquote used outside of a quasi quote")]
      [(list f args ...) (app (recur f) (map recur args))] ; application
      [_ e] ; literal
      )))

(define (app f args)
  (match f
    [(closure argnames body env) (eval (prepend-env argnames args env) body)] ; lambda
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

#;(define (run defs)
    ...)

(define (run-def env def)
  (match def
    [`(define ,x ,e) (prepend-env (list x) (list (eval env e)) env)]
    [`(define (,f ,xs ...) ,e) (run-def env `(define ,f (lambda ,xs ,e)))] ; no recursion :( need a layer of indirection or cyclic data
    [e (eval env e)]
    ))

;; expand (name ...) using the stx -> stx function f in the body e
; level is number of enclosing quasi quotes. only expands at 0
(define (expand-macro level name f e)
  (define ((recurf fl) e) (expand-macro (fl level) name f e))
  (define recur (recurf values))
  (define recur+1 (recurf add1))
  (define recur-1 (recurf sub1))
  (match e
    [`(,hd ,args ...) #:when (and (= level 0) (symbol? hd) (symbol=? name hd))
                      (app f args)]
    [`(,(or 'lambda 'λ) (,xs ...) ,body) (if (member name xs) e `(lambda ,xs ,(recur body)))] ; name capture
    [`(let ((,xs ,es) ...) body) (if (member name xs) e `(let ,(map (lambda (x e) `(,x ,(recur e))) xs es) (recur body)))] ; if any binding shadows, no macro expansion
    [`(quote ,e) `(quote ,e)]
    [`(quasiquote ,e) (list 'quasiquote (recur+1 e))]
    [(list 'unquote e) (list 'unquote (recur-1 e))]
    [`(,es ...) (map recur es)]
    [_ e]
    ))
         
(require rackunit)

(define (eval-empty e) (eval empty-env e))

(check-equal? (eval-quasi (cons-env 'x 2 empty-env) 1 ',x) 2)

(check-equal? (eval-empty '(lambda (x) x)) (closure '(x) 'x empty-env))
(check-equal? (eval-empty '((lambda (x) x) 1)) 1)

(define-syntax-rule (thunk e) (lambda () e))
(check-exn (lambda (e) (string=? (exn-message e) "unbound: x")) (thunk (eval-empty 'x)))

(check-equal? (eval-empty '(let ((x 2)) x)) 2)
(check-equal? (eval-empty '(* 2 3)) 6)
(check-equal? (eval-empty '(let ((x 2) (y 3)) (* x y 5))) 30)
(check-equal? (eval-empty '(if #t 1 2)) 1)
(check-equal? (eval-empty '(if #f 1 2)) 2)
(check-equal? (eval-empty '(quote x)) 'x)
(check-equal? (eval-empty `(if #t 1 2)) (racket-eval `(if #t 1 2) ns))
(define-syntax-rule (teval e) (check-equal? (eval-empty e) (racket-eval e ns)))

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
(teval '2)
(teval `2)
(check-exn (lambda (val) (string=? (exn-message val) "unquote used outside of a quasi quote")) (thunk (eval-empty '(unquote x))))
(check-equal? (eval-empty '(eval 2)) 2)
(check-equal? (eval-empty '(eval 2)) 2)
(check-equal? (eval-empty '(eval '(+ 2 2))) 4)
(check-equal? (eval-empty '(let ((x 2)) (eval 'x))) 2)
(check-equal? (eval-empty '(let ((x 2) (y 3)) (+ 1 (eval '(+ x y))))) 6)
(check-equal? (eval-empty '(let ((plus1 (lambda (stx) `(+ 1 ,stx)))) (eval (plus1 2)))) 3)
(check-equal? (eval-empty '(let ((x 2) (plus1 (lambda (stx) `(+ 1 ,stx)))) (eval (plus1 x)))) 3)
(check-equal? (eval-empty '(let ((plus1 (lambda (stx) `(+ 1 ,stx))) (x 2)) (eval (plus1 x)))) 3)
(check-equal? (eval-empty '(let ((plus1 (lambda (stx) `(+ 1 ,stx x))) (x 2)) (eval (plus1 x)))) 5) ; the macro outputs a reference to x. dynamic scope
(teval '(begin 1 2 3))
(teval '(let ((x 1)) (let ((f (lambda (y) (+ x y))) (x 2)) (f 3)))) ; lexical scope
(check-equal? (eval-empty '(letmacro (plus1 (lambda (stx) `(+ 1 ,stx))) (plus1 2))) 3)
(check-equal? (eval-empty '(letmacro (describe (lambda (stx) `(list ',stx ,stx))) (describe (+ 1 1)))) '((+ 1 1) 2))
(check-equal? (eval-empty '(letmacro (describe (lambda (stx) `(list ',stx ,stx))) (list 222 (describe (+ 1 1))))) '(222 ((+ 1 1) 2)))
(check-equal? (eval-empty '(letmacro (describe (lambda (stx) `(list ',stx ,stx))) (let ((x 1)) (describe x)))) '(x 1))
(check-equal? (eval-empty '(letmacro (one (lambda () 1)) (one))) 1)
(check-equal? (eval-empty '(letmacro (one (lambda () 1)) `,(one))) 1) ; expands escaped syntax in quasi quote
(check-equal? (eval-empty '(letmacro (one (lambda () 1)) '(one))) '(one)) ; doesn't expand in quote
(check-equal? (eval-empty '(letmacro (one (lambda () 1)) `(one))) '(one)) ; only expands escaped quasi quote
(check-equal? (eval-empty '(letmacro (one (lambda () 1)) ```,,,(one))) '``,,1) ; macro expand handles deep quasi quotes