#lang racket

(module+ test (require rackunit))

; an "interpreter" for a tiny language with delimited continuations
; really just a pre-processing step. Invokes racket's `eval` after transforming
; the source program

; expr -> value
(define (eval/cps expr)
  ((eval (cps-transform (desugar expr))) identity))


; translate the program into cps
; invariant:
; cps-ing an expr results in a function that takes in a continuation and
; calls it with the result of evaluating the expr
; core-expr -> cps-expr
(define (cps-transform expr)
  (match expr
    ['call/cc
     ; since f will call k, it needs to have the extra cont argument
     ; even though it will be ignored
     ; k-cc is the continuation for the reference to call/cc
     ; f is the function that receives the current continuation
     ; k is the continuation for the call/cc application (the current continuation)
     ; val is the value to "continue" with
     ; cont is the continuation for the application of k (ignored)
     '(lambda (k-cc)
        (k-cc
         (lambda (f k)
           (f (lambda (val cont) (k val))
              k))))]
    ['void
     ; if they define a variable called void, this will break
     '(lambda (k-void) (k-void (void)))]
    [`(lambda ,args ,body)
     (define k (gensym 'k-lam))
     (define cont (gensym 'cont))
     (define body^ (cps-transform body))
     `(lambda (,k) (,k (lambda (,@args ,cont) (,body^ ,cont))))]
    [`(if ,cnd ,thn ,els)
     (define k (gensym 'k-if))
     (define vcnd (gensym 'vcnd))
     (define cnd^ (cps-transform cnd))
     (define thn^ (cps-transform thn))
     (define els^ (cps-transform els))
     `(lambda (,k)
        (,cnd^
         (lambda (,vcnd)
           (if ,vcnd
               (,thn^ ,k)
               (,els^ ,k)))))]
    [`(,f ,xs ...)
     (define k (gensym 'k-app))
     `(lambda (,k) ,(cps-transform-app (cons f xs) k))]
    [_
     (define k (gensym 'k-const))
     `(lambda (,k) (,k ,expr))]))

; translate function application to cps
; Example:
#;{ (cps-transform-app (list f x y) '() k)
    ->
    (lambda (k)
      (f^
       (λ (vf)
         (x^
          (λ (vx)
            (y^
             (λ (vy)
               (vf vx vy k))))))))}
;; It's like monadic bind, or callbacks
;; (CPS f) gives you a callback which is like
;; "What do you want to do with this?"
;; And you say "I want to do (lambda (vf) ...)"
;; And in the end, you call the function value
;; with all the arguments and the outer k,
;; since functions take in a continuation
; (list-of core-expr) symbol -> cps-expr
(define (cps-transform-app exprs k)
  (define exprs^ (map cps-transform exprs))
  (define vs (map (lambda (_) (gensym 'v)) exprs))
  (foldr (lambda (expr^ v body) `(,expr^ (lambda (,v) ,body)))
         (append vs (list k))
         exprs^
         vs))

; desugar into core language
; expr -> core-expr
(define (desugar expr)
  (match expr
    [`(let ([,x ,rhs] ...) ,@body)
     (desugar `((lambda ,x ,@body) ,@rhs))]
    [`(let/cc ,k ,@body)
     (desugar `(call/cc (lambda (,k) ,@body)))]
    ['(begin) '(void)]
    [`(begin ,expr) (desugar expr)]
    [`(begin ,@exprs)
     (define vs (map (lambda (_) (gensym 'v-begin)) exprs))
     (desugar `((lambda ,vs ,(last vs)) ,@exprs))]
    [`(lambda ,args ,@body) `(lambda ,args ,(desugar `(begin ,@body)))]
    [`(,exprs ...) (map desugar exprs)]
    [_ expr]))

(module+ test
  (define-syntax-rule
    (teval expr)
    (check-equal? (eval/cps 'expr) (eval 'expr)))
  (teval (let ([x 1]) x))
  (teval (if #t 1 2))
  (teval (if #f 1 2))
  (teval ((lambda (x) (if x 1 2)) #t))
  (teval (call/cc (lambda (k) 2)))
  (teval (call/cc (lambda (k) (k 2))))
  (teval (call/cc (lambda (k) (let ([x 1] [y (k 3)]) x))))
  (teval (let ([x 3] [k (let/cc k k)])
           (if k (k #f) x))))
