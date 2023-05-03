#lang racket

; an interpreter for a tiny language with delimited continuations

; translate the program into cps
; invariant:
; cps-ing an expr results in a function that takes in a continuation and
; calls it with the result of evaluating the expr
(define (cps-transform expr)
  (match expr
    ['call/cc call/cc-expr]
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
; (list-of expr) symbol -> expr
(define (cps-transform-app exprs k)
  (define exprs^ (map cps-transform exprs))
  (define vs (map (lambda (_) (gensym 'v)) exprs))
  (foldr (lambda (expr^ v body) `(,expr^ (lambda (,v) ,body)))
         (append vs (list k))
         exprs^
         vs))

(define call/cc-expr
  ; since f will call k, it needs to have the extra cont argument
  ; even though it will be ignored
  '(lambda (f k) (f (lambda (val cont) (k val)) k)))

(define (desugar expr)
  (match expr
    [`(let ([,x ,rhs] ...) ,body)
     `((lambda ,x ,(desugar body)) ,@(map desugar rhs))]
    [_ expr]))

(define (eval/cps expr)
  ((eval (cps-transform (desugar expr))) identity))

(eval/cps '(let ([x 1]) x))
