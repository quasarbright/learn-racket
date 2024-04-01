#lang racket

;; compiling to anf with continuations

(require "algebraic-effect-2.rkt")

(define-algebraic-effect anf
  ; create a temp var and bind expr to it by wrapping the rest of the computation in a let.
  ; returns the variable.
  [(bind! expr k)
   (match expr
     [(or (? symbol?) (? number?)) expr]
     [_
      (define x (gensym 'anf))
      `(let ([,x ,expr]) ,(k x))])]
  ; like bind!, but you specify the variable name. lifts a binding into the surrounding nesting, returns void.
  [(lift! x expr k) `(let ([,x ,expr]) ,(k (void)))])

(define (to-anf expr)
  (anf (to-anf/help expr)))

(define (to-anf/help expr)
  (match expr
    [(or (? symbol?) (? number?)) expr]
    [`(,(and op (or '+ '*)) ,a-expr ,b-expr)
     `(,op ,(to-immediate a-expr) ,(to-immediate b-expr))]
    [`(let ([,x ,rhs-expr]) ,body-expr)
     (define rhs-expr^ (to-anf/help rhs-expr))
     (lift! x rhs-expr^)
     (to-anf/help body-expr)]))

(define (to-immediate expr)
  (match expr
    [(or (? symbol?) (? number?)) expr]
    [_ (bind! (to-anf/help expr))]))

(to-anf '(+ (* 2 3) (* 4 5)))

(define expr '(+ (let ([a (+ (* 2 3) (* 4 5))]) (+ (* a 6) 7)) (+ 8 9)))
expr
(to-anf expr)
(eval expr)
(eval (to-anf expr))
