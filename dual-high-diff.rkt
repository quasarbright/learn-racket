#lang racket

#|
higher order differentiation via a generalization of dual numbers.

!!!!!NEVER MIND! This actually doesn't work!!!!!!!!!

Dual numbers:
E^2 = 0, E != 0
f(a+bE) = f(a) + bf'(a)E

useful for first order derivatives, but not second order.
In general,
f(a+bD) = sum_n f^(n)(a)b^n/n!
Taylor series.
Since E^2 = 0, you only get the first two terms, but if
D^(n+1) = 0, you get nth derivatives. You just have to subtract out lower order ones

But for composite functions, you have to be able to take in high order polynomials.
How can you extend a function to high order polynomials? Should do the same
taylor series thing that they did for dual numbers
|#

(module+ test (require rackunit))

;; Data definitions

; A Polynomial is a (stream-of Number)
; Must be an infinite stream (can have trailing zeroes)
; Representing coefficients of a polynomial
; where the i-index element is the coefficient of x^i

;; polynomial operations

; zero polynomial
(define zero (stream-cons 0 zero))

; Number ... -> Polynomial
(define (polynomial . coefficients)
  (stream-append (for/stream ([c coefficients]) c) zero))

; Polynomial Natural -> Number
; Get the coefficient of x^i
(define (get-coefficient p i)
  (stream-ref p i))

; Polynomial Natural -> (list-of Number)
; Gets the first n coefficients.
(define (get-coefficients p n)
  (stream->list (stream-take p n)))

; Polynomial Polynomial -> Polynomial
(define (+/p p1 p2)
  (for/stream ([c1 p1] [c2 p2])
    (+ c1 c2)))

; Polynomial Polynomial -> Polynomial
(define (*/p p1 p2)
  ; the nth coefficient takes O(n) time to compute
  (for/stream ([i (in-naturals)])
    (for/sum ([j (in-range (add1 i))])
      (* (get-coefficient p1 j) (get-coefficient p2 (- i j))))))

(module+ test
  (check-equal?
   ; (2 + 3x)(5 + 7x)
   ; 10 + 14x + 15x + 21x^2
   (get-coefficients (*/p (polynomial 2 3) (polynomial 5 7))
                     5)
   (list 10 29 21 0 0)))

; Polynomial Natural -> Polynomial
(define (expt/p p n)
  (for/fold ([product (polynomial 1)])
            ([_ (in-range n)])
    (*/p p product)))

;; differentiation

; (Polynomial -> Polynomial) Number -> Number
#;(define (derivative f x)
  (f (polynomial x 1)))
