#lang racket

(module+ test (require rackunit))

; A DualNumber is a
(struct dual [a b] #:transparent)
; where a and b are numbers.
; Represents a + b * epsilon where
; epsilon ^ 2 = 0 and epsilon != 0

(define epsilon (dual 0 1))

(define-syntax-rule (define/dual (name arg ...) body ...)
  (define (name . args)
    (define args^ (map ensure-dual args))
    (define f (lambda (arg ...) body ...))
    (ensure-dual (apply f args^))))

; (Or Number DualNumber) -> DualNumber
(define (ensure-dual x)
  (if (number? x)
      (dual x 0)
      x))

(define/dual (+/dual x y)
  (match* (x y)
    [((dual a b) (dual c d))
     (dual (+ a c) (+ b d))]))

(define/dual (*/dual x y)
  (match* (x y)
    [((dual a b) (dual c d))
     (dual (* a c) (+ (* a d) (* b c)))]))

; (Or Number DualNumber) Natural -> DualNumber
(define (expt/dual x n)
  (if (zero? n)
      (dual 1 0)
      (*/dual x (expt/dual x (sub1 n)))))

(module+ test
  (check-equal? (*/dual epsilon epsilon) (dual 0 0))
  (check-equal? (*/dual 3 2) (dual 6 0))
  (check-equal? (expt/dual 3 2) (dual 9 0)))

; (DualNumber -> DualNumber) Number -> Number
(define (derivative f x)
  (match (f (dual x 1))
    [(dual _ dfdx) dfdx]))

(define/dual (sqr/dual x) (*/dual x x))

(module+ test
  (check-equal? (derivative (lambda (x) (+/dual 1 x)) 2) 1)
  (check-equal? (derivative sqr/dual 3) 6))

; (Or Number DualNumber) Natural -> DualNumber
(define (exp/dual/taylor x [num-terms 10])
  (for/fold ([sum (dual 0 0)])
            ([n (in-range num-terms)])
    (+/dual sum (*/dual (expt/dual x n) (/ (factorial n))))))

; Natural -> Natural
(define (factorial n)
  (if (zero? n) 1 (* n (factorial (sub1 n)))))

; (Or Number DualNumber) -> DualNumber
(define/dual (exp/dual/direct x)
  ; e ^ (a + bE) = e ^ a * e ^ bE = e ^ a + 1 + bE + (bE)^2/2 + (bE)^3/6
  ; = e^a * (1 + bE) = e^a + e^a * bE
  (match x
    [(dual a b)
     (dual (exp a) (* b (exp a)))]))

(define exp/dual exp/dual/direct)

(module+ test
  (check-equal? (derivative exp/dual 4) (exp 4)))

; (Number -> Number) (Number -> Number) -> (DualNumber -> DualNumber)
; Given a function and its derivative, extend it to dual numbers
(define ((lift-differentiable f f^) x)
  (match x
    [(dual a b)
     (dual (f a) (* b (f^ a)))]))

(define sin/dual (lift-differentiable sin cos))

(module+ test
  (check-equal? (derivative sin/dual 4) (cos 4)))

#|
D g(f(x)) = g'(f(x))f'(x) chain rule
f(a + bE) = f(a) + bf'(a)E
g(f(a + bE)) = g(f(a) + bf'(a)E)
= g(f(a)) + bf'(a)g'(f(a))E
works
|#

(module+ test
  ; chain rule
  ; D (1 + 3x)^2 = 6(1+3x)
  (check-equal? (derivative (lambda (x) (expt/dual (+/dual 1 (*/dual 3 x)) 2)) 5)
                96))

; doesn't work for higher order derivatives

; tri numbers?

#|
T^3 = 0, T != 0, T^2 != 0
(a + bT)(c + dT)
ac+adT+bcT+bdT^2

f(x) = sum fn(0)x^n/n!
f(x) = f(0) + f'(0)x + f''(0)x^2/2 + f'''(0)x^3/6 ...
f(a+bT) = f(0) + f'(0)(a+bT) + f''(0)(a+bT)^2/2 + f'''(0)(a+bT)^3/6 ...
f(a+bT) = f(0) + f'(0)(a+bT) + f''(0)(a+bT)^2/2 + f'''(0)(a+bT)^3/6 ...


P(x) = c0 + c1x + c2x^2 + c3x^3 ...
P(a + bT) = c0 + c1a + c1bT + c2a^2 + 2c2abT + c2b^2T^2 + c3a^3 + 3c3a^2bT + 3c3ab^2T^2 + b^3T3
Did it on paper, turns out
f(a + b * delta) = sum (b^n / n!) f^(n)(a) delta^n
Taylor series
|#

; What if we just computed derivatives on DualNumbers instead of regular numbers?
; Then the result of derivative will be a differentiable function.
; Actually, that doesn't even make sense because f(a+bE) = f(a) + bf'(a)E, no f'(a+bE)
