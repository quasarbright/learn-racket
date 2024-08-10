#lang racket

; Waier Hierarchy

; Ordinals can be represented as (-> Natural Natural) functions.
; add1 is 0, + is 1, * is 2, ^ is 3, and so on. More precisely,
; f_0(x) = x + 1
; f_1(x) = f_0(f_0(...f_0(x))) with x calls to f_0
; f_1(x) = (((x + 1) + 1) ... + 1) with x 1s
; f_1(x) = x + x = 2x
; f_2(x) = f_1(f_1(...(f_1(x))))
; f_2(x) = (2^x)*x
; ...
; The function itself is the ordinal. NOT the argument or anything like that.
; The subscript corresponds to the value of the ordinal.
; The successor operation is taking the previous operation and repeatedly applying it
; the same number of times as the value of the argument.
; These numbers get CRAZY big very fast.

(module+ test (require rackunit))

; an Ordinal is a (-> Natural Natural)

; Ordinal
(define zero add1)
; Ordinal -> Ordinal
(define ((succ f) x)
  ((repeat f x) x))

; (A -> A) Natural -> (A -> A)
; applies f to x reps times
(define ((repeat f reps) x)
  (let loop ([reps reps]
             [acc x])
    (if (zero? reps)
        acc
        (loop (sub1 reps)
              (f acc)))))

; 2x
(define one (succ zero))
; x2^x
(define two (succ one))
(define three (succ two))

(module+ test
  (check-equal? (zero 3)
                4)
  (check-equal? (one 3)
                6)
  (check-equal? (two 3)
                24)
  (check-equal? (three 2)
                2048)
  ; three(3)
  ; two(two(two(3)))
  ; two(two(24))
  ; two(402653184)
  ; very big. applies one 402,653,184 times. The result is more than 402653184 bits long, which is like 50 megabytes.
  #;(check-equal? (three 3)
                BIG))

; Natural -> Ordinal
(define (natural->ordinal n) ((repeat succ n) zero))

(module+ test
  (check-equal? ((natural->ordinal 3) 2)
                2048))

; f_omega(x) = f_x(x) = ((natural->ordinal x) x)
(define omega (lambda (x) ((natural->ordinal x) x)))
(define omega+1 (succ omega))
; Natural -> Ordinal
(define (omega+n n) ((repeat succ n) omega))
(define omega+omega (lambda (x) ((omega+n x) x)))
; Ordinal -> Ordinal
(define (+omega f) (lambda (x) (((repeat succ x) f) x)))
; Natural -> Ordinal
(define (omega*n n) ((repeat +omega n) zero))
(define omega*omega (lambda (x) ((omega*n x) x)))

(define (*omega f) (lambda (x) (((repeat +omega x) f) x)))
(define (omega^n n) ((repeat *omega n) one))
(define omega^omega (lambda (x) ((omega^n x) x)))

(define (^omega f) (lambda (x) (((repeat +omega x) f) x)))
(define (omega-arrow-n n) ((repeat ^omega n) one))
(define epsilon_0 (lambda (x) ((omega-arrow-n x) x)))
