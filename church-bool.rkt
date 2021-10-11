#lang racket

(define t (lambda (a b) a))
(define f (lambda (a b) b))
(define my-op (lambda (p q) (p q f)))
(define (test b) (b #t #f))

