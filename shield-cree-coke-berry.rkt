#lang racket

(require rackunit)

(define (eval sexpr)
  (match sexpr
    [`(lambda (,x) ,body) (lambda (arg) (eval (subs body x arg)))]
    [`(,func ,arg) ((eval func) (eval arg))]
    [x x]))

(define (subs expr var rep)
  (match expr
    [`(lambda (,x) ,body)
     (if (eq? x var) expr `(lambda (,x) ,(subs body var rep)))]
    [`(,func ,arg) (list (subs func var rep) (subs arg var rep))]
    [x (if (eq? x var) rep x)]))

(check-equal?
 (eval `((lambda (x) x) y))
 'y)

(check-equal? (eval `(((lambda (x) (lambda (y) x))
                foo)
                bar))
              'foo)
