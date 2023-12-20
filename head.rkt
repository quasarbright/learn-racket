#lang racket

(define (eval expr env)
  (match expr
    [(? symbol?) (hash-ref env expr expr)]
    [`(lambda (,arg-name) ,body)
     (lambda (arg)
       (eval body (hash-set env arg-name arg)))]
    [`(,fun ,arg)
     ((eval fun env) (eval arg env))]))

(module+ test
  (require rackunit)
  (check-equal? (eval '((lambda (x) x) y) (hasheq))
                'y)
  (check-equal? (eval '(((lambda (x) (lambda (y) x))
                         a)
                        b)
                      (hasheq))
                'a))
