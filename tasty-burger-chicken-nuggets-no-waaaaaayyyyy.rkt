#lang racket

; An Env is a (hash symbol value)

(define (eval expr env)
  (match expr
    [(? symbol? expr) (hash-ref env expr (lambda () (error "unbound variable")))]
    [`(lambda (,x) ,body)
     (lambda (v) (eval body (hash-set env x v)))]
    [`(,rator ,rand)
     ((eval rator env) (eval rand env))]
    [_ expr]))

(module+ test
  (require rackunit)
  (check-equal? (eval '1 (hasheq))
                1)
  (check-equal? (eval '((lambda (x) x) 2) (hasheq))
                2)
  (check-equal? (eval '(((lambda (x) (lambda (y) x)) 1) 2) (hasheq))
                1))
