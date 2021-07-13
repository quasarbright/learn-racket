#lang racket

(define (eval env e)
  (let ((recur (lambda (arg) (eval env arg))))
  (match e
    [x #:when (symbol? x) (let ((v (assoc x env))) (if v (first v) (error "unbound")))] ; var ref
    [(list (or 'lambda 'λ) (list argnames ...) body) e]
    [(list f args ...) (app env (recur f) (map recur args))] ; application
    [_ e] ; literal
    )))

(define (app env f args)
  (match f
    [(list (or 'lambda 'λ) (list argnames ...) body) (eval (append (map cons argnames args) env) body)]))

(require rackunit)

(check-equal? (eval empty '(lambda (x) x)) '(lambda (x) x))
(check-equal? (eval empty '((lambda (x) x) 1)) 1)