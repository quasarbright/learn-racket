#lang racket

#;(define-syntax-rule (~> arg fun ...)
  ((λ~> fun ...) arg))

(define-syntax (~> stx)
  (syntax-case stx ()
    [(~> arg) #'arg]
    [(~> arg (expr ...) fun ...)
     (with-syntax ([it (datum->syntax stx 'it)])
       #'(~> ((λ (it) (expr ...)) arg) fun ...))]
    [(~> arg expr fun ...)
     #'(~> (expr arg) fun ...)]))

(define-syntax-rule (λ~> fun ...)
  (reverse-compose (λ~>-help fun) ...))

(define-syntax (λ~>-help stx)
  (syntax-case stx ()
    [(λ~>-help (expr ...))
     (with-syntax ([it (datum->syntax stx 'it)])
       #'(λ (it) (expr ...)))]
    [(λ~>-help f) #'f]))

(define (reverse-compose . funs) (apply compose (reverse funs)))