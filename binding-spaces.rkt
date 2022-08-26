#lang racket

(module+ test (require rackunit))
(provide (all-defined-out))

(require (for-syntax syntax/parse syntax/stx))

(define-syntax space-let
  (syntax-parser
    [(_ space:id ([var:id rhs:expr] ...) body:expr ...)
     (define introducer (make-interned-syntax-introducer (syntax->datum #'space)))
     (define/syntax-parse (var^ ...) (stx-map (λ (stx) (introducer stx 'add)) (attribute var)))
     #'(let ([var^ rhs] ...) body ...)]))

(define-syntax space-define
  (syntax-parser
    [(_ space:id var:id rhs:expr)
     (define introducer (make-interned-syntax-introducer (syntax->datum #'space)))
     (with-syntax ([var^ (introducer #'var 'add)])
       #'(define var^ rhs))]
    [(_ space:id (f:id arg:expr ...) body:expr ...)
     (define introducer (make-interned-syntax-introducer (syntax->datum #'space)))
     (with-syntax ([f^ (introducer #'f 'add)])
       #'(define (f^ arg ...) body ...))]))

(define-syntax space-var
  (syntax-parser
    [(_ space:id var:id)
     (define introducer (make-interned-syntax-introducer (syntax->datum #'space)))
     (introducer #'var 'add)]))

(define-syntax add-space
  (syntax-parser
    [(_ space:id body:expr ...)
     (define introducer (make-interned-syntax-introducer (syntax->datum #'space)))
     (with-syntax ([(body^ ...) (stx-map (λ (stx) (introducer stx 'add)) (attribute body))])
       #'(begin body^ ...))]))

(define-syntax manip-space
  (syntax-parser
    [(_ space op body:expr ...)
     (define introducer (make-interned-syntax-introducer (syntax->datum #'space)))
     (with-syntax ([(body^ ...) (stx-map (λ (stx) (introducer stx (syntax->datum #'op))) (attribute body))])
       #'(begin body^ ...))]))

(module+ test
  (check-equal? (space-let s ([x 1]) (space-var s x)) 1)
  (check-equal? (let () (space-define s x 1) (space-var s x)) 1)
  (check-equal? (let () (space-define s (add1 x) (sub1 x)) (list (add1 1) ((space-var s add1) 1))) '(2 0)))

(module* foo #f (provide x (for-space s x)) (space-define s x 2) (define x 1))
; if you did require (for-space some-space-or-#f (submod ".." foo)), it tries to move both x bindings to the new space and errors
; provide for space is necessary to specify which x to provide
; require for space actually moves the identifiers to a new space
(module* main #f (require (submod ".." foo)) (println (space-var s x)) (println x))
