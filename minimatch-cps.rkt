#lang racket

(require syntax/parse (for-syntax syntax/parse))

(module+ test (require rackunit))

(define-syntax minimatch1
  (syntax-parser
    [(_ val pat result)
     #'(let ([val-pv val])
         (minimatch1* val-pv pat result))]))

#;(-> any/c any/c (-> any) (-> any))
(define (match-equal? val expected on-success on-fail)
  (if (equal? expected val)
      (on-success)
      (on-fail)))

#;(-> any/c (-> any/c any/c any) (-> any))
(define (match-cons val on-success on-fail)
  (if (cons? val)
      (on-success (car val) (cdr val))
      (on-fail)))

(define-syntax minimatch1*
  (syntax-parser
    [(_ val-pv:id pat result)
     (syntax-parse #'pat
       #:datum-literals (cons quote)
       [var:id
        ; could probably be a let
        #'((λ (var) result) val-pv)]
       [(quote datum)
        #'(match-equal? val-pv (quote datum) (λ () result) (λ () (error "expected datum" (quote datum) val-pv)))]
       [(cons first-pat rest-pat)
        #'(match-cons val-pv (λ (first-pv rest-pv) (minimatch1* first-pv first-pat (minimatch1* rest-pv rest-pat result))) (λ () (error "expected cons" val-pv)))]
       [(list) #'(minimatch1* val-pv '() result)]
       [(list pat pats ...) #'(minimatch1* val-pv (cons pat rest-pv) (minimatch1* rest-pv (list pats ...) result))])]))

(module+ test
  (check-equal? (minimatch1 (list 1) (cons a b) (list a b)) '(1 ()))
  (check-equal? (minimatch1 (list 1) (cons a '()) (list a)) '(1))
  (check-equal? (minimatch1 (list 1 2 3) (list a b c) (list a b c)) '(1 2 3)))

#;
(match (list 1)
  [(cons a '()) a])
#;
((let ([val (list 1)])
  (match-cons val
              (λ (first rest)
                ((λ (a)
                   (match-datum '() rest
                                (λ () a)))
                 first))))
 (list 1))
; the guard procedures use CPS, and you compile to lambdas that follow the scoping
; compilation results in one huge lambda that uses CPS guards. No problem of scope loss from applying remotely defined procedures
