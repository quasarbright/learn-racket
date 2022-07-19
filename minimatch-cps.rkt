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

(define-syntax minimatch
  (syntax-parser
    [(_ val clause ...+)
     #'(let ([val-pv val])
         (minimatch-pv val-pv clause ...))]))

(define-syntax minimatch-pv
  (syntax-parser
    #:datum-literals (=>)
    [(_ val-pv:id) #'(error 'minimatch "all branches failed")]
    [(_ val-pv:id [pat result:expr] clause ...)
     #'(minimatch* val-pv pat result (minimatch-pv val-pv clause ...))]
    [(_ val-pv:id [pat (=> fail:id) result:expr] clause ...)
     #'(let/cc k (let* ([on-fail-thunk (λ () (minimatch-pv val-pv clause ...))]
                        [fail (λ () (k (on-fail-thunk)))])
                   (minimatch* val-pv pat result (on-fail-thunk))))]))

(define-syntax minimatch*
  (syntax-parser
    [(_ val-pv:id pat on-success:expr on-fail:expr)
     (syntax-parse #'pat
       #:datum-literals (quote cons list or)
       [var:id #'((λ (var) on-success) val-pv)]
       [(quote datum) #'(match-equal? val-pv (quote datum) (λ () on-success) (λ () on-fail))]
       [(cons first-pat rest-pat)
        #'(match-cons val-pv (λ (first-pv rest-pv) (minimatch* first-pv first-pat (minimatch* rest-pv rest-pat on-success on-fail) on-fail)) (λ () on-fail))]
       [(list) #'(minimatch* val-pv '() on-success on-fail)]
       [(list pat pats ...)
        #'(minimatch* val-pv (cons pat rest-pv) (minimatch* rest-pv (list pats ...) on-success on-fail) on-fail)]
       [(or) #'on-fail]
       [(or pat pats ...)
        #'(minimatch* val-pv pat on-success (minimatch* val-pv (or pats ...) on-success on-fail))])]))

(module+ test
  ; tests from 
  (check-equal? (minimatch 4 [x (list x x)])
                '(4 4))
  (check-equal? (minimatch 5 [(quote 5) 6])
                6)
  (check-equal? (minimatch (list 1) [(cons a b) (list a b)])
                '(1 ()))
  (check-equal? (minimatch 3 [(cons a b) 4] [c 5])
                5)
  (check-equal? (minimatch (list 1 2 3) [(cons a (cons (quote 4) b)) 5] [x 6])
                6)
  (check-equal? (minimatch (list 1 2 3) [(cons a (cons b (quote 4))) 5] [x 6])
                6)
  (check-equal? (minimatch (list #t) ['1 1] ['2 2] ['3 3] [x 4])
                4)
  (check-equal? (minimatch (list 1 2 3)
                           [(cons a (cons b (quote 4))) 5]
                           [(cons a (cons b (quote 4))) 5]
                           [(cons a (cons b (quote 4))) 5]
                           [(cons a (cons b (quote 4))) 5]
                           [(cons a (cons b (quote 4))) 5]
                           [(cons a (cons b (quote 4))) 5]
                           [x 6])
                6)
  (check-exn exn:fail? (thunk (minimatch 2 [(cons a b) 3])))
  (check-exn exn:fail? (thunk (minimatch 2 ['3 4])))
  (check-exn exn:fail? (thunk (minimatch (list 1 2 3)
                                         [(cons a (cons b (quote 4))) 5]
                                         [(cons a (cons b (quote 4))) 5]
                                         [(cons a (cons b (quote 4))) 5]
                                         [(cons a (cons b (quote 4))) 5]
                                         [(cons a (cons b (quote 4))) 5]
                                         [(cons a (cons b (quote 4))) 5])))
  (check-equal? (minimatch (list 1 2) [(or (cons a (cons b '())) (cons '42 (cons a (cons b '())))) (list a b)])
                (list 1 2))
  (check-equal? (minimatch (list 1 2) [(or (cons '42 (cons a (cons b '()))) (cons a (cons b '()))) (list a b)])
                (list 1 2))
  ; this runs very slowly if you add more
  (check-equal? (minimatch (list 1 2) [(or (cons '42 (cons a (cons b '())))
                                           (cons '42 (cons a (cons b '())))
                                           (cons '42 (cons a (cons b '())))
                                           (cons a (cons b '())))
                                       (list a b)])
                (list 1 2))
  (check-equal? (minimatch (list 1 2)
                           [a (=> fail) (fail)]
                           [b (list b b)])
                '((1 2) (1 2))))
