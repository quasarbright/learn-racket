#lang racket

#|

pattern matcher

if a pattern fails, move to the next match. If all fail, error out

if a sub-pattern fails, the whole pattern fails (unless it's in an or pattern)

matching a literal succeeds iff the actual value is equivalent

matching a var pattern binds that variable to the matched value in the rhs

matching a _ pattern always succeeds

matching a list pattern just recurs on children


continuations would be good. Like if you had an onfail continuation. idk how continuations work though

(match (1 2 3) ((x y z) x))
(match 1 (x (match (2 3) ((y z) x))))

|#


(define (match-transform dtm)
  (match dtm
    [`(match (list) ((list) ,body)) body]
    [`(match (list ,target ,targets ...) ((list ,p ,ps ...) ,body)) (match-transform `(match ,target (,p ,(match-transform `(match (list . ,targets) ((list . ,ps) ,body))))))]
    [`(match ,target (,x ,body))
     (cond
       [(symbol? x) `(let ((,x ,target)) ,body)]
       [(number? x) `(if (equal? ,x ,target) ,body (error "literals not equal"))]
       [else (error "unknown")])]
    ))

(match-transform '(match (list 1 2) ((list x 2) x)))



  