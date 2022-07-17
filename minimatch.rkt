#lang racket

; http://rmculpepper.github.io/malr/basic.html

(require syntax/parse (for-syntax syntax/parse))
(module+ test (require rackunit))

(define-syntax minimatch1
  (syntax-parser
    [(_ val:expr pat result:expr) #'(let ([val-pv val]) (minimatch1* val-pv pat result))]))

(define-syntax minimatch1*
  (syntax-parser
    #:datum-literals (quote cons)
    [(_ val:id var:id result)
     #'(let ([var val]) result)]
    [(_ val:id (quote datum) result)
     #'(if (equal? val (quote datum)) result (error "value does not match datum" val (quote datum)))]
    [(_ val:id (cons first-pat rest-pat) result)
     #'(begin
       (unless (cons? val) (error "value is not a non-empty list" val))
       (let ([first-var (car val)])
         (minimatch1* first-var
           first-pat (let ([rest-var (cdr val)])
                       (minimatch1* rest-var rest-pat result)))))]))

(module+ test
  (check-equal? (minimatch1 (list 1 2 3) x (list x x))
                '((1 2 3) (1 2 3)))
  (check-equal? (minimatch1 (list 1) (cons a b) (list a b))
                '(1 ()))
  (check-equal? (minimatch1 2 (quote 2) 3)
                3)
  (check-equal? (minimatch1 '() (quote ()) 4)
                4)
  (check-equal? (minimatch1 (list 1 2 3)
                            (cons first (cons second rest)) (list first second))
                '(1 2))
  (check-equal? (minimatch1 (list 1 2 3)
                            (cons a (cons b (cons (quote 3) (quote ()))))
                            (list a b))
                '(1 2)))


; see if that works
; you're compiling the pattern to ANF and expanding the pattern as you go
; could be split into 2 passes

#;
(match val [(cons first rest) result])
;=>
#;
(let ([val-pv val])
  (begin
    (unless (cons? val-pv) (error))
    (let ([first (car val-pv)] [rest (cdr val-pv)])
      result)))

#;
(match val [(cons first (cons second rest)) result])
;=>
#;
(let ([val-pv val])
  (begin
    (unless (cons? val-pv) (error))
    (let ([first (car val-pv)] [val-pv2 (cdr val-pv)])
      (let ([second ...])))))

(define-syntax minimatch
  (syntax-parser
    [(_ val:expr clause ...+)
     #'(let ([val-pv val]) (minimatch-pv val-pv clause ...))]))

(define-syntax minimatch-pv
  (syntax-parser
    [(_ val:id)
     #'(error 'minimatch "no patterns matched")]
    [(_ val:id [pat result:expr] clause ...)
     #'(minimatch* val pat result (minimatch-pv val clause ...))]))

(define-syntax minimatch*
  (syntax-parser
    [(_ val:id pat on-success:expr on-fail:expr)
     (syntax-parse #'pat
       #:datum-literals (quote cons)
       [var:id
        #'(let ([var val]) on-success)]
       [(quote datum)
        #'(if (equal? val (quote datum))
              on-success
              on-fail)]
       [(cons first-pat rest-pat)
        ; it's ok to be passing on-fail around in many places
        ; it'll get evaluated at most once since it's always in an if
        #'(if (cons? val)
              (let ([first-pv (first val)] [rest-pv (rest val)])
                (minimatch* first-pv first-pat (minimatch* rest-pv rest-pat on-success on-fail) on-fail))
              on-fail)])]))

(module+ test
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
                                         [(cons a (cons b (quote 4))) 5]))))



