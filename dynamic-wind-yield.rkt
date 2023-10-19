#lang racket

(require racket/control)

; dynamic wind in terms of yield from oleg

(struct yield-record [v k] #:transparent)
; just a case analysis on a pure value, no control stuff
(define-syntax try-yield
  (syntax-rules ()
    ((try-yield exp (r on-r) (v k on-y))
     (let ((exp-r exp))
       (match exp-r
         [(yield-record v k)
          on-y]
         [r on-r])))))
(define (yield v) (shift k (yield-record v k)))

; Now we implement dynamic-wind, with the standard interface

(define (dynamic-wind before-thunk thunk after-thunk)
  (let loop ((th (lambda () (reset (thunk)))))
    (before-thunk)
    (let ((res (th)))
      (after-thunk)
      (match res
        [(yield-record v k)
         (let ((reenter (yield v)))
           (loop (lambda () (k reenter))))]
        [r r]))))

(define-syntax-rule (user-reset body ...) (user-reset* (lambda () body ...)))
(define (user-reset* thnk)
  (match (reset (thnk))
    [(yield-record v k)
     (match v
       [(shift-record f) (user-reset (f k))]
       #;
       [(call/cc-record f)
        (k (lambda () (f (lambda (x) (yield (begin (k (lambda () x)) #f))))))]
       [_ (error "unhandled yield from user reset")])]
    [r r]))

(define user-call/cc
  (lambda (p)
    (user-shift k (k (p (lambda (x)
                          (user-shift k1 (k x))))))))

(define-syntax-rule (user-shift k body ...) (user-shift* (lambda (k) body ...)))
(struct shift-record [f] #:transparent)
(define (user-shift* f)
  (yield (shift-record f)))

; has behavior that would lend itself to parameterize around composable continuation!
; it works!
(let ([saved-k #f])
  (dynamic-wind
    (lambda () (displayln "before"))
    (lambda ()
      (user-reset
       (dynamic-wind
         (lambda () (displayln "body before"))
         (lambda () (add1 (user-shift k (displayln "shift") (set! saved-k k))))
         (lambda () (displayln "body after")))))
    (lambda () (displayln "after")))
  (dynamic-wind (lambda () (displayln "after before"))
                (lambda () (list (saved-k 0) (saved-k 9)))
                (lambda () (displayln "after after"))))
