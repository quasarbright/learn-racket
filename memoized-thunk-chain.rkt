#lang racket

(require racket/generic)

(define-generics promise
  (force promise)
  (promise-forced? promise))
;; A promise is a memoized thunk
;; Its thunk is evaluated at most once

(struct simple-promise (thnk [result #:mutable] [forced? #:mutable])
  #:transparent
  #:methods gen:promise
  [(define (force p) (naive-force p))
   (define (promise-forced? p) (simple-promise-forced? p))])
;; A promise that stores its result

;; Force a promise and update its stored result if it has not been forced already
(define (naive-force p)
  (if (promise-forced? p)
      (simple-promise-result p)
      (let ([result ((simple-promise-thnk p))])
        (set-simple-promise-result! p result)
        (set-simple-promise-forced?! p #t)
        result)))

(define (make-simple-promise thnk)
  (simple-promise thnk #f #f))

;; Create a promise which evaluates to the last expression in body when forced
(define-syntax-rule (delay body ...)
  (make-simple-promise (lambda () body ...)))

(struct composable-promise simple-promise ()
  #:transparent
  #:methods gen:promise
  [(define/generic super-force force)
   (define/generic super-forced? promise-forced?)
   (define (promise-forced? p) (simple-promise-forced? p))
   (define (force p)
     (composable-force p))])
;; A promise which collapses a chain of promises
;; If the result evaluates to a promise, force that promise too and store that instead
;; In order to be tail recursive, if we our result is a promise, we grab its thunk, evaluate it,
;; set the inner promise's result to this promise, and repeat????

;; Force a composable promise, forcing other composable promises inside of it as well
;; Forces and flattens the whole chain tail recursively
(define (composable-force p)
  (define result (naive-force p))
  (cond
    [(composable-promise? result) (define inner-promise result)
                                  (define inner-result (naive-force result))
                                  (set-simple-promise-result! p inner-result) ; can't say set-composable... ??
                                  (if (composable-promise? inner-result)
                                      (begin (set-simple-promise-result! inner-promise p) ; flip the pointers
                                             ; was p1 -> p2 -> p3
                                             ; now it's p2 -> p1 -> p3
                                             ; repeat to collapse p1 -> p3
                                             ; will lead to all sub-promises pointing to p1
                                             ; except for the last one (which produces a final value)
                                             (composable-force p)) ; tail call
                                      inner-result)]
    [else result]))

(define (make-composable-promise thnk) (composable-promise thnk #f #f))

;; Creates a composable promise that evaluates to the last expression in body when forced
(define-syntax-rule (lazy body ...)
  (make-composable-promise (lambda () body ...)))

(module+ test (require rackunit))

;; test simple promises
(module+ test
  (test-equal? "force . delay = id"
               (force (delay 2))
               2)
  (test-equal? "delay handles multiple expressions"
               (force (delay 1 2))
               2)
  (test-equal? "delay handles statements"
               (force (delay (define x 1) (set! x 2) x))
               2)
  (test-case "doesn't run until forced"
    (define x 1)
    (define p (delay (set! x 3) x))
    (check-equal? x 1)
    (check-equal? (force p) 3)
    (check-equal? x 3))
  (test-case "force is idempotent"
    (define x 2)
    (define p (delay (set! x (add1 x)) x))
    (check-equal? x 2)
    (check-equal? (force p) 3)
    (check-equal? x 3)
    (check-equal? (force p) 3)
    (check-equal? x 3)))

;; test composable promises
(module+ test
  (test-equal? "force . lazy = id"
               (force (lazy 2))
               2)
  (test-equal? "2 lazies deep"
               (force (lazy (lazy 2)))
               2)
  (test-equal? "3 lazies deep"
               (force (lazy (lazy (lazy 2))))
               2)
  (test-equal? "many lazies deep"
               (force (lazy (lazy (lazy (lazy (lazy (lazy (lazy 'foo))))))))
               'foo))



