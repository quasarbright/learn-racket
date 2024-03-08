#lang racket

; like concurrent-object.rkt, but in terms of locks.
; has slightly different behavior because the methods actually
; run on the caller thread instead of an event loop thread.

(module+ test (require rackunit))
(provide concurrent-object% define/concurrent)
(require "./lock.rkt")

(define concurrent-object%
  (class object%
    (super-new)
    (define lck (make-lock))
    (define/public (#%with-lock thnk)
      (with-lock lck (thnk)))))

(define-syntax-rule
  (define/concurrent (name arg ...) body ...)
  (define/public (name arg ...)
    (send this #%with-lock (lambda () body ...))))

(module+ test
  (test-case "atomic counter"
    ; a concurrently modifiable cell
    (define atom%
      (class concurrent-object%
        (super-new)
        (init-field val)
        (define/concurrent (get) val)
        (define/concurrent (update! proc)
          (set! val (proc val))
          val)))
    (define counter (new atom% [val 0]))
    (define N 1000)
    (for/async ([_ (in-range N)]) (send counter update! add1))
    (check-equal? (send counter get) N))
  (test-case "exceptions in a method do not cause deadlock"
        (define bad%
          (class concurrent-object%
            (super-new)
            (define/concurrent (boom) (error "oh no!"))))
        (define bad (new bad%))
        (check-exn exn:fail? (lambda () (send bad boom)))))
