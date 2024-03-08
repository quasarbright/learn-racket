#lang racket

; locks for concurrent programming

(module+ test (require rackunit))
(provide
 lock?
 ; (with-lock lck body ...)
 ; runs body once lck has been acquired, and releases it when body is done.
 ; if control leaves body, the lck is released. if it resumes, lck is reacquired.
 with-lock
 (contract-out
  [make-lock (-> lock?)]
  ; block until the lock is acquired.
  ; returns the release procedure.
  ; use with-lock instead, it's safer.
  [lock-acquire! (-> lock? (-> void?))]))
(require)

(struct lock [acquire-chan release-chan thd])

; -> Lock
(define (make-lock)
  (define acquire-chan (make-channel))
  (define release-chan (make-channel))
  (shared ([thd (thread
                 (lambda ()
                   (let loop ()
                     ; use a promise to ensure the release proc only works the first time
                     (define release-promise (delay (channel-put release-chan #t)))
                     (channel-put acquire-chan (lambda () (force release-promise)))
                     (void (channel-get release-chan))
                     (loop))))]
           [lck (lock acquire-chan release-chan thd)])
    lck))

; Lock -> (-> Void)
; blocks until the lock is acquired, returns release procedure.
(define (lock-acquire! lck)
  (channel-get (lock-acquire-chan lck)))

(define-syntax-rule (with-lock lck body ...)
  (let ([release #f])
    (dynamic-wind (lambda () (set! release (lock-acquire! lck)))
                  (lambda () body ...)
                  (lambda () (release)))))

(module+ test
  (test-case "simple hold and release"
    (define lck (make-lock))
    (define release (lock-acquire! lck))
    (release))
  (test-case "atomic counter"
    (define n 0)
    (define lck (make-lock))
    (define N 1000)
    (for/async ([_ (in-range N)])
      (with-lock lck (set! n (add1 n))))
    (check-equal? n N))
  (test-case "cannot re-use a release proc"
    (define lck (make-lock))
    (define v 'good)
    (define old-release (lock-acquire! lck))
    (old-release)
    (define new-release (lock-acquire! lck))
    ; this thread is trying to re-use the old release proc.
    ; it should stay blocked waiting for the lock since we never use new-release.
    (thread (lambda () (old-release) (lock-acquire! lck) (set! v 'bad)))
    ; make sure that bad thread has time to run and get blocked
    (sleep 0.01)
    (check-equal? v 'good)))
