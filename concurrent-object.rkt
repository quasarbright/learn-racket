#lang racket

(provide
 ; a class with concurrent methods that can be called
 ; concurrently, but the calls are processed serially.
 ; concurrent method calls are blocking.
 concurrent-object%
 ; defines a concurrent method in a class. concurrent methods are executed serially even
 ; if called concurrently, and block until completion.
 ; this form can only be used inside of a class definition, and only inside a subclass of concurrent-object%
 define/concurrent)
(module+ test (require rackunit))
(require racket/async-channel)

; this is an example usage:
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
    (check-equal? (send counter get) N)))

; here is how you might implement something like this
(define atom-example%
  (class object%
    (super-new)
    (init-field val)
    (define chan (make-async-channel))

    (define thd
      (thread
       (lambda ()
         (let loop ()
           (match (async-channel-get chan)
             [`(get ,k) (k val)]
             [`(update! ,proc ,k)
              (set! val (proc val))
              (k val)]
             [_ (error "unknown operation")])
           (loop)))))

    (define/public (get)
      (with-async k
        (async-channel-put chan `(get ,k))))
    (define/public (update! proc)
      (with-async k
        (async-channel-put chan `(update! ,proc ,k))))))

; runs body, which kicks off some async process
; which will call k exactly once with its result.
; blocks until k is called.
; whole form evaluates to the argument of k.
(define-syntax-rule
  (with-async k body ...)
  (let ()
    (define result-chan (make-channel))
    (let ([k (lambda (result) (channel-put result-chan result))])
      body
      ...
      (channel-get result-chan))))

(module+ test
  (define counter (new atom-example% [val 0]))
  (define N 1000)
  (for/async ([_ (in-range N)])
    (send counter update! add1))
  (check-equal? (send counter get) N))

; we need to be more careful about error handling.
; currently, if the implementation of an async method fails to call
; the continuation, the caller will be blocked forever.
; from the loop, we will call k with a thunk that throws the error or returns
; the result.

(define concurrent-object%
  (class object%
    (super-new)

    (define chan (make-async-channel))
    ; maps method names (symbols) to implementations (procedures)
    (define concurrent-methods (make-hasheq))

    ; event loop
    (define thd
      (thread
       (lambda ()
         (let loop ()
           (match (async-channel-get chan)
             [(list name args ... k)
              ; this doesn't need to be in with-handlers because it should never happen
              (define proc (hash-ref concurrent-methods name (lambda () (error "unknown operation"))))
              ; we don't just put the call in the lambda because we want the computation to run in this thread
              (with-handlers ([exn:fail? (lambda (err) (k (lambda () (raise err))))])
                (define result (apply proc args))
                (k (lambda () result)))]
             [_ (error "unknown operation")])
           (loop)))))

    (define/public (#%call-concurrent-method name args)
      (when (thread-dead? thd)
        (error '#%call-concurrent-method "event loop down"))
      (define thnk
        (with-async k
          (async-channel-put
           chan
           (append (list name)
                   args
                   (list k)))))
      (thnk))

    (define/public (#%add-concurrent-method! name proc)
      (hash-set! concurrent-methods name proc))))

(define-syntax-rule (define/concurrent (name arg ...) body ...)
  (begin
    (unless (is-a? this concurrent-object%)
      (error 'define/concurrent "cannot be used outside of a concurrent-object%"))
    (define/public (name arg ...)
      (send this #%call-concurrent-method 'name (list arg ...)))
    (let ([proc (lambda (arg ...) body ...)])
      (send this #%add-concurrent-method! 'name proc))))

(module+ test
  (test-case "exceptions in a method do not cause deadlock"
        (define bad%
          (class concurrent-object%
            (super-new)
            (define/concurrent (boom) (error "oh no!"))))
        (define bad (new bad%))
        (check-exn exn:fail? (lambda () (send bad boom)))))
