#lang racket

;; Implementation of generators via delimited continuations

(require racket/control)

(define prompt-tag (make-continuation-prompt-tag))

;; Get the next value, or void if there are none left
(define (g-next g [v (void)])
  (g-force g)
  (match g
    [(g-wrapper (g-yield val k))
     ; shouldn't be evaluating this since it may not be necessary
     (set-g-wrapper-state! g (k v))
     val]
    [(g-wrapper (g-done)) (void)]))

;; If g is a thunk, evaluate it
(define (g-force g)
  (match g
    [(g-wrapper (g-thunk thnk))
     (define result (thnk))
     (set-g-wrapper-state! g (thnk))]
    [else (void)]))

(struct g-wrapper ([state #:mutable]) #:transparent
  #:property
  prop:procedure
  g-next)
(struct g-thunk (thnk) #:transparent)
(struct g-yield (val k) #:transparent)
(struct g-done () #:transparent)

;; Yield a value from a generator. Suspends execution of the body
;; Use outside of a generator raises an exception
(define (yield val)
  (unless (continuation-prompt-available? prompt-tag)
    (error "used a yield outside of a generator form"))
  (shift-at prompt-tag k (g-yield val k)))

;; Create a generator
(define-syntax-rule (generator body ...)
  (g-wrapper (g-thunk (thunk (prompt-at prompt-tag body ... (g-done))))))

;; Sequence which iterates over generator elements
(define (in-generator g)
  (g-force g)
  (let loop ()
    (if (generator-done? g)
        empty-stream
        (stream-cons (g) (loop)))))

;; Is the generator in a done state?
;; If it has never been evaluated, 
(define (generator-done? g)
  (g-done? (g-wrapper-state g)))

;; example
(define g (generator (map yield '(1 2 3 4 5))))
(sequence->list (in-generator g))
