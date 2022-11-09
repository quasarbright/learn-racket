#lang racket

; This module implements algebraic effects via delimited continuations.
; Unlike the original implementation, it does not use exceptions.

;; module interface ;;

(module+ test (require rackunit))
(provide)

;; dependencies ;;

(require racket/control)

;; data definitions ;;

; custom error types
(struct exn:fail:algebraic-effects exn:fail () #:transparent)
(struct exn:fail:algebraic-effects:unhandled  exn:fail:algebraic-effects () #:transparent)
; Represents an unhandled algebraic effect.
; This exception is thrown when an effect is performed, but there is no handler in scope for it.

;; functionality ;;

; a custom prompt tag used to avoid collision with other reset shifts
(define ae-tag (make-continuation-prompt-tag 'algebraic-effects-prompt-tag))

#;(any/c continuation? -> any/c)
; the current handler for algebraic effects.
; takes in an effect value and a continuation from which the effect was performs,
; and handles the effect in some way.
; The default value raises an exception that the effect is unhandled.
(define current-effect-handler
  (make-parameter (λ (v _) (raise (exn:fail:algebraic-effects:unhandled (format "Unhandled effect: ~v" v)
                                                                        (current-continuation-marks))))))

#;(any/c any/c)
; Perform an effect with the specified value.
(define (perform value)
  (let ([handler (current-effect-handler)])
    (shift-at ae-tag k
              ; this works because you get the handler OUTSIDE of the shift
              (handler value k)
              #;
              (handler value (λ (hole-filler)
                               ; We must restore the handler before resuming.
                               ; Otherwise, if we resume outside of the dynamic extent of the original
                               ; parameterize (like if k escapes the with-effect-handler form),
                               ; the handler is lost and just uses whichever one is around when you call
                               ; the continuation.
                               ; We perform an effect. That shifts and the delimited continuation escapes.
                               ; This continuation escapes the parameterize's dynamic extent.
                               ; you resume it and another effect is performed. The current effect handler
                               ; is used, which is no longer the original one.
                               ; this is weird but it's necessary
                               ; I feel like there is an edge case where this restoration overrides a
                               ; handler inappropriately.
                               ; TODO think about it more.
                               ; parameterize is continuation-y. That's probably why this weird behavior happens.
                               (parameterize ([current-effect-handler handler])
                                 (k hole-filler)))))))
#;; TODO try this?
[
 (with-effect-handler handler body ...)
 ~>
 (let ([handler-v handler])
   (syntax-parameterize ([perform (make-variable-like-transformer #'(λ (value) (shift k (handler-v value k))))])
     (reset body ...)))
 ]

; not viable bc then you can only use perform syntactically within a with-... form
; that makes no sense

(define-syntax-rule
  (with-effect-handler handler body ...)
  ; I tried trampolining before I had a parameter, but it didn't work for some reason.
  ; Maybe if the continuation escapes, the behavior is different. Or maybe I did it wrong.
  ; Probably that. This stuff is very subtle.
  (reset-at ae-tag
            (parameterize ([current-effect-handler handler])
              body ...)))

#|
If you have a generator in a generator, inner perform might break out to the outer reset.
control might fix it. Or you could just gensym a tag for each "with" and have the tag be a parameter.
|#

;; testing ;;

(module+ test
  (test-case "simple add1 effect"
    (check-equal? (with-effect-handler (λ (v k) (k (add1 v)))
                    (perform 1))
                  2))
  (test-case "multiple performs"
    (check-equal? (with-effect-handler (λ (v k) (k (add1 v)))
                    (list (perform 1) (perform 2)))
                  (list 2 3)))
  (test-case "resume twice"
    (check-equal? (with-effect-handler (λ (v k) (list (k #t) (k #f)))
                    (perform 42))
                  (list #t #f)))
  (test-case "capture k and resume after with-effect-handler"
    ; like add1 effect, but we wrap the resumption in a thunk and it all escapes the with-effect-handler
    (let ([thnk (with-effect-handler (λ (v k) (λ () (k (add1 v)))) (list (perform 1) (perform 2)))])
      (check-equal? ((thnk)) (list 2 3))))
  (test-case "capture k and resume in another with-effect-handler (resuming restores its original handler)"
    (let ([thnk (with-effect-handler (λ (v k)
                                       (λ () (k (add1 v))))
                  (list (perform 1) (perform 2)))])
      (check-equal? (with-effect-handler (λ (v k) (k 42))
                      ; this thunk will resume and perform effects,
                      ; but in a context with the thunk add1 handler, not the 42 one
                      (list (perform #f) ((thnk)) (perform #f)))
                    '(42 (2 3) 42))))
  (test-case "perform in a perform"
    (check-equal?
     (with-effect-handler (λ (v k) (k (add1 v)))
       (list (perform (* 2 (perform 3)))))
     '(9)))
  (test-case "non-determinism"
    (define (choice . items)
      (perform items))
    (define (nondet-handler items k)
      (for/fold ([result '()])
                ([item items])
        (append result (k item))))
    (define-syntax-rule (nondet body ...) (with-effect-handler nondet-handler (list (let () body ...))))
    (check-equal? (nondet 1) '(1))
    (check-equal? (nondet (choice 1 2)) '(1 2))
    (check-equal? (nondet (list (choice 1 2) (choice 3 4)))
                  '((1 3) (1 4) (2 3) (2 4))))
  (test-case "generator"
    (define yield perform)
    (define (yield* items) (for ([item items]) (yield item)))
    (define (gen-handler v k)
      (stream-cons v (k (void))))
    (define-syntax-rule (generator body ...) (with-effect-handler gen-handler body ... empty-stream))
    (check-equal? (stream->list (generator (yield 1)))
                  '(1))
    (check-equal? (stream->list (generator (yield 1) (yield 2)))
                  '(1 2)))
  (test-case "generator in a generator"
    (define yield perform)
    (define (yield* items) (for ([item items]) (yield item)))
    (define (gen-handler v k)
      (stream-cons v (k (void))))
    (define-syntax-rule (generator body ...) (with-effect-handler gen-handler body ... empty-stream))
    (check-equal? (stream->list (generator (yield 1) (yield* (generator (yield 2) (yield 3)))))
                  '(1 2 3))
    (check-equal? (stream->list (generator (yield 1)
                                           (let ([inner (generator (yield 2) (yield 3))])
                                             (yield* inner))))
                  '(1 2 3)))
  (test-case "state"
    (define (get) (perform 'get))
    (define (put v) (perform (list 'put v)))
    (define (modify f) (put (f (get))))
    (define current-state (make-parameter 'uninitialized-state))
    (define (state-handler v k)
      (match v
        ['get (k (current-state))]
        [(list 'put new-state)
         (parameterize ([current-state new-state]) (k (void)))]))
    (define-syntax-rule
      (state initial body ...)
      (with-effect-handler state-handler
        (let ([result (let () (put initial) body ...)]) (list (get) result))))
    (check-equal? (state 1 (get)) (list 1 1))
    (check-equal? (state 1 (put 2) (get)) (list 2 2))
    (check-equal? (state 1 (put 2) 3) (list 2 3))))
