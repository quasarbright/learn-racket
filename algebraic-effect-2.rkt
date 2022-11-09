#lang racket

; This module implements algebraic effects via delimited continuations.
; Unlike the original implementation, it does not use exceptions.

;; module interface ;;

(module+ test (require rackunit))
(provide)

;; dependencies ;;

(require racket/control (for-syntax syntax/parse))

;; data definitions ;;

; custom error types
(struct exn:fail:algebraic-effects exn:fail () #:transparent)
(struct exn:fail:algebraic-effects:unhandled  exn:fail:algebraic-effects () #:transparent)
; Represents an unhandled algebraic effect.
; This exception is thrown when an effect is performed, but there is no handler in scope for it.

;; functionality ;;

#;(any/c continuation? -> any/c)
; the current handler for algebraic effects.
; takes in an effect value and a continuation from which the effect was performed,
; and handles the effect in some way.
; The default value raises an exception that the effect is unhandled.
(define current-effect-handler
  (make-parameter (λ (v _) (raise (exn:fail:algebraic-effects:unhandled (format "Unhandled effect: ~v" v))))))

(define (new-prompt-tag) (make-continuation-prompt-tag (gensym 'algebraic-effects-prompt-tag)))

#;continuation-prompt-tag?
; the default prompt tag used for effect handling.
(define default-tag (new-prompt-tag))

#;(any/c any/c)
; Perform an effect with the specified value.
; Optionally takes in a prompt tag.
; NOTE: this does not mean you'll use the same handler as a corresponding 'with'
; TODO make handlers associated with prompt tags
(define (perform value #:tag [tag #f])
  (let ([handler (current-effect-handler)]
        [tag (or tag default-tag)])
    (shift-at tag k
              ; this works because you get the handler OUTSIDE of the shift
              (handler value k))))

(define-syntax with-effect-handler
  (syntax-parser
    [(_ handler
        (~optional (~seq #:tag tag) #:defaults ([tag #'default-tag]))
        body
        ...)
     #'(reset-at tag (parameterize ([current-effect-handler handler])
                       body ...))]))

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
        (let () (put initial) body ...)))
    (check-equal? (state 1 (get)) 1)
    (check-equal? (state 1 (put 2) (get)) 2)
    (check-equal? (state 1 (put 2) 3) 3)
    (check-equal? (state 0 (build-list 4 (thunk* (begin0 (get) (modify add1)))))
                  '(0 1 2 3)))
  (test-case "supply tag"
    (define tag (new-prompt-tag))
    (check-equal? (with-effect-handler (λ (v k) (k (add1 v)))
                    #:tag tag
                    (list (perform 1 #:tag tag)))
                  '(2)))
  #;; This fails because the handler doesn't know about tags. The inner perform use the inner handler
  (test-case "inner perform handled by outer handler via tags"
    (define tag-out (new-prompt-tag))
    (define tag-in (new-prompt-tag))
    (check-equal? (with-effect-handler (λ (v k) (k (add1 v)))
                    #:tag tag-out
                    (list (with-effect-handler (λ (v k) (error "boom"))
                            #:tag tag-in
                            (list (perform 1 #:tag tag-out)))))
                  '((2)))))
