#lang racket

; This module implements algebraic effects via delimited continuations.
; Unlike the original implementation, it does not use exceptions.

; it is like % and fcontrol, but when you resume, it wraps another % around E so  you can fcontrol more than once

;; module interface ;;

(module+ test (require rackunit))
(provide (struct-out exn:fail:algebraic-effects)
         (struct-out exn:fail:algebraic-effects:unhandled)
         (contract-out
          ; perform an effect. Like fcontrol
          [perform (->* (any/c) (#:tag continuation-prompt-tag?) any/c)])
         #;(with-effect-handler handler-proc [#:tag tag-expr] body ...)
         ; handles algebraic effects in the body
         ; where handler-proc is an EffectHandler (see data defs)
         ; Like %
         #|
         The reduction rules are (I'm pretty sure)
         (with-effect-handler proc val) => val
         (with-effect-handler proc E[(perform val)]) => (proc val (lambda (x) (with-effect-handler proc E[x])))
         ; where E has no with-effect-handler
         |#
         with-effect-handler
         ; wrapper for creating simple algebraic effects
         ; ex:
         #;
         (define-algebraic-effect math
           [(plus1 v k) (k (add1 v))]
           [(minus1 v k) (k (sub1 v))])
         ; usage:
         #;(equal? (math (list (plus1 2) (minus1 6))) '(3 5))
         define-algebraic-effect)

;; dependencies ;;

(require racket/control (for-syntax syntax/parse racket/syntax))

;; data definitions ;;

; custom error types
(struct exn:fail:algebraic-effects exn:fail () #:transparent)
(struct exn:fail:algebraic-effects:unhandled  exn:fail:algebraic-effects () #:transparent)
; Represents an unhandled algebraic effect.
; This exception is thrown when an effect is performed, but there is no handler in scope for it.

; An EffectHandler is a
#;(any/c continuation? -> any/c)
; Takes in an effect value and a continuation from which the ffect was performed,
; and handles it in some way.

;; functionality ;;

(define (new-prompt-tag) (make-continuation-prompt-tag (gensym 'algebraic-effects-prompt-tag)))

#;continuation-prompt-tag?
; the default prompt tag used for effect handling.
(define default-tag (new-prompt-tag))

#;(any/c any/c)
; Perform an effect with the specified value.
; Optionally takes in a prompt tag.
(define (perform value #:tag [tag default-tag])
  (fcontrol value #:tag tag))

(define-syntax with-effect-handler
  (syntax-parser
    [(_ handler
        (~optional (~seq #:tag tag) #:defaults ([tag #'default-tag]))
        body
        ...)
     #'(let ([handler-v handler])
         (define (proc v k)
           ; need to restore the handler before resuming
           ; need proc here, not handler-v. need the recursion
           (let ([k (λ (v) (% (k v) proc #:tag tag))])
             (handler-v v k)))
         (% (let () body ...)
            proc
            #:tag tag))]))

;; testing ;;
(module+ test
  (test-case "simple add1 effect"
    (check-equal? (with-effect-handler (λ (v k) (k (add1 v)))
                    (perform 1))
                  2))
  (test-case "abort"
    (define (product seq)
      (with-effect-handler (λ (v _) v)
        (for/fold ([acc 1])
                  ([elem seq])
          (if (zero? elem)
              (perform 0)
              (* acc elem)))))
    (check-equal? (product '(1 2 3 4)) 24)
    (check-equal? (product '(1 2 3 0 NaN)) 0)
    (define s (stream-cons 2 (stream-cons 0 s)))
    (check-equal? (product s) 0))
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
  ; generators
  (define gen-tag (make-continuation-prompt-tag 'generator-tag))
  (define (yield v) (perform v #:tag gen-tag))
  (define (yield* items) (for ([item items]) (yield item)))
  (define (gen-handler v k)
    (stream-cons v (k (void))))
  (define-syntax-rule (generator body ...) (with-effect-handler gen-handler #:tag gen-tag  body ... empty-stream))

  (test-case "generator"
        (check-equal? (stream->list (generator (yield 1)))
                  '(1))
    (check-equal? (stream->list (generator (yield 1) (yield 2)))
                  '(1 2)))
  (test-case "generator in a generator"
    (check-equal? (for/list ([e  (generator (yield 1) (yield* (generator (yield 2) (yield 3))))])
                    e)
                  '(1 2 3))
    (check-equal? (stream->list (generator (yield 1)
                                           (let ([inner (generator (yield 2) (yield 3))])
                                             (yield* inner))))
                  '(1 2 3)))
  ; state
  (define state-tag (make-continuation-prompt-tag 'state-tag))
  (define (get) (perform 'get #:tag state-tag))
  (define (put v) (perform (list 'put v) #:tag state-tag))
  (define (modify f) (put (f (get))))
  ; doesn't work with nested states but whatever
  (define current-state (make-parameter 'uninitialized-state))
  (define (state-handler v k)
    (match v
      ['get (k (current-state))]
      [(list 'put new-state)
       (parameterize ([current-state new-state]) (k (void)))]))
  (define-syntax-rule
    (state initial body ...)
    (with-effect-handler state-handler
      #:tag state-tag
      (let () (put initial) body ...)))

  (test-case "state"
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
  (test-case "inner perform handled by outer handler via tags"
    (define tag-out (new-prompt-tag))
    (define tag-in (new-prompt-tag))
    (check-equal? (with-effect-handler (λ (v k) (k (add1 v)))
                    #:tag tag-out
                    (list (with-effect-handler (λ (v k) (error "boom"))
                            #:tag tag-in
                            (list (perform 1 #:tag tag-out)))))
                  '((2))))
  (test-case "stateful generator"
    (check-equal? (stream->list (generator (yield 'start)
                                           (state 0
                                                  (yield (get))
                                                  (modify add1)
                                                  (yield (get)))
                                           (yield 'done)))
                  '(start 0 1 done))))

(define-syntax define-algebraic-effect
  (syntax-parser
    [(_ name:id
        (~optional (~seq #:body-wrapper body-wrapper) #:defaults ([body-wrapper #'(lambda (thnk) (thnk))]))
        [(effect-name:id v:id k:id)
         body ...]
        ...)
     (define/syntax-parse tag (format-id #'name "~a-tag" (syntax-e #'name)))
     #'(begin
         (define tag (make-continuation-prompt-tag 'tag))
         (define-syntax-rule (name body^ (... ...)) (proc (lambda () body^ (... ...))))
         (define (proc thnk) (with-effect-handler handler #:tag tag (body-wrapper thnk)))
         (define (handler v^ k^)
           (match v^
             [`(effect-name ,v) (let ([k k^]) body ...)]
             ...))
         (define (effect-name v^) (perform `(effect-name ,v^) #:tag tag))
         ...)]))

; TODO zero and multi-argument effects
; TODO better error message when no prompt available

(module+ test
  (let ()
    (define-algebraic-effect math
      [(plus1 v k) (k (add1 v))]
      [(minus1 v k) (k (sub1 v))])
    (check-equal? (math (list (plus1 2) (minus1 6)))
                  '(3 5)))
  (let ()
    (define-algebraic-effect generator
      #:body-wrapper (lambda (thnk) (thnk) empty-stream)
      [(yield v k) (stream-cons v (k (void)))])
    (check-equal? (stream->list (generator (yield 1) (yield 2)))
                  '(1 2))))
