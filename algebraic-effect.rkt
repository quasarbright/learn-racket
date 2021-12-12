#lang racket

;; An implementation of algebraic effects using exceptions and continuations

(require racket/control)

(provide perform with-effect-handlers)

(module+ test (require rackunit))

#|

The two essential forms are `perform` and `with-effect-handlers`.
Example:
> (with-effect-handlers ([number? (λ (n resume-with) (resume-with (add1 n)))])
    (* 3 (perform 4)))
15

It's like an exception, but you can resume from it with a value.
However, it's more powerful than that.

You can also get non-determinism:
> (with-effect-handlers ([number? (λ (n resume-with) (list (resume-with (add1 n)) (resume-with (+ 2 n))))])
    (perform 1))
'(2 3)

Async:
> (touch (with-effect-handlers ([number? (λ (n resume-with) (future (thunk (resume-with (add1 n)))))])
           (perform 1)))
2

I don't think multiple performs and multiple resumes makes sense. If you have multiple performs,
thinking about the evaluation in terms of (resume-with v) returning the result of the resumed body
might not even make sense, since that will involve another handling. Which one should be the result
of the whole thing? It doesn't make sense.

Maybe it does make sense. calling resume-with in the handler runs the rest of the body with that value
filled in for the hole. This may include other performs. In that case, you'd end up coming back to the
handler, and resuming. So you have to consider how the code will come back to the handler. This control
flow is pretty confusing. It's kind of like foldr since the whole thing evaluates to the handling of the
first perform, but 

|#

;; Perform an algebraic effect
(define (perform eff)
  (shift k (raise (effect eff k))))

;; Handle algebraic effects
#;(with-effect-handlers ([number? (λ (n resume-with) (resume-with (add1 n)))])
    (* 3 (perform 4))) ; results in 15
(define-syntax-rule (with-effect-handlers ([pred handler] ...) body ...)
  (call-with-effect-handling (list pred ...) (list handler ...) (thunk body ...)))

;; A [Handler E] is a [E [Any -> Any] -> Any]
;; Represents an effect handler a user would write where E is the effect type
;; Example:
(define add1-resume (λ (n resume-with) (resume-with (add1 n)))) ; [Handler Number]

#; { [Listof [Any -> Boolean]] [Listof [Handler Any]] -> Any }
(define (call-with-effect-handling predicates handlers thnk)
  #; { [Effect Any] -> Any }
  ; Searches for a handler among the arguments and applies it if its predicate
  ; passes. Otherwise, re-raise the effect
  (define (main-handler e)
    (define eff (effect-eff e))
    (define resume-with (effect-cont e))
    ; find a handler whose predicate passes
    (define handler
      (for/or ([pred predicates]
               [handler handlers])
        (and (pred eff) handler)))
    (if handler
        ; TODO reset and recursive call. reset inside
        (handler eff (λ (v) (call-with-effect-handling predicates
                                   handlers
                                   (thunk (reset (resume-with v))))))
        ; none of the predicates passed
        (raise e)))
  (with-handlers ([effect? main-handler])
    (reset (thnk))))

(struct effect (eff cont) #:transparent)
;; An [Effect A] is an (effect A Continuation)
;; Interpretation: an (effect eff cont) represents a performed algebraic effect.
;; eff is the value passed to `perform`
;; cont is the continuation which, when applied to an argument `v`, resumes the computation at the
;; performance site with the `perform` form replaced by `v`

#; { (Any -> Boolean) -> (Any -> Boolean) }
;; Lifts a predicate on values to a predicate on effects containing those values
(define ((effect-predicate pred) e) (and (effect? e) (pred (effect-eff e))))

(module+ test
  (check-true ((effect-predicate number?) (effect 1 #f)))
  (check-false ((effect-predicate number?) (effect 'foo #f)))
  (check-false ((effect-predicate number?) 'foo)))


;; Test programs
(module+ test
  (test-equal? "simple perform"
               (with-effect-handlers ([number? (λ (n resume-with) (resume-with (add1 n)))])
                 (* 3 (perform 4)))
               15)
  (test-equal? "2 performs"
               (with-effect-handlers ([number? (λ (n resume-with) (resume-with (add1 n)))])
                 ; I think it loses the handler the second time around
                 (list (perform 1) (perform 4)))
               '(2 5))
  (test-exn "unhandled effect"
            effect?
            (thunk (with-effect-handlers ([number? (λ (n resume-with) (resume-with n))])
                     (perform 'foo))))
  (test-equal? "ignored effect"
               (with-effect-handlers ([number? (λ (n resume-with) 3)])
                 (+ 2 (perform 500)))
               3)
  (test-equal? "ignored, no perform"
               (with-effect-handlers ([number? (λ (n resume-with) 3)])
                 4)
               4)
  (test-equal? "call a function which performs"
               (let ([perform-five (thunk (perform 5))])
                 (with-effect-handlers ([number? (λ (n resume-with) (resume-with (add1 n)))])
                   (perform-five)))
               6)
  (test-equal? "non-determinism"
               (with-effect-handlers ([number? (λ (n resume-with) (list (resume-with (add1 n)) (resume-with (+ 2 n))))])
                 (perform 1))
               '(2 3))
  (test-equal? "non-determinism with two performs"
               (with-effect-handlers ([number? (λ (n resume-with) (list (resume-with (add1 n)) (resume-with (+ 2 n))))])
                 (list (perform 5) (perform 1)))
               '(((6 2) (6 3))
                 ((7 2) (7 3))))
  (test-equal? "async"
               (touch (with-effect-handlers ([number? (λ (n resume-with) (future (thunk (resume-with (add1 n)))))])
                        (perform 1)))
               2))
