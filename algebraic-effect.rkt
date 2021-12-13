#lang racket

;; An implementation of algebraic effects using exceptions and continuations

(require racket/control)

(provide perform with-effect-handlers)

(module+ test (require rackunit))

#|
Algebraic effects:

It's like an exception, but you can resume from it with a value.
However, it's more powerful than that.
You have first-class access to the `resume-with` function, which opens up many possibilities.

The two essential forms are `perform` and `with-effect-handlers`.
Example:
> (with-effect-handlers ([number? (λ (n resume-with) (resume-with (add1 n)))])
    (* 3 (perform 4)))
15

You can also get non-determinism:
> (with-effect-handlers ([number? (λ (n resume-with) (list (resume-with (add1 n)) (resume-with (+ 2 n))))])
    (perform 1))
'(2 3)

Async:
> (touch (with-effect-handlers ([number? (λ (n resume-with) (future (thunk (resume-with (add1 n)))))])
           (perform 1)))
2

Generators:
> (with-effect-handlers ([(const #t) (λ (v resume-with) (cons v (resume-with (void))))])
    (perform 1)
    (perform 2)
    (if #t
        (perform 3)
        (perform 'foo))
    (perform 4)
    '())
'(1 2 3 4))

Here is a rough description of the semantics:
(with-effect-handlers ([pred (λ (v resume-with) handle-expr)])
  body-expr)
Assume there is not another with-handlers in body-expr
If a `(perform v)` is evaluated in the body, and `(pred v)` is true,
the entire computation evaluates to applying the handler to `v` and `resume-with`.
`resume-with` is a continuation that, when called `(resume-with u)`, will resume
computation in the body with the `(perform v)` replaced by `u`.
If there is no `(perform v)` in body-expr, the entire computation evaluates to the result of body-expr.
In the case of multiple handlers on the same level, the first one with a passing predicate is used.
If an effect is performed and no handler predicates pass, the effect is handled by an outer handler, if
one exists. If one doesn't exist, an exn:fail:algebraic-effects:unhandled is raised. This behavior
is similar to exceptions and `with-handlers`.

Things get tricky when you deal with multiple performs in the body.
You have to keep in mind that resuming will involve returning to your handler upon subsequent effects.
This makes it like writing a recursive function, and it's tricky to think about. The control flow is confusing.

The async example would be tricky with multiple performs. Resuming might result in a future, and it might result in
the final answer. You'd have to handle both cases in the handler. And what if the body results in a future? Would you
do some sort of tagging to distinguish? Sounds like a monad. I could automate the tagging in the library though.
|#

;; Perform an algebraic effect
(define (perform eff)
  (if (continuation-prompt-available? algebraic-effects-prompt-tag)
      (control-at algebraic-effects-prompt-tag k (raise (effect eff k)))
      (raise (exn:fail:algebraic-effects:unhandled (format "Unhandled effect: ~v" eff) (current-continuation-marks)))))

;; Handle algebraic effects
#;(with-effect-handlers ([number? (λ (n resume-with) (resume-with (add1 n)))])
    (* 3 (perform 4))) ; results in 15
(define-syntax-rule (with-effect-handlers ([pred handler] ...) body ...)
  (call-with-effect-handling (list pred ...) (list handler ...) (thunk body ...)))

;; A [Handler E] is a [E [Any -> Any] -> Any]
;; Represents an effect handler a user would write where E is the effect type
;; Example:
#; [Handler Number]
(define add1-resume (λ (n resume-with) (resume-with (add1 n))))

#; [Handler Any]
; Just resumes with the result of performing the effect. This allows
; passthrough to an outer handler, but retains this handler.
(define re-perform-handler (λ (e resume-with) (resume-with (perform e))))

#; { [Listof [Any -> Boolean]] [Listof [Handler Any]] -> Any }
(define (call-with-effect-handling predicates handlers thnk)
  #; { [Effect Any] -> Any }
  ; Searches for a Handler among the `handlers` and applies it if its predicate
  ; passes. Otherwise, re-perform the effect.
  ; This is an "exception" handler, not an "effect" handler like a user would write.
  ; This strangeness is a result of using `raise` to raise an effect struct.
  (define (exception-handler e)
    (define eff (effect-eff e))
    (define resume-with (effect-cont e))
    ; find a handler whose predicate passes
    (define maybe-handler
      (for/or ([pred predicates]
               [handler handlers])
        (and (pred eff) handler)))
    (define handler (or maybe-handler re-perform-handler))
    ; we need this recursive call to re-delimit the continuation upon resuming
    (handler eff (λ (v) (call-with-effect-handling predicates
                                                   handlers
                                                   (thunk (prompt-at algebraic-effects-prompt-tag (resume-with v)))))))
  (with-handlers ([effect? exception-handler])
    (prompt-at algebraic-effects-prompt-tag (thnk))))

(struct effect (eff cont) #:transparent)
;; An [Effect A] is an (effect A Continuation)
;; Interpretation: an (effect eff cont) represents a performed algebraic effect.
;; eff is the value passed to `perform`
;; cont is the continuation which, when applied to an argument `v`, resumes the computation at the
;; performance site with the `perform` form replaced by `v`

(struct exn:fail:algebraic-effects exn:fail () #:transparent)
(struct exn:fail:algebraic-effects:unhandled  exn:fail:algebraic-effects () #:transparent)

#; { (Any -> Boolean) -> (Any -> Boolean) }
;; Lifts a predicate on values to a predicate on effects containing those values
(define ((effect-predicate pred) e) (and (effect? e) (pred (effect-eff e))))

(module+ test
  (check-true ((effect-predicate number?) (effect 1 #f)))
  (check-false ((effect-predicate number?) (effect 'foo #f)))
  (check-false ((effect-predicate number?) 'foo)))

; a custom prompt tag used to avoid collision with user reset shifts
(define algebraic-effects-prompt-tag (make-continuation-prompt-tag 'algebraic-effects-prompt-tag))


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
            exn:fail:algebraic-effects:unhandled?
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
               2)
  (test-equal? "can use reset shift in body"
               (with-effect-handlers ([number? (λ (n resume-with) (resume-with (add1 n)))])
                 (reset (+ 3 (shift k (perform 1)))))
               2)
  (test-equal? "can use prompt control in body"
               (with-effect-handlers ([number? (λ (n resume-with) (resume-with (add1 n)))])
                 (prompt (+ 3 (shift k (k (k (perform 1)))))))
               8)
  (test-equal? "can use reset shift around the whole computation"
               (reset (+ 99 (with-effect-handlers ([number? (λ (n resume-with) (resume-with (add1 n)))])
                              (shift k 1))))
               1)
  (test-equal? "can use reset control around the whole computation"
               (reset (+ 99 (with-effect-handlers ([number? (λ (n resume-with) (resume-with (add1 n)))])
                              (control k 1))))
               1)
  (test-equal? "use escaped resume-with"
               (let-values ([(n resume-with) (with-effect-handlers ([number? values])
                                               (* 3 (perform 4)))])
                 (resume-with (add1 n)))
               15)
  (test-equal? "use escaped resume-with twice"
               (let-values ([(n resume-with) (with-effect-handlers ([number? values])
                                               (* 3 (perform 4)))])
                 (+ (resume-with (sub1 n)) (resume-with (add1 n))))
               24)
  (test-equal? "re-perform effect without inner resume"
               (with-effect-handlers ([number? (λ (n resume-with) (resume-with (add1 n)))])
                 (with-effect-handlers ([number? (λ (n resume-with) (perform (add1 n)))])
                   (* 2 (perform 3))))
               5)
  (test-equal? "re-perform effect with inner resume"
               (with-effect-handlers ([number? (λ (n resume-with) (resume-with (add1 n)))])
                 (with-effect-handlers ([number? (λ (n resume-with) (resume-with (perform (add1 n))))])
                   (* 2 (perform 3))))
               10)
  (test-equal? "effect pass-through"
               (with-effect-handlers ([number? (λ (n resume-with) (resume-with (add1 n)))])
                 (with-effect-handlers ([symbol? (λ (s resume-with) (resume-with s))])
                   (* 2 (perform 4))))
               10)
  (test-equal? "nested perform"
               (with-effect-handlers ([number? add1-resume])
                 (perform (perform 1)))
               3)
  (test-case "escaped resume-with retains handlers"
             (define-values (n resume-with) (with-effect-handlers ([number? values])
                                              (* (perform 3) (perform 4))))
             (define-values (n2 resume-with2) (resume-with 2))
             (define result (resume-with2 5))
             (check-equal? (list n n2 result) (list 3 4 10)))
  (test-equal? "handlers are retained after effect pass-through"
               (with-effect-handlers ([number? (λ (n resume-with) (resume-with (add1 n)))])
                 (with-effect-handlers ([symbol? (λ (s resume-with) (resume-with s))])
                   (list (perform 2) (perform 'foo))))
               (list 3 'foo))
  (test-equal? "handlers are retained after re-performing"
               (with-effect-handlers ([number? (λ (n resume-with) (resume-with (add1 n)))])
                 (with-effect-handlers ([number? (λ (n resume-with) (resume-with (perform (add1 n))))])
                   (list (perform 2) (perform 9))))
               (list 4 11))
  (test-equal? "generator"
               (with-effect-handlers ([(const #t) (λ (v resume-with) (cons v (resume-with (void))))])
                 (perform 1)
                 (perform 2)
                 (if #t
                     (perform 3)
                     (perform 'foo))
                 (perform 4)
                 '())
               '(1 2 3 4))
  ; I thought this would fail, but you control with raise,
  ; so the prompt is replaced with the raise, which aborts the body
  (test-equal? "users can't catch effects"
               (with-effect-handlers ([number? add1-resume])
                 (with-handlers ([(const #t) (const 'oopsie)])
                   (perform 3)))
               4)
  (test-exn "exceptions propagate through the effect handler"
            exn:fail?
            (thunk (with-effect-handlers ([number? add1-resume])
                     (error "poof"))))
  (test-exn "exceptions propagate through effect handler after perform"
            exn:fail?
            (thunk (with-effect-handlers ([number? add1-resume])
                     (+ (perform 1) (error "uh oh"))))))
