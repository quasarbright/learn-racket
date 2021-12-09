#lang racket

;; An attempt at implementing algebraic effects using exceptions and continuations

(provide perform with-effect-handlers)

(module+ test (require rackunit))

;; An effect, which contains the performed effect eff and the continuation to resume to
(struct effect (eff cont))

#; { (Any -> Boolean) -> (Any -> Boolean) }
;; Lifts a predicate on values to a predicate on effects containing those values
(define ((effect-predicate pred) e) (and (effect? e) (pred (effect-eff e))))

(module+ test
  (check-true ((effect-predicate number?) (effect 1 #f)))
  (check-false ((effect-predicate number?) (effect 'foo #f)))
  (check-false ((effect-predicate number?) 'foo)))

;; Perform an algebraic effect
(define-syntax-rule (perform eff)
  (let/cc k (raise (effect eff k))))

;; Handle algebraic effects
#;(with-effect-handlers ([number? (λ (n resume-with) (resume-with (add1 n)))])
    (* 3 (perform 4))) ; results in 5
(define-syntax-rule (with-effect-handlers ([pred handler] ...) body ...)
  (with-handlers ([(effect-predicate pred) (λ (e) (handler (effect-eff e) (effect-cont e)))]
                  ...)
    body ...))

(module+ test
  (check-equal? (with-effect-handlers ([number? (λ (n resume-with) (resume-with (add1 n)))])
                  (* 3 (perform 4)))
                15))

;; Problem: you can't do non-determinism
;; Ex:
#;(with-effect-handlers ([number? (λ (n resume-with) (list (resume-with (add1 n)) (resume-with (+ 2 n))))])
    1)
;; Want that to be (list 2 3)
;; You might want some other control operators, maybe reset shift???
;; With shift, you can call k multiple times
