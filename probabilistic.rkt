#lang racket

;; A probabilistic programming language implemented with algebraic effects
;; Provides naive sampling and enumeration implementations

(require racket/hash
         "algebraic-effect-2.rkt")
(module+ test (require rackunit))
(provide
 ;;; probabilistic block

 ;; runs every possible path of the program.
 ;; produces an exact distribution
 prob/enumeration
 ;; runs the program a bunch of times, randomly sampling at choice points.
 ;; produces an inexact distribution
 prob/sampling

 ;;; probabilistic operators (these "fork" the program)

 ;; [Real] -> Boolean
 ;; Random boolean, optionally weighted
 flip
 ;; A ... -> A
 ;; uniform random choice
 choice
 ;; (hash A Real) -> A
 ;; weighted random choice. Input should be a legal probability distribution
 ;; (probabilities are in [0,1] and sum to 1)
 weighted-choice
 ;; Any -> Void
 ;; kill this "branch" of the program if the condition is false
 assert
 ;; kill this "branch" of the program
 abort)

;;; Data Definitions

;; A Probability is a Real in [0,1]

;; A (DiscreteDistribution A), or (DD A) is a (Hash A Probability)
;; Represents a discrete probability distribution.
;; CONSTRAINT: values must add to 1


;; An Effect is a (DD A) representing a random choice from the distribution.

;; Binary choice, optionally weighted
;; [Probability] -> Boolean
(define (flip [p 1/2])
  (perform (hash #t p
                 #f (- 1 p))))

;; A ... -> A
;; Uniform choice from provided arguments
(define (choice . vs)
  (define N (length vs))
  (define 1/N (/ N))
  (perform (for/hash ([v vs])
             (values v 1/N))))

;; (DD A) -> A
;; Weighted choice from provided distribution
(define (weighted-choice dd)
  (perform dd))

;; Any -> Void
;; Kills this branch of the program if the condition is false
(define (assert b)
  (unless b (abort)))



;; -> Void
;; Kill this branch of the program
(define (abort)
  (perform (hash)))

;; Run program probabilistically, using enumeration. Evaluates to a distribution over program results
(define-syntax-rule (prob/enumeration body ...)
  (with-effect-handler enumeration-handler
    (hash (let ()
            body ...)
          1)))

;; (DD Hole) (Hole -> (DD Result)) -> (DD Result)
;; Follows every possible path of execution and accumulates a probability distribution on results
(define (enumeration-handler dd k)
  (dd-join
   (for/hash ([(v p) (in-hash dd)])
     (values (k v) p))))

;; (DD (DD A)) -> (DD A)
;; Converts a probability distribution of probability distributions to a single probability distribution.
;; Like a weighted sum
(define (dd-join ddd)
  (for/fold ([dd-joined (hash)])
            ([(dd p) ddd])
    (dd-add dd-joined (dd-scale dd p))))

;; (DD A) (DD A) -> (DD A)
;; adds two distributions without normalization.
;; may lead to invalid distributions if used improperly
(define (dd-add dd1 dd2)
  (hash-union dd1 dd2 #:combine +))

;; (DD A) Real -> (DD A)
;; scales a probability distribution
(define (dd-scale dd x)
  (for/hash ([(v p) (in-hash dd)])
    (values v (* x p))))

(define NUM_SAMPLES 100) ; TODO optional kwarg
(define-syntax-rule (prob/sampling body ...)
  (with-effect-handler sampling-handler
    (define counts
      (for/fold ([dd (hash)])
                ([_ (in-range NUM_SAMPLES)])
        (define result
          (let () body ...))
        (hash-set dd result (+ 1 (hash-ref dd result 0)))))
    (for/hash ([(v count) (in-hash counts)])
      (values v (/ count NUM_SAMPLES)))))

;; (DD Hole) (Hole -> (DD Result)) -> (DD Result)
;; Runs the program a bunch of times, randomly sampling
(define (sampling-handler dd k)
  (k (dd-sample dd)))

;; (DD A) -> A
;; Sample from the distribution (non-effectful)
(define (dd-sample dd)
  (define rand (random))
  (define sum 0)
  ; the first v that puts the rolling sum over rand
  (for/or ([(v p) (in-hash dd)])
    (set! sum (+ sum p))
    (and (> sum rand) v)))

(module+ test
  (check-equal? (prob/enumeration 'foo)
                (hash 'foo 1))
  (check-equal? (prob/enumeration (flip))
                (hash #t 1/2
                      #f 1/2))
  (check-equal? (prob/enumeration (choice 'a 'b 'c))
                (hash 'a 1/3
                      'b 1/3
                      'c 1/3))
  (check-equal? (prob/enumeration (and (flip) (flip)))
                (hash #t 1/4
                      #f 3/4))
  (check-equal? (prob/sampling 'foo)
                (hash 'foo 1))
  (check-within (prob/sampling (flip))
                (hash #t 1/2
                      #f 1/2)
                0.1)
  (check-within (prob/sampling (and (flip) (flip)))
                (hash #t 1/4
                      #f 3/4)
                0.1))
