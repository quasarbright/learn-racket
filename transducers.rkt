#lang racket

;; step : X R -> R



;; mapping : (A -> B) -> (B R -> R) -> (A R -> R)
;; interesting. There is a contravariant twist
;; I wonder how this affects composition
(define (mapping f)
  (lambda (step)
    (lambda (x r) (step (f x) r))))

;; filtering : (X -> Boolean) -> (A R -> R) -> (A R -> R)
(define (filtering p)
  (lambda (step)
    (lambda (x r) (if (p x) (step x r) r))))

#;
(define catting
  (lambda (step)
    (lambda (x r) ???)))



(define keeping-short-numbers
  (compose ))

(define (transducer/c x a y b) (-> (-> x a a) (-> y b b)))
;; transduces a step on xs that produces an a
;; to a step on ys that produces a b
;; a transducer is just a step transformer, for a reduction step
;; which is a function you pass to a sequence-fold

(define reduce sequence-fold)

(define (mapping-then-filtering f p)
  (compose (filtering p) (mapping f)))

