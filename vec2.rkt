#lang racket

(module+ test (require rackunit))
(provide
 (struct-out vec2)
 (contract-out
  [vec2+ (->* () () #:rest (listof vec2?) vec2?)]
  [vec2-scale (-> vec2? number? vec2?)]
  [vec2-rotate-90 (-> vec2? vec2?)]
  [vec2-dist (-> vec2? vec2? number?)]
  [vec2-magnitude (-> vec2? number?)]
  [vec2- (->* (vec2?) () #:rest (listof vec2?) vec2?)]
  ; linear interpolate. 0 yields v1, 1 yields v2.
  [vec2-lerp (-> vec2? vec2? number? vec2?)]
  [vec2-dot (-> vec2? vec2? number?)]))

; 2D vectors

; A Vec2 is a
(struct vec2 [x y] #:transparent)
; x and y are Numbers

; Vec2 ... -> Vec2
(define (vec2+ . vs)
  (for/fold ([sum (vec2 0 0)])
            ([v vs])
    (vec2-pointwise + sum v)))

; (Number Number -> Number) Vec2 Vec2 -> Vec2
(define (vec2-pointwise f v1 v2)
  (match (list v1 v2)
    [(list (vec2 x1 y1) (vec2 x2 y2))
     (vec2 (f x1 x2)
           (f y1 y2))]))

; Vec2 Number -> Vec2
(define (vec2-scale v k)
  (match v
    [(vec2 x y) (vec2 (* k x) (* k y))]))

; Vec2 -> Vec2
; Rotate by 90 degrees counter-clockwise
(define (vec2-rotate-90 v)
  (match v
    [(vec2 x y) (vec2 (- y) x)]))

; Vec2 Vec2 -> Number
(define (vec2-dist v1 v2)
  (vec2-magnitude (vec2- v1 v2)))

; Vec2 -> Number
(define (vec2-magnitude v)
  (match v
    [(vec2 x y)
     (sqrt (+ (sqr x) (sqr y)))]))

; Vec2 Vec2 ... -> Vec2
(define (vec2- v . vs)
  (if (null? vs)
      (vec2-scale v -1)
      (apply vec2+ v (for/list ([v vs])
                       (vec2-scale v -1)))))

; Vec2 Vec2 Number -> Vec2
; linear interpolate where 0 yields v1, 1 yields v2
(define (vec2-lerp v1 v2 r)
  ; v1 + r (v2 - v1)
  (vec2+ v1
         (vec2-scale (vec2- v2 v1)
                     r)))

; Vec2 Vec2 -> Number
(define (vec2-dot v1 v2)
  (match (list v1 v2)
    [(list (vec2 x1 y1)
           (vec2 x2 y2))
     (+ (* x1 x2) (* y1 y2))]))
