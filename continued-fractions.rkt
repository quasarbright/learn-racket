#lang racket

(module+ test
  (require rackunit))

; exploring continued fractions
; https://en.wikipedia.org/wiki/Continued_fraction

; A ContinuedFraction (CF) is a (stream Integer Natural ...)
; Where the first element is the "shallowest"
; Example:
; represents 7/3 = 2 + 1/3
(define cf-7/3 (stream 2 3))
; first can be zero
(define cf-1/2 (stream 0 2))
(define cf-1 (stream 1))
; first can be negative
(define cf--1/2 (stream -1 2))
(define cf-415/93 (stream 4 2 6 7))
(define cf-phi (stream-cons 1 cf-phi))
#;(stream->list (stream-take (cf->numbers cf-phi) 10))
#;'(1 2 3/2 5/3 8/5 13/8 21/13 34/21 55/34 89/55)
; so cool

; CF -> (streamof Rational)
(define (cf->numbers cf)
  ; each iteration is O(1) time
  ; https://en.wikipedia.org/wiki/Continued_fraction#Infinite_continued_fractions_and_convergents
  ; loop generates both h and k sequences depending on the initial values
  (define (loop h_n-2 h_n-1 cf)
    (if (stream-empty? cf)
        (stream)
        (let* ([a_n (stream-first cf)]
               ; this is why (cf->numbrs cf-phi) produces 3/2 5/3 8/5 ...
               [h_n (+ (* a_n h_n-1) h_n-2)])
          (stream-cons h_n
                       (loop h_n-1 h_n (stream-rest cf))))))
  (define numerators (loop 0 1 cf))
  (define denominators (loop 1 0 cf))
  (for/stream ([numerator (in-stream numerators)]
               [denominator (in-stream denominators)])
    (/ numerator denominator)))

(module+ test
  (check-equal? (sequence->list (cf->numbers cf-1))
                '(1))
  (check-equal? (sequence->list (cf->numbers cf-1/2))
                '(0 1/2))
  (check-equal? (sequence->list (cf->numbers cf-7/3))
                '(2 7/3)))

(define (cf->number cf [max-iter #f])
  (if max-iter
      (for/last ([v (in-stream (cf->numbers cf))]
                 [_ (in-range max-iter)])
        v)
      (for/last ([v (in-stream (cf->numbers cf))]) v)))

(module+ test
  (check-equal? (cf->number cf-1/2) 1/2)
  (check-equal? (cf->number cf-415/93) 415/93)
  (define PHI (/ (+ 1 (sqrt 5))
                   2))
  (check-within (cf->number cf-phi 15)
                PHI
                .01))

; Real -> CF
(define (number->cf x)
  (if (integer? x)
      (stream x)
      (stream-cons (floor x)
                   (number->cf (/ (- x (floor x)))))))

(module+ test
  (check-equal? (sequence->list (number->cf 1))
                '(1))
  (check-equal? (sequence->list (number->cf 7/3))
                '(2 3))
  (check-equal? (sequence->list (number->cf 415/93))
                '(4 2 6 7))
  (check-equal? (sequence->list (stream-take (number->cf PHI) 5))
                '(1.0 1.0 1.0 1.0 1.0)))
