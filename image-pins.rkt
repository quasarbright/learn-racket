#lang racket
(require pict)

;; macro for pinning a sequence of images on top of each other.
;; example usage:
#;
(pins (colorize (filled-rectangle 70 40) "chocolate")
      (define x 10)
      (define y 10)
      (pin x y (colorize (filled-rectangle 30 30) "orange"))
      (pin 20 20 (colorize (disk 10) "white")))
(define-syntax (pins stx)
  (syntax-case stx (pin)
    [(_ bg stmt ...)
     #'(begin
         (define acc bg)
         (pins-stmt acc stmt)
         ...
         acc)]))

;; helper macro which runs a pins statement, which is a
;; (pin x y img) or
;; <expr>
(define-syntax (pins-stmt stx)
  (syntax-case stx (pin)
    [(_ acc (pin x y img)) #'(set! acc (pin-over acc x y img))]
    [(_ acc stmt) #'stmt]))

(pins (colorize (filled-rectangle 70 40) "chocolate")
      (define x 10)
      (define y 10)
      (pin x y (colorize (filled-rectangle 30 30) "orange"))
      (pin 20 20 (colorize (disk 10) "white")))
