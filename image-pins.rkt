#lang racket
(require pict)

#;
(pins bg
      [pin x1 y1 img1]
      [pin x2 y2 img2]
      [pin x3 y3 img3])
#;
(pin-over (pin-over (pin-over bg x1 y1 img1) x2 y2 img2) x3 y3 img3)

#;
(pins bg
      [pin x1 y1 img1]
      [define k 2]
      [pin k k img2])

;; macro for pinning a sequence of images on top of each other
(define-syntax (pins stx)
  (syntax-case stx (pin)
    [(_ bg (pin x y img) ...)
     #'(begin
         (define acc bg)
         (set! acc (pin-over acc x y img))
         ...
         acc)
     ]))

(define-syntax (pins- stx)
  (syntax-case stx (pin)
    [(_ bg stmt ...)
     #`(begin
         (define acc bg)
         (pins-help acc stmt)
         ...
         acc)]))

(define-syntax (pins-help stx)
  (syntax-case stx (pin)
    [(_ acc (pin x y img)) (set! acc (pin-over acc x y img))]
    [(_ acc stmt) stmt]))
#;
(pin-over (colorize (filled-rectangle 70 40) "chocolate")
            10 10
            (colorize (filled-rectangle 30 30) "orange"))
(pins (colorize (filled-rectangle 70 40) "chocolate")
      [pin 10 10 (colorize (filled-rectangle 30 30) "orange")])
