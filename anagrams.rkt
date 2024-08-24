#lang racket

; bot for cheating at anagrams
(require "word-hunt.rkt")

(module+ main
  (main))

(define (main)
  (load-legal-words)
  (display "Enter the letters\n> ")
  (for ([anagram (anagrams (read-line))])
    (displayln anagram)))

; string -> (listof string)
(define (anagrams letters)
  (sort (for/list ([word (get-legal-words)]
                   #:when (anagram? word letters))
          word)
        < #:key string-length))

; a Count is a (hasheq char? Natural)

; string string -> boolean?
(define (anagram? word letters)
  (subcount? (count word) (count letters)))

; Count Count -> boolean?
(define (subcount? c1 c2)
  (for/and ([(k n) (in-hash c1)])
    (and (hash-has-key? c2 k)
         (<= n (hash-ref c2 k)))))

; String -> Count
(define (count s)
  (define cnt (make-hasheq))
  (for ([chr (string->list s)])
    (hash-set! cnt chr (add1 (hash-ref cnt chr -1))))
  cnt)
