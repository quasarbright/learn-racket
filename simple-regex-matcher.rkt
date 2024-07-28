#lang racket

; simplest regular expression matcher I could think of.
; no state machine, no derivatives, no call/cc.
; does not perform backtracking, so the pattern /a*a/ does not match "aaa" even though it should.

(provide (struct-out repeat)
         (struct-out seq)
         (struct-out alt)
         match?)

; a Regexp represents a pattern of text.
; a Regexp is one of
; a String
; matches the exact text of the string.
(struct repeat [re] #:transparent)
; matches 0 or more repetitions of re
(struct seq [re1 re2] #:transparent)
; matches strings that match re1 then re2
(struct alt [re1 re2] #:transparent)
; matches strings that match re1 or re2

(struct stream [text index] #:transparent)
; represents an input stream
; text is a String
; index is a Natural representing the index into the string

; Regex String -> Boolean
; does the regex match the whole text string? (not just a prefix)
(define (match? re text)
  (define strm (do-match re (stream text 0)))
  ; check that there is no text left to make sure this is a full match
  (and strm (stream-empty? strm)))

(module+ test
  (require rackunit)
  (check-true (match? "" ""))
  (check-false (match? "" "a"))
  (check-true (match? "foo" "foo"))
  (check-false (match? "foo" "fo"))
  (check-false (match? "foo" "foobar"))
  (check-true (match? (alt "a" "b")
                      "a"))
  (check-true (match? (alt "a" "b")
                      "b"))
  (check-false (match? (alt "a" "b")
                       "c"))
  (check-true (match? (repeat "a") ""))
  (check-true (match? (repeat "a") "a"))
  (check-true (match? (repeat "a") "aa"))
  (check-true (match? (repeat "a") "aaaaaaaaa"))
  (check-false (match? (repeat "a") "aaaaaaaaab"))
  (check-false (match? (repeat "a") "b"))
  (check-true (match? (seq (repeat "a") "b")
                      "b"))
  (check-true (match? (seq (repeat "a") "b")
                      "aaab"))
  ; backtracking (these tests fail because we don't do backtracking)
  #;(check-true (match? (seq (repeat "a") "a") "a"))
  #;(check-true (match? (seq (repeat "a") "a") "aa"))
  #;(check-true (match? (seq (repeat "a") "a") "aaa"))
  #;(check-true (match? (seq (repeat "a") "a") "aaaaa"))
  (check-false (match? (seq (repeat "a") "a")
                       "")))

; Regex Stream -> (Union #f Stream)
; try to match re on the current part of the input stream s.
; returns the resulting stream, advanced to after the matched text, on success.
; retrurns #f on failure.
(define (do-match re s)
  (match re
    [(? string?)
     (match s
       [(stream text index)
        (define index^ (+ index (string-length re)))
        (and (<= index^ (string-length text))
             (string=? re (substring text index index^))
             (stream text index^))])]
    [(seq re1 re2)
     (define s^ (do-match re1 s))
     (and s^ (do-match re2 s^))]
    [(alt re1 re2)
     (or (do-match re1 s)
         (do-match re2 s))]
    [(repeat re)
     (define s^ (do-match re s))
     (if s^
         (do-match (repeat re) s^)
         ; if re didn't match, the repetition matches 0 occurrences
         s)]))

; Stream -> Boolean
; Does the input stream not have any text left?
(define (stream-empty? s)
  (>= (stream-index s)
      (string-length (stream-text s))))
