#lang racket

(module+ test (require rackunit))
(require racket/match racket/hash)
(provide load-legal-words get-legal-words)
(module+ main
  (main))

; a bot to help me cheat at word hunt

#|
Idea:
Take a dictionary of words. Form a prefix tree.
Try every path from every letter using BFS, only allowing moves that follow the prefix tree.
This will get all playable words. Then sort by length in reverse and display.
Ingest game board as a 16-length string.
Output words as-is, maybe with starting coordinates. Ideally, show path along game board.
Start out simple, then UI. Maybe port to js.
|#

(define DICTIONARY_PATH "/Users/mdelmonaco/Downloads/Collins Scrabble Words (2019).txt")
(define BOARD_SIZE 4)
; A Board is a 4x4 2D vector of characters
; Example
(define example-board
  #(#(#\o #\a #\t #\r)
    #(#\i #\h #\p #\s)
    #(#\h #\t #\n #\r)
    #(#\e #\n #\e #\i)))

; An Index is a
(struct index [row col] #:transparent)
; Representing a location on a Board

; A WordTree is a (hasheq Char WordTree)
; Represents a prefix tree of words.
; Example:
(define small-word-tree
  ; foo bar baz
  (hasheq #\f (hasheq #\o (hasheq #\o (hasheq)))
          #\b (hasheq #\a (hasheq #\r (hasheq)
                                  #\z (hasheq)))))

(define BOARD_INPUT_PAT #px"^([a-z][a-z][a-z][a-z])\\s*([a-z][a-z][a-z][a-z])\\s*([a-z][a-z][a-z][a-z])\\s*([a-z][a-z][a-z][a-z])$")

(define should-log? (make-parameter #t))
(define (logln s)
  (when (should-log?)
    (displayln s)))
(define (log s)
  (when (should-log?)
    (display s)))

(define (main)
  (define legal-word-tree (get-legal-word-tree))
  (define legal-word-set (get-legal-word-set))
  (log "input game board. rows can be separated by spaces, but must be on the same line.\n> ")
  (define line (read-line))
  (unless (regexp-match? BOARD_INPUT_PAT line)
    (raise-user-error "Invalid input. Please input 16 lowercase alphabetic characters"))
  (define board (string->board line))
  (logln "solving")
  (define words (solve board legal-word-tree legal-word-set))
  (logln "solved")
  (logln "words: \n")
  (for ([word (sort (remove-duplicates words) < #:key string-length)])
    (displayln word)))

(define (test s)
  (define out (open-output-string))
  (parameterize ([current-input-port (open-input-string s)]
                 [current-output-port out]
                 [should-log? #f])
    (main))
  (string-split (get-output-string out)
                "\n"))

; String -> Board
; Assume string is 16 lowercase alphabetic characters.
(define (string->board s)
  (match-define (list _ lines ...) (regexp-match BOARD_INPUT_PAT s))
  (list->vector (map (compose list->vector string->list) lines)))

(module+ test
  (check-equal? (string->board "oatrihpshtnrenei")
                example-board))
; -> WordTree
(define (get-legal-word-tree)
  (define legal-words (get-legal-words))
  (logln "building prefix tree")
  (begin0
      (words->word-tree legal-words)
    (logln "built prefix tree")))

; -> (Set String)
(define (get-legal-word-set)
  (define legal-words (get-legal-words))
  (list->set legal-words))

; -> (Listof String)
(define legal-words-promise
  (delay
    (logln "reading dictionary")
    (begin0 (for/list ([line (file->lines DICTIONARY_PATH)]
                       #:unless (= 0 (string-length line)))
              (string-downcase line))
      (logln "read dictionary"))))
(define (get-legal-words)
  (force legal-words-promise))
; -> Void
(define (load-legal-words)
  (get-legal-words)
  (void))

; (Listof string) -> WordTree
(define (words->word-tree words)
  ; invariant: words only has words with length > index, and common prefixes up to and excluding index
  (let loop ([words words]
             [index 0])
    (define groups (groupby words (lambda (word) (string-ref word index))))
    (for/hasheq ([(char words) (in-hash groups)])
      (define index^ (add1 index))
      (define words^
        (for/list ([word words]
                   #:when (> (string-length word) index^))
          word))
      (values char (loop words^ index^)))))

(module+ test
  (check-equal? (words->word-tree '("foo" "bar" "baz"))
                small-word-tree)
  (check-equal? (words->word-tree '("a" "aa" "aaa"))
                (hasheq #\a (hasheq #\a (hasheq #\a (hasheq))))))

; (Listof T) (T -> S) -> (hasheq S (listof T))
(define (groupby lst proc)
  (define result (make-hasheq))
  (for ([v lst])
    (define k (proc v))
    (hash-set! result k (cons v (hash-ref result k (list)))))
  result
  #;(apply hash-union
         (hasheq)
         (for/list ([v lst])
           (hasheq (proc v) (list v)))
         #:combine append))

(module+ test
  (check-equal? (groupby '(1 2 3 4) (lambda (n) (modulo n 2)))
                (make-hasheq (list (cons 0 '(4 2)) (cons 1 '(3 1))))))

; Board WordTree (Set String) -> (Listof String)
; Find all playable words.
(define (solve board word-tree word-set)
  (define indices (board-indices))
  (apply append
         (for/list ([index indices])
           (solve/index board index word-tree word-set))))

; -> (Listof Index)
(define (board-indices)
  (for*/list ([row (in-range BOARD_SIZE)]
              [col (in-range BOARD_SIZE)])
    (index row col)))

; Find all playable words starting at index
(define (solve/index board idx word-tree word-set)
  ; dfs
  (define words (list))
  (let loop ([idx idx]
             [path (list idx)]
             [tree (hash-ref word-tree (board-get board idx) (hasheq))])
    (define word (board-indices->word board (reverse path)))
    (when (set-member? word-set word)
      (set! words (cons word words)))
    (for ([idx^ (get-neighboring-indices idx)]
          #:when (hash-has-key? tree (board-get board idx^))
          #:unless (member idx^ path))
      (loop idx^ (cons idx^ path) (hash-ref tree (board-get board idx^)))))
  words)

(module+ test
  (check-equal? (solve/index (string->board "foox barx xxzx xxxx") (index 0 0) small-word-tree (set "foo" "bar" "baz"))
                (list "foo"))
  (check-equal? (solve/index (string->board "foox barx xxzx xxxx") (index 1 0) small-word-tree (set "foo" "bar" "baz"))
                (list "baz" "bar")))

; Board Index -> Char
(define (board-get board idx)
  (vector-ref (vector-ref board (index-row idx))
              (index-col idx)))

; Board (Listof Index) -> String
(define (board-indices->word board indices)
  (apply string
         (for/list ([idx indices])
           (board-get board idx))))

; Index -> (Listof Index)
; In-bounds neighbors including diagonals
(define (get-neighboring-indices idx)
  (match-define (index r c) idx)
  (for*/list ([dr (in-range -1 2)]
              [dc (in-range -1 2)]
              #:unless (equal? (list dr dc) '(0 0))
              #:unless (or (< (+ r dr) 0)
                           (< (+ c dc) 0)
                           (>= (+ r dr) BOARD_SIZE)
                           (>= (+ c dc) BOARD_SIZE)))
    (index (+ r dr) (+ c dc))))

(module+ test
  (check-equal? (get-neighboring-indices (index 0 0))
                (list             (index 0 1)
                      (index 1 0) (index 1 1)))
  (check-equal? (get-neighboring-indices (index 1 1))
                (list (index 0 0) (index 0 1) (index 0 2)
                      (index 1 0)             (index 1 2)
                      (index 2 0) (index 2 1) (index 2 2)))
  (check-equal? (get-neighboring-indices (index 3 3))
                (list (index 2 2) (index 2 3)
                      (index 3 2))))

(module+ test
  (check-not-false (member "high" (test "memi legh dail ayoh")))
  (check-not-false (member "day" (test "memi legh dail ayoh"))))
