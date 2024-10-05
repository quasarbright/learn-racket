#lang racket

; this lives in its own repo now, called rico-blaze

; usage of logic language to create cpu components
; uses designs from https://www.youtube.com/watch?v=I0-izyq6q5s&t=850s

(module+ test (require rackunit))
(require "./logic-gates-lang.rkt")

(module+ test
  (require (for-syntax syntax/srcloc syntax/parse))
  (define-syntax-rule (until cnd body ...)
    (let loop ()
      (unless cnd
        body ...
        (loop))))
  ; ex: (test-run! and-circ [a #t] [b #f] -> [out #f])
  (define-syntax test-run!
    (syntax-parser
      [(_ circ:id [in:id in-v:boolean] ... (~datum ->) [out:id out-v:boolean] ...)
       (define loc (build-source-location-list this-syntax))
       (define/syntax-parse (loc-stuff ...) (for/list ([v loc]) (datum->syntax this-syntax v)))
       #'(begin
           (set-input! in in-v)
           ...
           (circuit-run! circ)
           (with-check-info* (list (make-check-location (list loc-stuff ...)))
             (lambda ()
               (check-equal? (get-output circ out) out-v (symbol->string 'out))
               ...)))])))

(define-syntax-rule (define-wrapper-gate (f x ...)) (define-gate (f x ...) (f x ...)))
(define-wrapper-gate (identity a))
(define-wrapper-gate (not a))
(define-wrapper-gate (and a b))
(define-wrapper-gate (or a b))
(define-wrapper-gate (nor a b))
(define-wrapper-gate (xor a b))

; startup of 1
; period of 2
; 001010101...
(define-module (1-clock [out : out])
  (define-wire w)
  (not w w)
  (identity w out))

; startup of 2
; delay of 3
; r resets the state
; s sets the state
; r and s shouldn't both be true
(define-module (sr-latch [r : in] [s : in] [q : out])
  (define-wires w1 w2)
  (nor r w2 w1)
  (nor s w1 w2)
  (identity w1 q))

(module+ test
  (test-case "sr-latch"
    (define-input r)
    (define-input s)
    (define-output q)
    (define-circuit circ (sr-latch r s q))

    (define-syntax-rule
      (test r-val s-val q-expected)
      (begin
        (set-input! r r-val)
        (set-input! s s-val)
        (circuit-run! circ)
        (check-equal? (get-output circ q) q-expected)))
    ; stabilizes when an input is on
    (test-run! circ [r #t] -> [q #f])
    ; stabilizes when all inputs are off (after initial stabilization)
    (test-run! circ [r #f] -> [q #f])
    ; writes
    (test-run! circ [s #t] -> [q #t])
    ; remembers when inputs are off
    (test-run! circ [s #f] -> [q #t])
    ; clear
    (test-run! circ [r #t] -> [q #f])
    ; remembers
    (test-run! circ [r #f] -> [q #f])))

; startup of 3
; delay of 4
; like sr latch, but only does anything when e is on
(define-module (gated-sr-latch [e : in] [r : in] [s : in] [q : out])
  (sr-latch (and e r _) (and e s _) q))

(module+ test
  (test-case "gated-sr-latch"
    (define-input e)
    (define-input r)
    (define-input s)
    (define-output q)
    (define-circuit circ (gated-sr-latch e r s q))
    ; initial stable
    (test-run! circ [e #t] [r #t] -> [q #f])
    ; no write when not enabled
    (test-run! circ [e #f] [r #f] [s #t] -> [q #f])
    ; write
    (test-run! circ [e #t] [s #t] -> [q #t])
    ; remember
    (test-run! circ [e #f] [r #f] [s #f] -> [q #t])
    ; no clear when not enabled
    (test-run! circ [e #f] [r #t] -> [q #t])
    ; clear
    (test-run! circ [e #t] [r #t] -> [q #f])
    ; remember
    (test-run! circ [e #f] [r #f] [s #f] -> [q #f])))

; stores d if e is on
(define-module (d-latch [e : in] [d : in] [q : out])
  (define-wires not-d)
  (not d not-d)
  (gated-sr-latch e (not d _) d q))

(module+ test
  (test-case "d-latch"
    (define-input d)
    (define-input e)
    (define-output q)
    (define-circuit circ (d-latch e d q))

    ; stabilizes (needs to be powered though)
    (test-run! circ [e #t] -> [q #f])
    ; remembers
    (test-run! circ [e #f] -> [q #f])
    ; doesn't write when e is off
    (test-run! circ [e #f] [d #t] -> [q #f])
    ; writes when e is on
    (test-run! circ [e #t] [d #t] -> [q #t])
    ; remembers
    (test-run! circ [e #f] [d #f] -> [q #t])
    ; write off
    (test-run! circ [e #t] [d #f] -> [q #f])))

; stores d on rising edge of clock
(define-module (d-flip-flop [clock : in] [d : in] [q : out])
  (define-wires not-clock inner-q)
  (d-latch (not clock _) d inner-q)
  (d-latch clock inner-q q))

(module+ test
  (test-case "d-flip-flop"
    (define-input clock)
    (define-input d)
    (define-output q)
    (define-circuit circ (d-flip-flop clock d q))
    ; stabilize
    (test-run! circ [clock #t] -> [q #f])
    ; remember
    (test-run! circ [clock #f] -> [q #f])
    ; no write
    (test-run! circ [d #t] -> [q #f])
    ; write on rising edge
    (test-run! circ [clock #t] [d #t] -> [q #t])
    ; don't write while still high
    (test-run! circ [clock #t] [d #f] -> [q #t])
    ; don't write on falling edge
    (test-run! circ [clock #f] [d #f] -> [q #t])
    ; write on rising edge
    (test-run! circ [clock #t] [d #f] -> [q #f])))

(define-module (1-bit-register [e : in] [clock : in] [d : in] [q : out])
  ; could just do (d-flip-flop d (and e clock _) q),
  ; but then it'd store on rising edge of e.
  (define-wire q^)
  (d-flip-flop clock
               (or (and (not e _) q^ _)
                   (and d e _) _)
               q^)
  (identity q^ q))

(module+ test
  (test-case "1 bit register"
    (define-input e)
    (define-input clock)
    (define-input d)
    (define-output q)
    (define-circuit circ
      (1-bit-register e clock d q))
    ; stabilize
    (test-run! circ [clock #t] -> [q #f])
    ; don't write when disabled
    (test-run! circ [e #f] [clock #f] -> [q #f])
    (test-run! circ [e #f] [clock #t] [d #t] -> [q #f])
    ; don't write on rising edge of e instead of clock
    (test-run! circ [e #f] [clock #f] -> [q #f])
    (test-run! circ [e #t] [clock #f] [d #t] -> [q #f])
    ; write
    (test-run! circ [e #t] [clock #t] [d #t] -> [q #t])
    ; don't write while still high
    (test-run! circ [d #f] -> [q #t])
    ; don't write on falling edge
    (test-run! circ [d #f] [clock #f] -> [q #t])
    ; clear
    (test-run! circ [e #t] [clock #t] [d #f] -> [q #f])
    ; pulse write (fails)
    #;(begin
        (test-run! circ [e #t] [clock #f] [d #f] -> [q #f])
        (set-input! clock #t)
        (set-input! d #t)
        (circuit-step! circ)
        (test-run! circ [clock #f] [d #f] -> [q #t]))))

; stores in if e is on
(define-module (4-bit-register [e : in] [clock : in]
                               [in-0 : in] [in-1 : in] [in-2 : in] [in-3 : in]
                               [out-0 : out] [out-1 : out] [out-2 : out] [out-3 : out])
  (1-bit-register e clock in-0 out-0)
  (1-bit-register e clock in-1 out-1)
  (1-bit-register e clock in-2 out-2)
  (1-bit-register e clock in-3 out-3))

(define-module (full-adder [a : in] [b : in] [c : in] [sum : out] [carry : out])
  (xor (xor a b _) c sum)
  (or (and a b _)
      (or (and a c _)
          (and b c _) _)
      carry))

(module+ test
  (test-case "full-adder"
    (define-input a)
    (define-input b)
    (define-input c)
    (define-output sum)
    (define-output carry)
    (define-circuit circ (full-adder a b c sum carry))
    (test-run! circ [a #f] [b #f] [c #f] -> [sum #f] [carry #f])
    (test-run! circ [a #f] [b #f] [c #t] -> [sum #t] [carry #f])
    (test-run! circ [a #f] [b #t] [c #f] -> [sum #t] [carry #f])
    (test-run! circ [a #f] [b #t] [c #t] -> [sum #f] [carry #t])
    (test-run! circ [a #t] [b #f] [c #f] -> [sum #t] [carry #f])
    (test-run! circ [a #t] [b #f] [c #t] -> [sum #f] [carry #t])
    (test-run! circ [a #t] [b #t] [c #f] -> [sum #f] [carry #t])
    (test-run! circ [a #t] [b #t] [c #t] -> [sum #t] [carry #t])))
