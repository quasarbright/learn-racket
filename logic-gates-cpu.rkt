#lang racket

; usage of logic language to create cpu components

(module+ test (require rackunit))
(require "./logic-gates-lang.rkt")

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

; startup of 3
; delay of 4
; like sr latch, but only does anything when e is on
(define-module (gated-sr-latch [e : in] [r : in] [s : in] [q : out])
  (define-wires r^ s^)
  (and e r r^)
  (and e s r^)
  (sr-latch r^ s^ q))

; stores d if e is on
(define-module (d-latch [e : in] [d : in] [q : out])
  (define-wires not-d)
  (not d not-d)
  (gated-sr-latch e not-d d q))

; stores d on rising edge of clock
(define-module (d-flip-flop [clock : in] [d : in] [q : out])
  (define-wires not-clock inner-q)
  (not clock not-clock)
  (d-latch not-clock d inner-q)
  (d-latch clock inner-q q))

(define-module (1-bit-register [e : in] [clock : in] [d : in] [q : out])
  (define-wires
    not-e
    and-d-e
    and-not-e-q^
    q^
    inner-d)
  (and d e and-d-e)
  (not e not-e)
  (and not-e q^ and-not-e-q^)
  (d-flip-flop inner-d clock q^)
  (identity q^ q))

(module+ test
  (define-syntax-rule (until cnd body ...)
    (let loop ()
      (unless cnd
        body ...
        (loop))))
  (test-case "1 bit register"
    (define-input e)
    (define-input d)
    (define-output q)
    (define-circuit circ
      (define-wire clock)
      (1-clock clock)
      (1-bit-register e clock d q))
    (set-input! e #t)
    (set-input! d #f)
    (circuit-step! circ)
    (circuit-step! circ)
    (circuit-step! circ); clock rising
    (circuit-step! circ)
    (check-equal? (get-output circ q) #f)

    (set-input! d #t)
    (until (get-output circ q) (circuit-step! circ))

    ; shouldn't update when e is off
    (set-input! e #f)
    (set-input! d #f)
    (circuit-step! circ)
    (circuit-step! circ)
    (circuit-step! circ)
    (circuit-step! circ)
    (check-equal? (get-output circ q) #t)

    ; now update
    (set-input! e #t)
    (until (not (get-output circ q)) (circuit-step! circ)))
  ; TODO why infinite loop
  #;(test-case "1 bit register clock rising"
    (define-input e)
    (define-input d)
    (define-output q)
    (define-input clock)
    (define-circuit circ
      (1-bit-register e clock d q))

    (set-input! clock #f)
    (set-input! e #t)
    (set-input! d #t)
    (circuit-run! circ)
    (check-equal? (get-output circ q) #f)

    (set-input! clock #t)
    (circuit-run! circ)
    (check-equal? (get-output circ q) #t)

    (set-input! d #f)
    (circuit-run! circ)
    (check-equal? (get-output circ q) #t)

    (set-input! clock #f)
    (circuit-run! circ)
    (check-equal? (get-output circ q) #t)

    (set-input! clock #t)
    (circuit-run! circ)
    (check-equal? (get-output circ q) #f)))

; stores in if e is on
(define-module (4-bit-register [e : in] [clock : in]
                               [in-0 : in] [in-1 : in] [in-2 : in] [in-3 : in]
                               [out-0 : out] [out-1 : out] [out-2 : out] [out-3 : out])
  (1-bit-register e clock in-0 out-0)
  (1-bit-register e clock in-1 out-1)
  (1-bit-register e clock in-2 out-2)
  (1-bit-register e clock in-3 out-3))

(define-module (full-adder [a : in] [b : in] [c : in] [sum : out] [carry : out])
  (define-wires xor-ab or-ab)
  (xor a b xor-ab)
  (xor xor-ab c sum)
  (or a b or-ab)
  (and or-ab c carry))
