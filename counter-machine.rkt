#lang racket

; https://www.youtube.com/watch?v=PXN7jTNGQIw&t=1s&ab_channel=Computerphile

; model of computation equivalent to turing machine

; instead of a tape, we have counters, where a counter is just a cell with a number.
; the machine can increment, decrement, and check whether a counter is zero. that's it
; it also has a state machine like a turing machine for rules

; a MachineInstruction is one of
(struct label [name] #:transparent)
; where name is a symbol
; sets a label for jumping to, no effect
(struct inc [counter] #:transparent)
; where counter is a symbol
; increment the counter
(struct dec [counter] #:transparent)
; where counter is a symbol
; decrement the counter
(struct j [label-name] #:transparent)
; where label-name is a symbol
; jump unconditionally
(struct jz [counter label-name] #:transparent)
; where
; counter is a symbol
; label-name is a symbol
; jump if counter is zero

; A MachineProgram is a (listof MachineInstruction)

; A VirtualMachine is a
(struct virtual-machine [counters instructions (pc #:mutable)])
; where
; counters is a mutable hash from symbol to natural
; instructions is a MachineProgram
; pc is a natural, representing the index of the current instruction

; I thought of having pc just be a counter, but that doesn't really make sense bc
; you're not supposed to be able to look at the number of a counter

; VirtualMachine -> void
; run a machine program to completion
(define (run-machine-program vm)
  (let loop ()
    (unless (virtual-machine-done? vm)
      (virtual-machine-step! vm)
      (loop))))

; VirtualMachine -> boolean
; is the virtual machine done running?
(define (virtual-machine-done? vm)
  (>= (virtual-machine-pc vm) (length (virtual-machine-instructions vm))))

; VirtualMachine -> void
; run the current instruction
(define (virtual-machine-step! vm)
  (define current-instruction (virtual-machine-current-instruction vm))
  (virtual-machine-increment-pc! vm)
  (match current-instruction
    [(label name)
     (void)]
    [(inc counter)
     (virtual-machine-counter-transform! vm counter add1)]
    [(dec counter)
     (virtual-machine-counter-transform! vm counter add1)]
    [(j label-name)
     (virtual-machine-set-pc! vm (virtual-machine-label-index vm label-name))]
    [(jz counter label-name)
     (when (virtual-machine-counter-zero? vm counter)
       (virtual-machine-set-pc! vm (virtual-machine-label-index vm label-name)))]))
