#lang racket

; https://www.youtube.com/watch?v=PXN7jTNGQIw&t=1s&ab_channel=Computerphile

; model of computation equivalent to turing machine

; instead of a tape, we have counters, where a counter is just a cell with a number.
; the machine can increment, decrement, and check whether a counter is zero. that's it
; it also has a state machine like a turing machine for rules

(module+ test (require rackunit))

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
(struct virtual-machine [counters instructions (pc #:mutable)] #:transparent)
; where
; counters is a mutable hash from symbol to natural
; instructions is a MachineProgram
; pc is a natural, representing the index of the current instruction (program counter)

; I thought of having pc just be a counter, but that doesn't really make sense bc
; you're not supposed to be able to look at the number of a counter

; VirtualMachine -> (hash/c symbol natural)
; run a machine program to completion, return counters
(define (run-machine-program! vm)
  (let loop ()
    (unless (virtual-machine-done? vm)
      (virtual-machine-step! vm)
      (loop)))
  (virtual-machine-counters vm))

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
     (virtual-machine-counter-transform! vm counter sub1)]
    [(j label-name)
     (set-virtual-machine-pc! vm (virtual-machine-label-index vm label-name))]
    [(jz counter label-name)
     (when (virtual-machine-counter-zero? vm counter)
       (set-virtual-machine-pc! vm (virtual-machine-label-index vm label-name)))]))

; VirtualMachine -> MachineInstruction
(define (virtual-machine-current-instruction vm)
  (list-ref (virtual-machine-instructions vm) (virtual-machine-pc vm)))

; VirtualMachine -> void
(define (virtual-machine-increment-pc! vm)
  (set-virtual-machine-pc! vm (add1 (virtual-machine-pc vm))))

; VirtualMachine symbol (natural -> natural) -> void
; apply the function to the counter. should either be increment or decrement
(define (virtual-machine-counter-transform! vm counter proc)
  (hash-set! (virtual-machine-counters vm)
             counter
             ; max 0 to prevent negatives
             (max 0 (proc (hash-ref (virtual-machine-counters vm) counter 0)))))

; VirtualMachine symbol -> boolean
(define (virtual-machine-counter-zero? vm counter)
  (zero? (hash-ref (virtual-machine-counters vm) counter 0)))

; VirtualMachine symbol -> natural
; index of the label instruction with the given name
(define (virtual-machine-label-index vm label-name)
  (or (index-of (virtual-machine-instructions vm) (label label-name))
      (error 'run-machine-program "unknown label: ~a" label-name)))

#|
optimizations:
- cache label indices
- garbage collection?
  - make a graph of labels and jumps, very naive. labels are associated with counters referenced in their "blocks". reachability analysis.
    jumps far back screw you with this approach.
|#

(module+ test
  (test-equal?
   "clear"
   (run-machine-program!
    (virtual-machine
     (make-hash '((a . 10)))
     (list (label 'start)
           (jz 'a 'end)
           (dec 'a)
           (j 'start)
           (label 'end))
     0))
   (make-hash '((a . 0))))
  (test-equal?
   "move"
   (run-machine-program!
    (virtual-machine
     (make-hash '((a . 10) (b . 0)))
     (list (label 'start)
           (jz 'a 'end)
           (dec 'a)
           (inc 'b)
           (j 'start)
           (label 'end))
     0))
   (make-hash '((a . 0) (b . 10))))
  (test-equal?
   "copy"
   (run-machine-program!
    (virtual-machine
     (make-hash '((a . 10) (b . 0)))
     (list (label 'start-a->temp)
           (jz 'a 'end-a->temp)
           (dec 'a)
           (inc 'temp)
           (j 'start-a->temp)
           (label 'end-a->temp)
           (label 'start-temp->ab)
           (jz 'temp 'end)
           (dec 'temp)
           (inc 'a)
           (inc 'b)
           (j 'start-temp->ab)
           (label 'end))
     0))
   (make-hash '((a . 10) (b . 10) (temp . 0)))))

; instruction "macros"

; (listof MachineInstruction) -> (listof MachineInstruction)
; use this to sequence instructions. supports nested sequences
(define (sequence . instructions)
  ; if it's sequences all the way down, shallow flattening here is fine
  (foldr (lambda (instruction instructions)
           (if (list? instruction)
               (append instruction instructions)
               (cons instruction instructions)))
         '()
         instructions))

; set counter to 0
(define (clear counter)
  (define start (gensym 'clear-start))
  (define end (gensym 'clear-end))
  (sequence (label start)
            (jz counter end)
            (dec counter)
            (j start)
            (label end)))

; clear from and add its contents to to
(define (transfer to from)
  (define start (gensym 'transfer-start))
  (define end (gensym 'transfer-end))
  (if (eq? to from)
      (sequence)
      (sequence (label start)
                (jz from end)
                (dec from)
                (inc to)
                (j start)
                (label end))))

; clear from and set to to its value
(define (move to from)
  (if (eq? to from)
      (sequence)
      (sequence
       (clear to)
       (transfer to from))))

; copy from to to. clears to
(define (copy to from)
  (cond
    [(eq? to from)
     (sequence)]
    [else
     ; assumes copy-temp is 0
     (define start (gensym 'copy-start))
     (define end (gensym 'copy-end))
     (sequence (clear to)
               (transfer copy-temp from)
               (label start)
               (jz copy-temp end)
               (dec copy-temp)
               (inc to)
               (inc from)
               (j start)
               (label end))]))
; can be reused since it's zero between uses
(define copy-temp (gensym 'copy-temp))

(define (add to a b)
  (define start (gensym 'add-start))
  (define end (gensym 'add-end))
  ; TODO this breaks if to == b
  (sequence (copy to a)
            (copy add-temp b)
            (transfer to add-temp)))
(define add-temp (gensym 'add-temp))

; a *= b
(define (multiply to a b)
  ; add b to to a times
  (sequence (copy multiply-temp a)
            ; the clear needs to happen after the copy in case to == a
            (clear to)
            (repeat-and-decrement-until-empty
             multiply-temp
             (add to to b))))
(define multiply-temp (gensym 'multiply-temp))

(define (subtract to a b)
  ; decrement b times
  (sequence (copy to a)
            (copy subtract-temp b)
            (repeat-and-decrement-until-empty
             subtract-temp
             (dec to))))
(define subtract-temp (gensym 'subtract-temp))

; loop as many times as the number the counter holds, clears the counter
; instructions can be a sequence or an individual instruction
; decrements after loop body
(define (repeat-and-decrement-until-empty counter instructions)
  (define start (gensym 'repeat-and-decrement-until-empty-start))
  (define end (gensym 'repeat-and-decrement-until-empty-end))
  (sequence (label start)
            (jz counter end)
            instructions
            (dec counter)
            (j start)
            (label end)))

(define (divide to-quotient to-remainder a b)
  (define start (gensym 'divide-start))
  (define end (gensym 'divide-end))
  ; subtract b from a until a < b, count how many times
  ; final difference is remainder
  (sequence (copy to-remainder a)
            (clear to-quotient)
            (label start)
            (jl a b end)
            (inc to-quotient)
            (subtract to-remainder to-remainder b)
            (j start)
            (label end)))

; jump if a <= b
(define (jle a b label-name)
  (sequence (subtract jle-temp a b)
            (jz jle-temp label-name)))
(define jle-temp (gensym 'jle-temp))

; jump if a < b
(define (jl a b label-name)
  (define maybe (gensym 'jl-maybe))
  (define dont (gensym 'jl-dont))
  (sequence (jle a b maybe)
            (j dont)
            (label maybe)
            (jle b a dont); they're equal
            (j label-name)
            (label dont)))

; jump if a = b
(define (je a b label-name)
  (define maybe (gensym 'je-maybe))
  (define dont (gensym 'je-dont))
  (sequence (jle a b maybe)
            (j dont)
            (label maybe)
            (jle b a label-name)
            (label dont)))

; jump if counter != 0
(define (jnz label-name)
  (define dont (gensym 'jnz-dont))
  (sequence (jz dont)
            (j label-name)
            (label dont)))
