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

(module+ test
  (test-equal?
   "clears"
   (run-machine-program!
    (virtual-machine
     (make-hash '((a . 10) (b . 20) (c . 30)))
     (sequence (sequence (sequence (clear 'a)) (clear 'b)))
     0))
   (make-hash '((a . 0) (b . 0) (c . 30)))))

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

(module+ test
  (test-equal?
   "basic transfer"
   (run-machine-program!
    (virtual-machine
     (make-hash '((a . 10) (b . 20) (c . 40)))
     (transfer 'a 'b)
     0))
   (make-hash '((a . 30) (b . 0) (c . 40))))
  (test-equal?
   "transfer to self"
   (run-machine-program!
    (virtual-machine
     (make-hash '((a . 10) (b . 20) (c . 40)))
     (transfer 'a 'a)
     0))
   (make-hash '((a . 10) (b . 20) (c . 40)))))

; clear from and set to to its value
(define (move to from)
  (if (eq? to from)
      (sequence)
      (sequence
       (clear to)
       (transfer to from))))

(module+ test
  (test-equal?
   "basic move"
   (run-machine-program!
    (virtual-machine
     (make-hash '((a . 10) (b . 20) (c . 40)))
     (move 'a 'b)
     0))
   (make-hash '((a . 20) (b . 0) (c . 40))))
  (test-equal?
   "move to self"
   (run-machine-program!
    (virtual-machine
     (make-hash '((a . 10) (b . 20) (c . 40)))
     (move 'a 'a)
     0))
   (make-hash '((a . 10) (b . 20) (c . 40)))))

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

(module+ test
  (test-equal?
   "basic copy"
   (run-machine-program!
    (virtual-machine
     (make-hash '((a . 10) (b . 20) (c . 40)))
     (copy 'a 'b)
     0))
   (make-hash `((a . 20) (b . 20) (c . 40) (,copy-temp . 0))))
  (test-equal?
   "copy to self"
   (run-machine-program!
    (virtual-machine
     (make-hash '((a . 10) (b . 20) (c . 40)))
     (copy 'a 'a)
     0))
   (make-hash '((a . 10) (b . 20) (c . 40)))))

(define (add to a b)
  (define start (gensym 'add-start))
  (define end (gensym 'add-end))
  (sequence (copy add-temp b)
            (copy to a)
            (transfer to add-temp)))
(define add-temp (gensym 'add-temp))

(module+ test
  (test-equal?
   "basic add"
   (run-machine-program!
    (virtual-machine
     (make-hash '((a . 10) (b . 20) (c . 30)))
     (add 'a 'b 'c)
     0))
   (make-hash `((a . 50) (b . 20) (c . 30) (,add-temp . 0) (,copy-temp . 0))))
  (test-equal?
   "add to self left"
   (run-machine-program!
    (virtual-machine
     (make-hash '((a . 10) (b . 20) (c . 30)))
     (add 'a 'a 'c)
     0))
   (make-hash `((a . 40) (b . 20) (c . 30) (,add-temp . 0) (,copy-temp . 0))))
  (test-equal?
   "add to self right"
   (run-machine-program!
    (virtual-machine
     (make-hash '((a . 10) (b . 20) (c . 30)))
     (add 'a 'c 'a)
     0))
   (make-hash `((a . 40) (b . 20) (c . 30) (,add-temp . 0) (,copy-temp . 0)))))

; a *= b
(define (multiply to a b)
  ; add b to to a times
  (sequence (copy multiply-temp-a a)
            (copy multiply-temp-b b)
            ; the clear needs to happen after the copy in case to == a
            (clear to)
            (repeat-and-decrement-until-empty
             multiply-temp-a
             (add to to multiply-temp-b))
            ; not actually necessary
            (clear multiply-temp-b)))
(define multiply-temp-a (gensym 'multiply-temp-a))
(define multiply-temp-b (gensym 'multiply-temp-b))

(module+ test
  (test-equal?
   "basic multiply"
   (run-machine-program!
    (virtual-machine
     (make-hash '((a . 10) (b . 20) (c . 30)))
     (multiply 'a 'b 'c)
     0))
   (make-hash `((a . 600) (b . 20) (c . 30) (,multiply-temp-a . 0) (,multiply-temp-b . 0) (,add-temp . 0) (,copy-temp . 0))))
  (test-equal?
   "multiply to self left"
   (run-machine-program!
    (virtual-machine
     (make-hash '((a . 10) (b . 20) (c . 30)))
     (multiply 'a 'a 'c)
     0))
   (make-hash `((a . 300) (b . 20) (c . 30) (,multiply-temp-a . 0) (,multiply-temp-b . 0) (,add-temp . 0) (,copy-temp . 0))))
  (test-equal?
   "multiply to self right"
   (run-machine-program!
    (virtual-machine
     (make-hash '((a . 10) (b . 20) (c . 30)))
     (multiply 'a 'c 'a)
     0))
   (make-hash `((a . 300) (b . 20) (c . 30) (,multiply-temp-a . 0) (,multiply-temp-b . 0) (,add-temp . 0) (,copy-temp . 0)))))

(define (subtract to a b)
  ; decrement b times
  (sequence (copy subtract-temp b)
            (copy to a)
            (repeat-and-decrement-until-empty
             subtract-temp
             (dec to))))
(define subtract-temp (gensym 'subtract-temp))

(module+ test
  (test-equal?
   "basic subtract"
   (run-machine-program!
    (virtual-machine
     (make-hash '((a . 10) (b . 70) (c . 30)))
     (subtract 'a 'b 'c)
     0))
   (make-hash `((a . 40) (b . 70) (c . 30) (,subtract-temp . 0) (,copy-temp . 0))))
  (test-equal?
   "subtract 3 10"
   (run-machine-program!
    (virtual-machine
     (make-hash '((a . 10) (b . 3) (c . 10)))
     (subtract 'a 'b 'c)
     0))
   (make-hash `((a . 0) (b . 3) (c . 10) (,subtract-temp . 0) (,copy-temp . 0))))
  (test-equal?
   "subtract from self left"
   (run-machine-program!
    (virtual-machine
     (make-hash '((a . 70) (b . 20) (c . 30)))
     (subtract 'a 'a 'c)
     0))
   (make-hash `((a . 40) (b . 20) (c . 30) (,subtract-temp . 0) (,copy-temp . 0))))
  (test-equal?
   "subtract from self right"
   (run-machine-program!
    (virtual-machine
     (make-hash '((a . 30) (b . 20) (c . 70)))
     (subtract 'a 'c 'a)
     0))
   (make-hash `((a . 40) (b . 20) (c . 70) (,subtract-temp . 0) (,copy-temp . 0)))))

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
  (sequence (copy divide-temp b)
            (copy to-remainder a)
            (clear to-quotient)
            (label start)
            (jl to-remainder divide-temp end)
            (inc to-quotient)
            (subtract to-remainder to-remainder divide-temp)
            (j start)
            (label end)
            ; not actually necessary
            (clear divide-temp)))
(define divide-temp (gensym 'divide-temp))

(module+ test
  (test-equal?
   "basic divide"
   (run-machine-program!
    (virtual-machine
     (make-hash '((quot . 100) (b . 36) (c . 10) (rem . 999)))
     (divide 'quot 'rem 'b 'c)
     0))
   (make-hash `((quot . 3) (b . 36) (c . 10) (rem . 6) (,subtract-temp . 0) (,copy-temp . 0) (,jle-temp . 4) (,divide-temp . 0))))
  (test-equal?
   "divide 0 10"
   (run-machine-program!
    (virtual-machine
     (make-hash '((quot . 100) (b . 0) (c . 10) (rem . 999)))
     (divide 'quot 'rem 'b 'c)
     0))
   (make-hash `((quot . 0) (b . 0) (c . 10) (rem . 0) (,subtract-temp . 0) (,copy-temp . 0) (,jle-temp . 10) (,divide-temp . 0))))
  (test-equal?
   "divide 10 10"
   (run-machine-program!
    (virtual-machine
     (make-hash '((quot . 100) (b . 10) (c . 10) (rem . 999)))
     (divide 'quot 'rem 'b 'c)
     0))
   (make-hash `((quot . 1) (b . 10) (c . 10) (rem . 0) (,subtract-temp . 0) (,copy-temp . 0) (,jle-temp . 10) (,divide-temp . 0))))
  (test-equal?
   "divide 7 10"
   (run-machine-program!
    (virtual-machine
     (make-hash '((quot . 100) (b . 7) (c . 10) (rem . 999)))
     (divide 'quot 'rem 'b 'c)
     0))
   (make-hash `((quot . 0) (b . 7) (c . 10) (rem . 7) (,subtract-temp . 0) (,copy-temp . 0) (,jle-temp . 3) (,divide-temp . 0))))
  (test-equal?
   "divide by self left"
   (run-machine-program!
    (virtual-machine
     (make-hash '((a . 70) (b . 10)))
     (divide 'a 'rem 'a 'b)
     0))
   (make-hash `((a . 7) (b . 10) (rem . 0) (,subtract-temp . 0) (,copy-temp . 0) (,jle-temp . 10) (,divide-temp . 0))))
  (test-equal?
   "divide by self right"
   (run-machine-program!
    (virtual-machine
     (make-hash '((a . 10) (b . 70)))
     (divide 'a 'rem 'b 'a)
     0))
   (make-hash `((a . 7) (b . 70) (rem . 0) (,subtract-temp . 0) (,copy-temp . 0) (,jle-temp . 10) (,divide-temp . 0)))))

; jump if a <= b
(define (jle a b label-name)
  (sequence (subtract jle-temp a b)
            (jz jle-temp label-name)))
(define jle-temp (gensym 'jle-temp))

(module+ test
  (test-equal?
   "jle jump"
   (run-machine-program!
    (virtual-machine
     (make-hash '((a . 10) (b . 20)))
     (sequence (jle 'a 'b 'jumped)
               (j 'end)
               (label 'jumped)
               (inc 'a)
               (label 'end))
     0))
   (make-hash `((a . 11) (b . 20) (,copy-temp . 0) (,subtract-temp . 0) (,jle-temp . 0))))
  (test-equal?
   "jle don't jump"
   (run-machine-program!
    (virtual-machine
     (make-hash '((a . 30) (b . 20)))
     (sequence (jle 'a 'b 'jumped)
               (inc 'a)
               (j 'end)
               (label 'jumped)
               (inc 'b)
               (label 'end))
     0))
   (make-hash `((a . 31) (b . 20) (,copy-temp . 0) (,subtract-temp . 0) (,jle-temp . 10)))))

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

(module+ test
  (test-equal?
   "jl jump"
   (run-machine-program!
    (virtual-machine
     (make-hash '((a . 10) (b . 20)))
     (sequence (jl 'a 'b 'jumped)
               (j 'end)
               (label 'jumped)
               (inc 'a)
               (label 'end))
     0))
   (make-hash `((a . 11) (b . 20) (,copy-temp . 0) (,subtract-temp . 0) (,jle-temp . 10))))
  (test-equal?
   "jl don't jump eq"
   (run-machine-program!
    (virtual-machine
     (make-hash '((a . 30) (b . 30)))
     (sequence (jl 'a 'b 'jumped)
               (inc 'a)
               (j 'end)
               (label 'jumped)
               (inc 'b)
               (label 'end))
     0))
   (make-hash `((a . 31) (b . 30) (,copy-temp . 0) (,subtract-temp . 0) (,jle-temp . 0))))
  (test-equal?
   "jl don't jump >"
   (run-machine-program!
    (virtual-machine
     (make-hash '((a . 40) (b . 30)))
     (sequence (jl 'a 'b 'jumped)
               (inc 'a)
               (j 'end)
               (label 'jumped)
               (inc 'b)
               (label 'end))
     0))
   (make-hash `((a . 41) (b . 30) (,copy-temp . 0) (,subtract-temp . 0) (,jle-temp . 10)))))

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
