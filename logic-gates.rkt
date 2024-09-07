#lang racket

; little logic gate DSL

#|

# design notes

## surface syntax and high level stuff

(define-module/assignment (not (in) (out))
  (set! out (not in)))

(define-module/assignment (and (a b) (out))
  ; escape to racket.
  ; need binding spaces to distinguish the module `and` and Racket `and`.
  (set! out (and a b)))

; sugar
(define-module/assignment/easy (and (a b) ((and a b))))

(define-module (nand (a b) (out))
  (fresh (tmp)
    (and (a b) (tmp))
    (not (tmp) (out))))

Might want something more like (and [a input] [b input] [out output]), especially if you're going to do
types like bytes later.

applications are module instances.
variables are wires.

need notion of input and output. will need something like a type checker.
this should error:
(define-module (foo (in) (out))
  (not (out) (in)))
; error: input used as an output
; error: output used as an input

fresh vars are inputs and outputs

maybe types could be optional and default to input output. Shouldn't make a difference to the runtime,
It'll just prevent stupid things from happening.

the syntax looks like minikanren/verilog,
but you want it to run like a reactive programming language.

there needs to be a concept of time if you want latches and stuff,
but idk how exactly that should work.
Maybe just 1 "round" of bfs at a time or something.
kind of like redstone I think.

how will debugging work? fit prints somewhere?
maybe just expose internal variables as circuit outputs.

Full example:
(define-input a #t)
(define-input b #f)
(define-output out)
(define circ (circuit (and a b out)))
(circuit-run! circ)
(displayln (get-output out))
(set-input! b #t)
(circuit-run! circ)
(displayln (get-output out))

a circuit has internal state since there is a concept of time.
circuit-run! runs circuit until stable. this may not terminate.
circuit-step! runs circuit for one "tick".

you'll end up wanting clocks too, not sure how those will fit in.
should be able to choose period of clock.
should also be able to choose the delay of a module, or at least add bogus delayer modules.

## runtime

a module has ports
wires connect ports, not necessarily 1 to 1
a wire can be on or off
expand away compound gates?

Maybe delays should be explicit.
Options:
- delay module
  - primitives have no delay
  - if you make an infinite loop with no delays, it's your fault and a step will not terminate
  - stepping the circuit just keeps going in all directions until it hits a delay
  - step starts at each input and each delay from the previous step
  - kind of annoying, but can make macros around it ig
- inherent delay
  - delay on core modules? Or each module boundary?
  - module boundaries would make delay dependent on internal abstraction structure. Something that should be a refactor could change behavior bc of delay
  - everything would require more delay/steps. User would have less straightforward control over delay. You could also have delay modules though.

going to go with a single delay module. Makes everything simpler.

for runtime, expand down to core modules.
|#

(provide)
(require syntax-spec)

; runtime

; a Circuit is a
(struct circuit [inputs outputs gates wires])
; where
; inputs is a list of circuit input ports for the circuit interface
; outputs is a list of circuit output ports for the circuit interface
; gates is a list of gates in the circuit
; wires is a list of wires inside the circuit (connecting the interface ports and gates)

; a gate is a
(struct gate [inputs output proc delay?])
; where
; inputs is a list of input ports
; output is an output port
; proc is a (boolean ... -> boolean)
; where the input arity is the same as the number of input ports
; delay? is whether the gate has delay

; A Port is one of
(struct port [])
(struct input-port port [])
; for gates
(struct circuit-input-port input-port [[value #:mutable]])
; for the circuit interface
(struct output-port port [])
; for gates
(struct circuit-output-port output-port [[value #:mutable]])
; for the circuit interface

; TODO I don't like this mutability. Can you just use wires as circuit inputs and outputs or something?

; A Wire is a
(struct wire [inputs outputs state])
; where
; inputs is a list of input ports
; outputs is a list of output ports
; state is a boolean for whether the wire has power flowing through it
