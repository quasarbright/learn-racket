#lang racket

; little logic circuit DSL
; this file contains the runtime and design notes

#|

# design notes

## surface syntax and high level stuff

surface concepts:
a module is a unit of logic.
modules can contain other sub-modules.
modules have wires, which are there interfaces.
wires can be inputs, outputs, or both.
data/power flows into and out of modules through wires.
a wire can connect many modules together. They are not 1-to-1 connectors.
gates are primitive modules which contain no sub-modules.
gates have zero or more input wires and one output wire.
gates run racket code directly to produce a boolean output.

; gates are primitive modules
(define-gate (and a b)
  (and a b))
; the first is the gate name and input names,
; the body is the racket code to produce the boolean result

(define-gate (not a)
  (not a))

; modules are composable logical units
(define-module (nand [a : in] [b : in] [out : out])
  (define-wire tmp)
  ; gates take in an implicit extra "argument" for output
  (and a b tmp)
  (not tmp out))

; like a redstone repeater
(define-gate (id a)
  a)

(define-module (clock [x : inout])
  (not x x))

; no annotation defaults to inout
(define-module (clock x)
  (not x x))

want type checker for in vs out vs inout
this should error:
(define-module (foo [in in] [out out])
  (not out in))
; error: in: input used as an output
; error: out: output used as an input

x : t means "x can be used as a t", not "x is a t". idc about "is a".

t := in, out, inout

subtyping: t1 <: t2 means "any t1 can be used as a t2"
inout <: in
inout <: out
t <: t

generally, passed arguments must be subtypes of expected argument types
specifically:
supplying an out where an in is expected is an error since the callee module will use it as an input.
supplying an out where an inout is expected is an error since it may be used as an input in the callee module
supplying an inout where an out is expected is ok since an inout

define-wire creates an inout. It would make no sense to have an in-only wire. It would be unusable because no output would write to it. I guess you might want to do
(define-module (true [out out])
  (define-wire tmp)
  (not tmp out))
But there's no need to allow the creation of in-only wires

Types are mostly optional. They can be used to prevent stupid things from happening if desired.

the syntax looks like minikanren/verilog,
but you want it to run like a reactive programming language.

there needs to be a concept of time if you want latches and stuff,
but idk how exactly that should work.
Maybe just 1 "round" of bfs at a time or something.
kind of like redstone I think.

how will debugging work? fit prints somewhere?
maybe just expose internal variables as circuit outputs.

Full example:
(define-input a)
(define-input b)
(define-output out)
(define circ (circuit (and a b out)))
(set-input! a #t)
(circuit-run! circ)
(get-output out)
(set-input! b #t)
(circuit-run! circ)
(get-output out)

a circuit has internal state since there is a concept of time.
circuit-run! runs circuit until stable. this may not terminate.
circuit-step! runs circuit for one "tick".

you'll end up wanting clocks too, not sure how those will fit in.
should be able to choose period of clock. or at least make a clock with different periods.
should also be able to choose the delay of a module, or at least add bogus delayer modules.

for time, ended up going with a redstone-like cellular automaton approach.
see runtime design for more details.

## runtime

runtime concepts:
a gate is a primitive unit of logic.
a gate has zero or more input ports and one output port.
a port is an interface for a gate.
a port is either an input or output port, not both.
a port can either be powered or not powered.
a wire connects one output port to one input port.
data/power flows from output ports to input ports.
a circuit is a collection of gates and wires.

Options for how to handle time:
- delay module
  - primitives have no delay
  - if you make an infinite loop with no delays, it's your fault and a step will not terminate
  - stepping the circuit just keeps going in all directions until it hits delays
  - step starts at each input and each delay from the previous step
  - kind of annoying, but can make macros around it ig
- inherent delay
  - delay on core modules? Or each module boundary?
  - module boundaries would make delay dependent on internal abstraction structure. Something that should be a refactor could change behavior bc of delay
  - everything would require more delay/steps. User would have less straightforward control over delay. You could also have delay modules though.
- global update. like cellular automaton/redstone
  - globally update all ports every step based on the current state, like a cellular automaton.
  - do a global update based on the previous step's state, like a cellular automaton.
  - in the next state, an input will be powered if any of the outputs connected to it are powered in the current state.
  - in the next state, an output will be powered if its gate outputs true based on its inputs in the current state.


going to go with cellular automaton
ended up changing it a little. outputs immediately power inputs

|#

(module+ test (require rackunit))
(provide
 circuit
 circuit?
 (struct-out gate)
 port?
 (struct-out input-port)
 (struct-out output-port)
 (struct-out wire)
 circuit-debug
 (contract-out
  [circuit-run! (-> circuit? void?)]
  [circuit-step! (-> circuit? void?)]
  [circuit-reset! (-> circuit? void?)]
  [circuit-port-powered? (-> circuit? port? boolean?)]
  [set-circuit-port-powered?! (-> circuit? port? boolean? void?)]
  [circuit-union (->* () #:rest (listof circuit?) circuit?)]
  [circuit->datum (-> circuit? any)]))
(require racket/match)

; runtime

; a Circuit is a
(struct circuit [gates wires [powered-ports #:mutable]])
; where
; gates is a list of gates in the circuit
; wires is a list of wires inside the circuit
; powered-ports is a seteq of ports that are receiving or sending power. This is the state.
; Represents a running logic circuit.

; a Gate is a
(struct gate [name inputs output proc] #:property prop:object-name 0)
; where
; inputs is a list of input ports
; output is an output port
; proc is a (boolean ... -> boolean)
; where the input arity is the same as the number of input ports
; Represents a logic gate

; A Port is one of
(struct port [name] #:property prop:object-name 0)

(struct input-port port [])
(struct output-port port [])
; Represents the interfaces of a logic gate

; A Wire is a
(struct wire [output input]
  #:transparent
  #:guard (lambda (output input name)
            (unless (input-port? input)
              (error "wire input must be an input port"))
            (unless (output-port? output)
              (error "wire output must be an output port"))
            (values output input)))
; where
; input is an input port
; output is an output port
; Represents a connection between two logic gates.
; Power flows from output to input.

; example:
; a-->|\
;     | |-->out
; b-->|/
(define and-a (input-port 'a))
(define and-b (input-port 'b))
(define and-out (output-port 'out))
(define and-circuit
  (let ([and-gate (gate 'and (list and-a and-b) and-out (lambda (a b) (and a b)))])
    (circuit (list and-gate) (list) (seteq))))

(module+ test
  (test-case "and-gate full use"
    (circuit-reset! and-circuit)
    (circuit-step! and-circuit)
    (check-equal? (circuit-port-powered? and-circuit and-out) #f)

    (circuit-reset! and-circuit)
    (set-circuit-port-powered?! and-circuit and-a #t)
    (set-circuit-port-powered?! and-circuit and-b #f)
    (circuit-step! and-circuit)
    (check-equal? (circuit-port-powered? and-circuit and-out) #f)

    (circuit-reset! and-circuit)
    (set-circuit-port-powered?! and-circuit and-a #t)
    (set-circuit-port-powered?! and-circuit and-b #t)
    (circuit-step! and-circuit)
    (check-equal? (circuit-port-powered? and-circuit and-out) #t)

    (circuit-reset! and-circuit)
    (set-circuit-port-powered?! and-circuit and-a #f)
    (set-circuit-port-powered?! and-circuit and-b #t)
    (circuit-step! and-circuit)
    (check-equal? (circuit-port-powered? and-circuit and-out) #f)))

; Circuit -> Void
; Run the circuit until it stabilizes (everything stops changing).
; Not all circuits will stabilize. In this case, this procedure will not terminate.
(define (circuit-run! circ)
  (let loop ([old-powereds (circuit-powered-ports circ)])
    (circuit-step! circ)
    (define new-powereds (circuit-powered-ports circ))
    (unless (equal? old-powereds new-powereds)
        (loop new-powereds))))

; Circuit -> Void
; Step the circuit.
; Update each output according to its current inputs and logic gate procedure.
; Update each input according to the output(s) connected to it and their NEW values.
(define (circuit-step! circ)
  (define powered-outputs
    (for/seteq ([gat (circuit-gates circ)]
                #:when (circuit-gate-run circ gat))
      (gate-output gat)))
  (define powered-inputs
    (for/fold ([powered-inputs (seteq)])
              ([out powered-outputs])
      (define ins (for/seteq ([in (circuit-output-children circ out)]) in))
      (set-union powered-inputs ins)))
  (define new-powereds (set-union powered-outputs powered-inputs))
  (set-circuit-powered-ports! circ new-powereds))

; Power off all ports in the circuit
(define (circuit-reset! circ)
  (set-circuit-powered-ports! circ (seteq)))

; Circuit Gate -> Boolean
; Should the gate's output be powered based on its inputs?
; Runs the gate's procedure with the current values of its input ports.
(define (circuit-gate-run circ gat)
  (match-define (gate _ inputs _ proc) gat)
  (apply proc (for/list ([in inputs]) (circuit-port-powered? circ in))))

; Circuit OutputPort -> (Listof InputPort)
; Finds the inputs that the given output is directly connected to through wires
(define (circuit-output-children circ out)
  (for/list ([wir (circuit-wires circ)]
             #:when (eq? out (wire-output wir)))
    (wire-input wir)))

; Circuit Gate -> Boolean
; Is the gate's output powered?
(define (circuit-gate-powered? circ gat)
  (circuit-port-powered? circ (gate-output gat)))

; Circuit Port -> Boolean
; Is the port powered?
(define (circuit-port-powered? circ prt)
  (set-member? (circuit-powered-ports circ) prt))

; Circuit Port Boolean -> Void
; Power the port on or off.
(define (set-circuit-port-powered?! circ prt powered?)
  (define powereds (circuit-powered-ports circ))
  (set-circuit-powered-ports! circ
                              (if powered?
                                  (set-add powereds prt)
                                  (set-remove powereds prt))))

(define-syntax-rule
  (circuit-debug circ prt ...)
  (begin
    (displayln (format "~a: ~a" 'prt (circuit-port-powered? circ prt)))
    ...))

(module+ test
  (test-case "clock stepping"
    ; clock that changes every other tick
    ; can make a 1-tick clock by hooking this up to an xor
    (define in (input-port 'in))
    (define out (output-port 'out))
    (define not-gate (gate 'not (list in) out not))
    (define clock (circuit (list not-gate) (list (wire out in)) (seteq)))
    (check-equal? (circuit-port-powered? clock out) #f)
    (check-equal? (circuit-port-powered? clock in) #f)

    (circuit-step! clock)
    (check-equal? (circuit-port-powered? clock out) #t)
    (check-equal? (circuit-port-powered? clock in) #t)

    (circuit-step! clock)
    (check-equal? (circuit-port-powered? clock out) #f)
    (check-equal? (circuit-port-powered? clock in) #f)

    (circuit-step! clock)
    (check-equal? (circuit-port-powered? clock out) #t)
    (check-equal? (circuit-port-powered? clock in) #t)

    (circuit-step! clock)
    (check-equal? (circuit-port-powered? clock out) #f)
    (check-equal? (circuit-port-powered? clock in) #f))
  (test-case "nand"
    (define a (input-port 'a))
    (define b (input-port 'b))
    (define and-out (output-port 'and-out))
    (define not-in (input-port 'not-in))
    (define out (output-port 'out))
    (define and-gate (gate 'and (list a b) and-out (lambda (a b) (and a b))))
    (define not-gate (gate 'not (list not-in) out not))
    (define nand (circuit (list and-gate not-gate)
                          (list (wire and-out not-in))
                          (seteq)))

    (set-circuit-powered-ports! nand (seteq a b))
    (circuit-step! nand)
    (check-equal? (circuit-powered-ports nand)
                  (seteq and-out not-in out))
    (circuit-step! nand)
    (check-equal? (circuit-powered-ports nand)
                  (seteq))
    (circuit-step! nand)
    (check-equal? (circuit-powered-ports nand)
                  (seteq out))

    (circuit-step! nand)
    (check-equal? (circuit-powered-ports nand)
                  (seteq out))))

; Circuit ... -> Circuit
(define (circuit-union . circs)
  (for/fold ([u (circuit (list) (list) (seteq))])
            ([circ circs])
    (circuit-union/bin u circ)))

; Circuit Circuit -> Circuit
(define (circuit-union/bin u circ)
  (define powereds (mutable-seteq))
  (set-union! powereds (circuit-powered-ports u) (circuit-powered-ports circ))
  (circuit (append (circuit-gates u) (circuit-gates circ))
           (append (circuit-wires u) (circuit-wires circ))
           powereds))

; Circuit -> Datum
; for debugging
(define (circuit->datum circ)
  (list 'circuit
        (cons 'gates (for/list ([gat (circuit-gates circ)])
                       (gate->datum gat)))
        (cons 'powered-ports (for/list ([prt (circuit-powered-ports circ)])
                               (object-name prt)))
        (cons 'wires (for/list ([wir (circuit-wires circ)])
                       (wire->datum wir)))))

; Gate -> Datum
; for debugging
(define (gate->datum gat)
  (list (object-name gat) (append (for/list ([prt (gate-inputs gat)]) (object-name prt))
                                  '(->)
                                  (list (object-name (gate-output gat))))))

; Wire -> Datum
; for debugging
(define (wire->datum wir)
  (list (object-name (wire-output wir))
        '->
        (object-name (wire-input wir))))
