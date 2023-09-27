#lang racket

; an "interpreter" for a tiny language with delimited continuations
; really just a pre-processing step. Invokes racket's `eval` after transforming
; the source program to cps

; To get the essence of this, look at the rules for lambda, application, call/cc, shift, and reset in cps-transform

(module+ test (require rackunit))
(require racket/control
         "algebraic-effect-2.rkt")

(define (all-but-last lst)
  (reverse (rest (reverse lst))))

(define-namespace-anchor anc)
(define ns (namespace-anchor->namespace anc))

; expr -> value
(define (eval/cps expr)
  ((eval (cps-transform (desugar expr)) ns) (lambda (x ps) x) 'totally-a-parameterization))

; desugar into core language
; expr -> core-expr
(define (desugar expr)
  (match expr
    [`(let ([,x ,rhs] ...) ,@body)
     (desugar `((lambda ,x ,@body) ,@rhs))]
    [`(let/cc ,k ,@body)
     (desugar `(call/cc (lambda (,k) ,@body)))]
    ['(begin) '(void)]
    [`(begin ,expr) (desugar expr)]
    [`(begin ,@exprs)
     (define vs (map (lambda (_) (gensym 'v-begin)) exprs))
     (desugar `((lambda ,vs ,(last vs)) ,@exprs))]
    [`(lambda ,args ,@body) `(lambda ,args ,(desugar `(begin ,@body)))]
    [`(,exprs ...) (map desugar exprs)]
    [_ expr]))

; translate the program into cps
; invariant:
; cps-ing an expr results in a function that takes in a continuation and
; calls it with the result of evaluating the expr (with the exception of control flow forms)
; core-expr -> cps-expr
(define (cps-transform expr)
  (match expr
    ['call/cc
     ; since f will call k, it needs to have the extra cont argument
     ; even though it will be ignored
     ; k-cc is the continuation for the reference to call/cc
     ; f is the function that receives the current continuation
     ; k is the continuation for the call/cc application (the current continuation)
     ; val is the value to "continue" with
     ; cont is the continuation for the application of k (ignored)
     '(lambda (k-cc ps-cc)
        (k-cc
         (lambda (f k ps)
           (f (lambda (val cont ps^) (k val ps))
              k
              ps))
         ps-cc))]
    ['call-with-composable-continuation
     ; the difference is we actually use cont on the result of k
     ; so k doesn't abort
     '(lambda (k-cc ps-cc)
        (k-cc
         (lambda (f k ps)
           (f (lambda (val cont ps^) (cont (k val ps) ps^))
              k
              ps))
         ps-cc))]
    [`(reset ,expr)
     ; stole rules from https://www.deinprogramm.de/sperber/papers/shift-reset-direct.pdf
     ; I had reset right, but shift was a little off.
     (define k (gensym 'k-reset))
     (define ps (gensym 'ps-reset))
     (define expr^ (cps-transform expr))
     `(lambda (,k ,ps)
        (let-values ([(v ps^)
                      (,expr^ values ,ps)])
          (,k v ps^)))]
    [`(shift ,user-k ,expr)
     (define k (gensym 'k-shift))
     (define ps (gensym 'ps-shift))
     (define expr^ (cps-transform expr))
     ; k is the continuation of the shift expression.
     ; user-k is the identifier in the source program which we bind to the delimited current continuation.
     ; val is the argument provided to user-k.
     ; cont is the continuation of the application of user-k.
     ; It's like call/cc/use, except we give it identity instead of k so the shift escapes to the reset.
     ; We call cont on (,k val) so calling user-k doesn't escape the shift.
     ; We give apply expr^ to identity so the final result of the shift escapes out to the reset.
     ; The actual continuation of the shift expression is only used by user-k. We don't use it to continue. We use identity instead.
     `(lambda (,k ,ps) ((let ([,user-k (lambda (val cont ps^)
                                         (cont (,k val ,ps) ps^))])
                          ,expr^)
                        values
                        ,ps))]
    ['void
     ; if they define a variable called void, this will break
     '(lambda (k-void ps-void) (k-void (lambda args (match args [(list args ... k ps) (k (void) ps)]))
                                       ps-void))]
    [`(set! ,x ,expr)
     (define k (gensym 'k-set!))
     (define ps (gensym 'ps-set!))
     `(lambda (,k ,ps) ,(with-binding ps `(,k (set! ,x ,(bind expr)) (current-ps))))]
    ['add1
     `(lambda (k-add1 ps-add1) (k-add1 (lambda (n cont ps) (cont (add1 n) ps)) ps-add1))]
    ['list
     '(lambda (k-list ps-list) (k-list (lambda args (match args [(list args ... k ps) (k args ps)])) ps-list))]
    ['vector
     '(lambda (k-vector ps-vector) (k-vector (lambda args (match args [(list args ... k ps) (k (list->vector args) ps)])) ps-vector))]
    [`(if ,cnd ,thn ,els)
     (define k (gensym 'k-if))
     (define ps (gensym 'ps-if))
     (define thn^ (cps-transform thn))
     (define els^ (cps-transform els))
     `(lambda (,k ,ps)
        ,(with-binding ps
           `(if ,(bind cnd)
                (,thn^ ,k ,(current-ps))
                (,els^ ,k ,(current-ps)))))]
    [`(lambda ,args ,body)
     (define k (gensym 'k-lam))
     (define ps (gensym 'ps-lam))
     (define ps^ (gensym 'ps^-lam))
     (define cont (gensym 'cont))
     (define body^ (cps-transform body))
     `(lambda (,k ,ps) (,k (lambda (,@args ,cont ,ps^) (,body^ ,cont ,ps^)) ,ps))]
    [`(,f ,xs ...)
     ; TODO ps
     (define k (gensym 'k-app))
     (define ps (gensym 'ps-app))
     `(lambda (,k ,ps) ,(with-binding ps (append (map bind (cons f xs)) (list k (current-ps)))))]
    [_
     (define k (gensym 'k-const))
     (define ps (gensym 'ps-const))
     `(lambda (,k ,ps) (,k ,expr ,ps))]))

(define current-ps (make-parameter #f))

; left off here about to make a macro to take in ps and parameterize around with-binding.
; then bind will thread it and parameterize and the caller can just get the parameter

(define-syntax-rule (with-binding ps body ...) (with-binding^ (parameterize ([current-ps ps]) body ...)))

; transforms and binds the expressions according to cps.
; bind adds a binding around the inner result and returns the variable it gets bound to.
; also takes care of ps using current-ps
; Ex:
; TODO add ps to example
#;(with-binding (f (bind e1) (bind e2)))
;~>
#;`(,e1^
    (lambda (v1 ps1)
      (,e2^
       (lambda (v2 ps2)
         ,(f 'v1 'v2)) ; with ps2 as current-ps
       ps1))
    ps)
(define-algebraic-effect with-binding^
  ; that's right, we're compiling continuations with continuations!!!
  ; and we're compiling parameters with parameters!
  [(bind expr k)
   (define v (gensym 'v-bind))
   (define ps (current-ps))
   (define ps^ (gensym 'ps^-bind))
   (define expr^ (cps-transform expr))
   `(,expr^ (lambda (,v ,ps^) ,(parameterize ([current-ps ps^]) (k v))) ,ps)])

; TODO lift primitives like +
; TODO lift higher order stuff like map such that you can do call/cc during map.
; TODO parameters

(module+ test
  (define-syntax-rule
    (teval expr)
    ; when you eval something with call/cc, the context outside of the eval is included!
    ; this includes the check-equal?
    ; so we need to wrap it in a prompt
    (check-equal? (eval/cps 'expr) (eval `(call-with-continuation-prompt (lambda () expr)) ns)))
  (teval (let ([x 1]) x))
  (teval (add1 1))
  (teval (add1 (add1 (add1 1))))
  (teval (if #t 1 2))
  (teval (if #f 1 2))
  (teval ((lambda (x) (if x 1 2)) #t))
  (teval (call/cc (lambda (k) 2)))
  (teval (call/cc (lambda (k) (k 2))))
  (teval (call/cc (lambda (k) (let ([x 1] [y (k 3)]) x))))
  (teval (add1 (add1 (call-with-composable-continuation (lambda (k) (k 0))))))
  (teval (add1 (add1 (call-with-composable-continuation (lambda (k) (k (k 0)))))))
  (teval (let ([x 3] [k (let/cc k k)])
           (if k (k #f) x)))
  (teval (let ([x 2]) (set! x 3) x))
  (teval (void))
  (teval (void 2 3 4))
  (teval (add1 2))
  (teval (list 1 2))
  (teval (let ([handler (lambda (v k) (k (add1 v)))])
           (add1 (let/cc k (handler 1 k)))))
  (teval (let ([handler (lambda (v k) (vector (k v) (k (add1 v))))])
           (list (let/cc k (handler 1 k)))))
  (teval (reset 2))
  (teval (reset (list (shift k 2))))
  (teval (reset (add1 (shift k (k (k 0))))))
  (teval (reset (list (shift k (vector (k 1) (k 2))))))
  (teval (let ([k (reset (shift k k))]) (add1 (k 1))))
  (teval (let ([k (reset (list (shift k k) 1))]) (vector (k 2) (k 3))))
  (displayln "got to the end"))

; go ahead, find the bug
#;
(lambda (k-reset47319 ps-reset47320)
   (let-values (((v ps^)
                 ((lambda (k-app47321 ps-app47322)
                    ((lambda (k-add1 ps-add1) (k-add1 (lambda (n cont ps) (cont (add1 n) ps)) ps-add1))
                     (lambda (v-bind47323 ps^-bind47324)
                       ((lambda (k-shift47327 ps-shift47328)
                          ((let ((k (lambda (val cont ps^) (cont (k-shift47327 val ps-shift47328) ps^))))
                             (lambda (k-app47329 ps-app47330)
                               ((lambda (k-const47333 ps-const47334) (k-const47333 k ps-const47334))
                                (lambda (v-bind47331 ps^-bind47332)
                                  ((lambda (k-app47337 ps-app47338)
                                     ((lambda (k-const47341 ps-const47342) (k-const47341 k ps-const47342))
                                      (lambda (v-bind47339 ps^-bind47340)
                                        ((lambda (k-const47345 ps-const47346) (k-const47345 0 ps-const47346)) (lambda (v-bind47343 ps^-bind47344) (v-bind47339 v-bind47343 k-app47337 ps-app47338)) ps^-bind47340))
                                      ps^-bind47332))
                                   (lambda (v-bind47335 ps^-bind47336) (v-bind47331 v-bind47335 k-app47329 ps-app47330))
                                   ps^-bind47332))
                                ps^-bind47324)))
                           values
                           ps-shift47328))
                        (lambda (v-bind47325 ps^-bind47326) (v-bind47323 v-bind47325 k-app47321 ps-app47322))
                        ps^-bind47324))
                     #f))
                  values
                  ps-reset47320)))
     (k-reset47319 v ps^)))

#|
playing with parameters and shift reset:


> (require racket/control)
> (define p (make-parameter 'init))
> (define k (parameterize ([p 'out]) (reset (parameterize ([p 'reset]) (shift k (parameterize ([p 'shift]) k))))))
> (k 1)
1
; this one is interesting. think of it as replacing the reset with (p)
> (parameterize ([p 'out]) (reset (parameterize ([p 'reset]) (shift k (p)))))
'out
> (parameterize ([p 'out]) (reset (parameterize ([p 'reset]) (shift k (lambda () (p))))))
#<procedure>
; this one is interesting to compare to the similar one that produces 'out. think of it as ((parameterize ... (lambda () (p)))) -> ((lambda () (p))) -> (p) -> 'init
> ((parameterize ([p 'out]) (reset (parameterize ([p 'reset]) (shift k (lambda () (p)))))))
'init
> (parameterize ([p 'out]) (reset (parameterize ([p 'reset]) (list (shift k (k 1)) (p)))))
'(1 reset)
> (parameterize ([p 'out]) (reset (parameterize ([p 'reset]) (list (shift k k) (p)))))
#<procedure:.../racket/control.rkt:158:23>
> (define k (parameterize ([p 'out]) (reset (parameterize ([p 'reset]) (list (shift k k) (p))))))
> k
#<procedure:.../racket/control.rkt:158:23>
; k restores the parameterization context of the enclosing reset
> (k 1)
'(1 reset)


Racket implements parameters in terms of continuation marks. A continuation can be split into frames, which I think are just the nested lambdas.
As we evaluate, we wrap and unwrap continuations, pushing and popping frames. I think.
Anyway, a continuation mark is a key-value pair, and a continuation frame is associated with a set of continuation marks. It's a key-value store on a frame.
For something like parameters, we'd want child continuations to inherit the parameter mark from its parent, or some way to go "up the stack" to find a value for the mark.
Frames get added (continuations get wrapped) during applications, or generally when using/evaluating exprs, and removed (continuations get applied) when evaluating constants.

Idea for implementation: Instead of pure lambdas, continuations are structs with prop:procedure, and they have marks. When you wrap a continuation, inherit the marks,
unless you're a special form like parameterize which manipulates them. (wrap-continuation k (lambda (v) ...something-with-k...)) creates a continuation from
the lambda which inherits the marks from k.
Inheritance is tricky though. Think through an example with an application. It may not be this simple.

(f (parameterize ([p 1]) (g (p))) y)

(lambda (k) ([f] (lambda (vf) ([(parameterize ([p 1]) (g (p)))] (lambda (x) ([y] (lambda (y) (vf x y k))))))))

parameterize can just put the mark on the continuation it passes to the body.
getting the value later is the tricky bit

(lambda (k) ((lambda (kf) (kf f)) (lambda (vf) ([(parameterize ([p 1]) (g (p)))] (lambda (x) ((lambda (ky) (ky y)) (vf x y k)))))))

[(parameterize ([p 1]) (g (p)))]
(lambda (kparam) ([1] (lambda (one) (let ([k^ (continuation-set-mark kparam p one)]) ([(g (p))] k^)))))
(lambda (kparam) ([1] (lambda (one) (let ([k^ (continuation-set-mark kparam p one)])
                                      ((lambda (kapp) ([g] (lambda (vg) ([(p)] (lambda (vget) (vg vget kapp))))))
                                       k^)))))

[(p)] needs to get the mark from its continuation
the continuation that (p) gets is the (lambda (vget) ...), but the one with the mark is kapp.

instead of plain lambda for continuations, do (wrap-continuation k (lambda (v) ...)). Then (p) will get a continuation with markings.

p needs to be
(case-lambda
  [(k) (k (continuation-get-mark k p))]
  [(v k) (continuation-set-mark! k p v) (k (void))])

I was worried about this mutation spreading too much, but actually, I think it might not spread far enough. Nobody will see the mutated mapping because everything copies.
Idea:
marks map to boxes
wrap-continuation just passes the mapping directly, no copying
continuation-set-mark (parameterize) creates a new hash which replaces the parameter's box with a new one
continuation-set-mark! (p v) mutates the box

I'm worried about a situation where we save a continuation, mutate a parameter, and then jump back to before the mutation.
Should it have the old value, or the new value? see what racket does.

> (define p (make-parameter 1))
> (p)
1
> (let () (define k (let/cc k k)) (displayln (p)) (p (add1 (p))) (when k (k #f)))
1
2

The mutation persists after the jump.

But also,

> (define p (make-parameter 1))
> (define saved-k #f)
> (let () (let/cc k (set! saved-k k) (void)) (p))
1
> (parameterize ([p 2]) (saved-k (void)))
1

TODO tests for these

continuations remember the parameterization that was present

what if continuations took in a value and a mark mapping instead of storing it? then, we wouldn't need mutation. from p, int the (p v) case, we could just
call k with a modified mapping.

This should handle the jump to before mutation thing, I don't think it's compatible with continuations remembering their parameterization at the same time.
I'll have to be carefull with the call/cc rewrite, might be able to make it work.

Could also do something in between. Automate the passing of a hash from parameters to boxes. Sounds equivalent, but might behave slightly differently.
But if continuations are kept in correspondence with their parameterizations, it should be the same, I think. User-accessible continuations will close
over the appropriate parameterization, so it's like a continuation mark.

- a parameterization is a mapping from parameters to their current value. can use hasheq
- a parameter is just its (CPS-land) procedure, can make a struct wrapper if you want. it's a case lambda for the getter and setter.
- expressions are translated to (lambda (k ps) ...) where k is called on the result and the new parameterization, usually just ps.
ps is the parameterization to evaluate the expression under
- continuations take in a value and a parameterization. the meaning is "what to do with the answer and the parameterization to do it under"

[x] = (lambda (k ps) (k x ps))

[(lambda (x) e)] = (lambda (k ps) (k (lambda (x cont ps^) ([e] cont ps^)) ps))
the lambda gets called with under the parameterization ps^. we evaluate the body under this parameterization.

[(e1 e2)] = (lambda (k ps) ([e1] (lambda (v1 ps1) ([e2] (lambda (v2 ps2) (v1 v2 k ps2)) ps1)) ps))
thinking about this:
we evaluate e1 under ps. when it's done, it will call our 1 continuation with its value v1 and a new parameterization ps1.
then, we evaluate e2 under ps1. when it's done, it will call our 2 continuation with its value v2 and a new parameterization ps2.
Finally, we apply the function, passing it k and ps2, so the actual function body will run under ps2.

[(make-parameter default)] = (case-lambda
                               [(k ps)   (k (hash-ref ps p default) ps)]
                               [(v k ps) (k (void)                  (hash-set ps p v))])
CPS default expr ofc, just took a shortcut here in the rule

[(parameterize ([p e^]) e)] = (lambda (k ps) ([e^] (lambda (v^ ps^) ([e] k (hash-set ps^ p v^))) ps))
TODO test for mutating a parameter in e^. test mutating p and mutating not p. mutating not p should be seen in e

[call/cc] = (lambda (k-cc ps-cc) (k-cc (lambda (f k ps) (f (lambda (val cont ps^) (k val ps)) ps)) ps-cc))
ps is the parameterization for the application of call/cc. ps^ is the parameterization for the application of k in f. Since k jumps to
the call/cc application's context, it should use the old parameterization ps.

[call-with-composable-continuation] = (lambda (k-cc ps-cc) (k-cc (lambda (f k ps) (f (lambda (val cont ps^) (cont (k val ps) ps^)) ps)) ps-cc))
same thing but (cont (k val ps) ps^)

[(reset e)] = (lambda (k ps) (let-values ([(v ps^) ([e] (lambda (x ps^) (values v ps^)) ps)]) (k v ps^)))
e runs under ps, but its continuation is sandboxed. This breaks the continuation-parameterization correspondence.
TODO Need to maintain the final parameterization from the body though. Is this right?
TODO Will this play nice with call/cc inside reset?

[(shift user-k e)] = (lambda (k ps) ((let ([user-k (lambda (val cont ps^) (cont (k val ps) ps^))]) [e]) (lambda (x ps^^) (values x ps^^)) ps))
e runs under ps, but its continuation escapes to the reset. This breaks the continuation-parameterization correspondence.
TODO Need to maintain the final parameterization from the body though. Is this right?
This is getting weird. what does it look like with marks?

TODO what happens if you do (shift k (parameterize ... (k ...)))? And how does this play with mutation?

steps:
- add parameterization passing, but no forms that use it. get old tests passing
- get parameters working without mutation
- get mutation working, maybe use boxes

|#
