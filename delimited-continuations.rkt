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
  ((eval (cps-transform (desugar expr)) ns) empty-continuation))

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
     '(lambda (k-cc)
        (k-cc
         (lambda (f k)
           (f (lambda (val cont) (k val))
              k))))]
    ['call-with-composable-continuation
     ; the difference is we actually use cont on the result of k
     ; so k doesn't abort
     '(lambda (k-cc)
        (k-cc
         (lambda (f k)
           (f (lambda (val cont) (cont (k val)))
              k))))]
    [`(reset ,expr)
     ; stole rules from https://www.deinprogramm.de/sperber/papers/shift-reset-direct.pdf
     ; I had reset right, but shift was a little off.
     (define k (gensym 'k-reset))
     (define expr^ (cps-transform expr))
     `(lambda (,k)
        (,k (,expr^ (wrap-continuation ,k (lambda (x) x)))))]
    [`(shift ,user-k ,expr)
     (define k (gensym 'k-shift))
     (define expr^ (cps-transform expr))
     ; k is the continuation of the shift expression.
     ; user-k is the identifier in the source program which we bind to the delimited current continuation.
     ; val is the argument provided to user-k.
     ; cont is the continuation of the application of user-k.
     ; It's like call/cc/use, except we give it identity instead of k so the shift escapes to the reset.
     ; We call cont on (,k val) so calling user-k doesn't escape the shift.
     ; We give apply expr^ to identity so the final result of the shift escapes out to the reset.
     ; The actual continuation of the shift expression is only used by user-k. We don't use it to continue. We use identity instead.
     `(lambda (,k) ((let ([,user-k (lambda (val cont) (cont (,k val)))]) ,expr^) (wrap-continuation ,k (lambda (x) x))))]
    [`(dynamic-wind ,pre-thunk-expr ,value-thunk-expr ,post-thunk-expr)

     'todo]
    ['void
     ; if they define a variable called void, this will break
     '(lambda (k-void) (k-void (lambda args ((last args) (void)))))]
    [`(set! ,x ,expr)
     (define k (gensym 'k-set!))
     `(lambda (,k) ,(with-binding k `(,k (set! ,x ,(bind expr)))))]
    ['add1
     `(lambda (k-add1) (k-add1 (lambda (n cont) (cont (add1 n)))))]
    ['list
     '(lambda (k-list) (k-list (lambda args ((last args) (all-but-last args)))))]
    ['vector
     '(lambda (k-vector) (k-vector (lambda args ((last args) (list->vector (all-but-last args))))))]
    ['make-parameter
     '(lambda (k-make-parameter)
        (k-make-parameter (lambda (v-default k)
                            (define p
                              (case-lambda
                                [(cont) (cont (continuation-get-parameter cont p))]
                                [(new-val cont)
                                 (continuation-set-parameter! cont p new-val)
                                 (cont (void))]))
                            (k p))))]
    [`(parameterize ([,e-p ,e-new]) ,e)
     (define k (gensym 'k-parameterize))
     `(lambda (,k) ,(with-binding k `(,(cps-transform e-new)
                                      (continuation-set-parameter ,k
                                                                  ,(bind e-p)
                                                                  ,(bind e-new)))))]
    [`(if ,cnd ,thn ,els)
     (define k (gensym 'k-if))
     (define thn^ (cps-transform thn))
     (define els^ (cps-transform els))
     `(lambda (,k)
        ,(with-binding
           k
           `(if ,(bind cnd)
                (,thn^ ,k)
                (,els^ ,k))))]
    [`(lambda ,args ,body)
     (define k (gensym 'k-lam))
     (define cont (gensym 'cont))
     (define body^ (cps-transform body))
     `(lambda (,k) (,k (lambda (,@args ,cont) (,body^ ,cont))))]
    [`(,f ,xs ...)
     (define k (gensym 'k-app))
     `(lambda (,k) ,(with-binding k (append (map bind (cons f xs)) (list k))))]
    [_
     (define k (gensym 'k-const))
     `(lambda (,k) (,k ,expr))]))

; an expression for the current continuation (just an expression, i'm not cheating!)
(define current-k (make-parameter #f))
(define-syntax-rule (with-binding k body ...) (with-binding^ (parameterize ([current-k k]) (with-binding^ body ...))))

; transforms and binds the expressions according to cps.
; bind adds a binding around the inner result and returns the variable it gets bound to.
; Ex:
#;(with-binding (f (bind e1) (bind e2)))
;~>
#;`(,e1^
    (lambda (v1)
      (,e2^
       (lambda (v2)
         ,(f 'v1 'v2)))))
(define-algebraic-effect with-binding^
  ; that's right, we're compiling continuations with continuations!!!
  [(bind expr k)
   (define v (gensym 'v-bind))
   (define expr^ (cps-transform expr))
   `(,expr^ (wrap-continuation ,(current-k) (lambda (,v) ,(k v))))])

; TODO lift primitives like +
; TODO lift higher order stuff like map such that you can do call/cc during map.
; TODO parameters

; runtime

(struct continuation [proc marks] #:property prop:procedure (struct-field-index proc))
; where
; proc is a (any/c -> any/c)
; marks is a hasheq from any/c to any/c

; parameters are implemented by mapping themselves to a box of their current value in the marks.

(define empty-continuation (continuation identity (hasheq)))

(define (continuation-get-mark cont key)
  (hash-ref (continuation-marks cont) key (lambda () (error 'continuation-get-mark "mark not found for key ~a" key))))

(define (continuation-set-mark cont key val)
  (struct-copy continuation cont [marks (hash-set (continuation-marks cont) key val)]))

(define (continuation-get-parameter cont key)
  (unbox (continuation-get-mark cont key)))

(define (continuation-set-parameter cont key val)
  (continuation-set-mark cont key (box val)))

(define (continuation-set-parameter! cont key val)
  (set-box! (continuation-get-mark cont key) val))

(define (wrap-continuation cont proc)
  (struct-copy continuation cont [proc proc]))

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
  (teval (let ([p (make-parameter 0)])
           (p)))
  (teval (let ([p (make-parameter 0)])
           (parameterize ([p 1]) (p))))
  ; it's not setting saved-k
  (teval (let ([saved-k #f]
                 [p (make-parameter 0)]
                 [v #f])
             (parameterize ([p 1])
               (if (call/cc (lambda (k) (set! saved-k k) #f))
                   (set! v (p))
                   (void)))
             (if v (void) (saved-k #t))
             v))
  (displayln "got to the end"))

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

- a parameterization is a mapping from parameters to a box of their current value. box is necessary for the (p new-val) mutation.
- a parameter is just its (CPS-land) procedure, can make a struct wrapper if you want. it's a case lambda for the getter and setter.
- expressions are translated to (lambda (k ps) ...) where k is called on the result and ps is the current parameterization
- continuations don't take in a parameterization

[x] = (lambda (k ps) (k x))

[(lambda (x) e)] = (lambda (k ps) (k (lambda (x cont ps^) ([e] cont ps^))))
the lambda gets called with under the parameterization ps^. we evaluate the body under this parameterization.

[(e1 e2)] = (lambda (k ps) ([e1] (lambda (v1) ([e2] (lambda (v2) (v1 v2 k ps)) ps)) ps))

[make-parameter] = (lambda (k^ ps^) (k^ (lambda (v-default k^^) (k^^ (case-lambda [(k ps) (k (parameterization-get ps p v-default))]
                                                                                  [(v k ps)
                                                                                   (parameterization-set! ps p v)
                                                                                   (k (void))])))))

[(parameterize ([p e^]) e)] = (lambda (k ps) ([e^] (lambda (v^) ([e] k (parameterization-set ps p v^))) ps))
TODO test for mutating a parameter in e^. test mutating p and mutating not p. mutating not p should be seen in e

[call/cc] = (lambda (k-cc ps-cc) (k-cc (lambda (f k ps) (f (lambda (val cont ps^) (k val)) ps))))
ps is the parameterization for the application of call/cc. ps^ is the parameterization for the application of k in f.

[call-with-composable-continuation] = (lambda (k-cc ps-cc) (k-cc (lambda (f k ps) (f (lambda (val cont ps^) (cont (k val))) ps))))
same thing but (cont (k val ps) ps^)

When you use k, will it run under the right ps? If k just fills in the hole, then the evaluation of (k val) should be under the "outer" parameterization,
and (cont that) should be under the "inner" parameterization from the body of f. Right?

thinking:
> (define p (make-parameter 0))
> (+ (call/cc (lambda (k) (parameterize ([p 1]) (k 9)))) (p))
9

This will work for sure. But,
> (reset (+ (shift k (parameterize ([p 1]) (k 9))) (p)))
10

Pretend shift is call-with-composable-continuation. shift just simplifies by avoiding resuming twice, but it's the same idea.

The key point is that for call/cc, k needs to forget the parameterization and just jump. But for shift and call-with-composable-continuation, k needs to use the call-site's parameterization.
But these two rewrites handle parameterization the same way: ignoring it! Even if cont "has" ps^, it's too late bc (k val) will already have been evaluated the same way it would in call/cc. one or both are wrong.
This might mean that continuations need to take in a parameterization.

But that makes no sense everywhere else.

Maybe you need continuation marks after all. But then for parameterize to play nicely with shift, it'll need to change the k's marks or something. Or, in shift, you give k cont's marks.
With marks, do you need to have exprs take in ps?

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



marks:

- continuations have marks. parameter values live in the marks
- when you use a value, you need to supply a continuation, not just a lambda. That continuation must inherit the marks of the current continuation
- parameter procedure gets and sets the value using the current continuation
- parameterize runs the body under a continuation with modified marks
- a parameter is a procedure, that case lambda. can wrap in a struct if you want, not necessary.
- in marks, the parameter procedure is mapped to a box. we need a box for mutation. parameterize makes a new box, the procedure set case mutates.

[x] = (lambda (k) (k x))

[(lambda (x) e)] = (lambda (k) (k (lambda (x cont) ([e] cont))))

[(e1 e2)] = (lambda (k) ([e1] (wrap-continuation k (lambda (f) ([e2] (wrap-continuation k (lambda (x) (f x k))))))))

[make-parameter] = (lambda (k) (k (lambda (v-default k^) (letrec ([p (case-lambda [(cont) (cont (continuation-get-mark cont p))] [(v-new cont) (continuation-set-mark! cont p v-new) (cont (void))])]) ((continuation-set-mark k^ p v-default) p)))))

[(parameterize ([p e-new]) e)] = (lambda (k) ([p] (lambda (vp) ([e-new] (lambda (v-new) ([e] (continuation-set-mark k p v-new)))))))
TODO test mutating in p^ too lol
but if marks ride along with the continuation, how do we "pop out"? Does parameterize need sandboxing?
an expr gets the current continuation, which has the current parameterization. but the cc is also what to do with the answer, but when you continue, you don't want the rest of the program to use cc's
parameterization. But when the expr gets a parameter value, it does a field access on the cc, it doesn't call it. When it calls it, the cc's body doesn't use its own marks, so they're gone. you do pop out.

[call/cc] = (lambda (k-cc) (k-cc (lambda (f k) (f (lambda (val cont) (k val)) k))))

[call-with-composable-continuation] = (lambda (k-cc) (k-cc (lambda (f k) (f (lambda (val cont) (cont ((wrap-continuation cont k) val))) k))))

[(reset e)] = (lambda (k-reset) (k-reset ([e] (wrap-continuation k-reset identity))))

[(shift user-k e)] = (lambda (k) ((let ([user-k (lambda (val cont) (cont ((wrap-continuation cont k) val)))]) [e]) (wrap-continuation k identity)))

the inner wrapping makes it so applying k in e uses the parameterization from e. the outer wrapping runs e against the shift's parameterization.

just realized that this won't work
when you wrap in call-with-current-continuation, that doesn't actually do anything bc you're calling k, not passing it. might need to mutate the marks?
can't mutate the marks

having continuations accept a parameterization would solve this, but it doesn't make sense elsewhere.

what actually happens in the current system?
The current continuation is just something that fills in the hole .

(f (call/cc (lambda (k) (k 2))) (p))

(lambda (k-app) ([f] (wrap-continuation k-app (lambda (vf) ([(call/cc (lambda (k) (k 2)))] (wrap-continuation k-app (lambda (x) ([(p)] (wrap-continuation k-app (lambda (y) (vf x y k-app)))))))))))
that second wrapped continuation is what the call/cc body will end up calling. so substitute x with 2. the [(p)] still receives a continuation with k-app's marks, and nothing in the control operator can change that
under the current system.

call/cc will end up working fine (k will "save" the parameterization), but not shift and probably not call-with-composable-continuation either.

read this https://citeseerx.ist.psu.edu/doc/10.1.1.22.7256

doesn't talk about implementation

screw this, i'm doing marks and seeing what happens

default value for the parameter doesn't work because it can't leak out without mutation
this paper is about continuation marks: https://www-old.cs.utah.edu/plt/publications/pldi20-fd.pdf
actually talks about implementation!

watched this video by matthew flatt about the paper https://www.youtube.com/watch?v=lfxsM4TC8Yw&ab_channel=LFCSSeminar
looks like it's equivalent to what i'm doing. marks are immutable and associated
with the continuation, pretty much. it's just that for wrap-continuation, instead of replacing the value and having a single mapping,
it's a list of mappings, one for each frame. a frame corresponds to a wrapping, but you don't keep the old stuff around.

how does it handle doing a default value then? all we get is the continuation, and all we can do is call it. we don't actually have control over the subsequent
evaluation.
is translation-based CPS not capable of expressing this easily? Do I need to make an interpreter?
if you do, rewatch that video. it has nice pictures for the semantics. an interpreter wouldn't even be that bad, but try to figure out translation

is there some way for continuations to take in marks to run under and not break everything? like an optional argument for cases like this?
|#
