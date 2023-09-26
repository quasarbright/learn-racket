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
  ((eval (cps-transform (desugar expr)) ns) identity))

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
        (,k (,expr^ identity)))]
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
     `(lambda (,k) ((let ([,user-k (lambda (val cont) (cont (,k val)))]) ,expr^) identity))]
    [`(dynamic-wind ,pre-thunk-expr ,value-thunk-expr ,post-thunk-expr)

     'todo]
    ['void
     ; if they define a variable called void, this will break
     '(lambda (k-void) (k-void (lambda args ((last args) (void)))))]
    [`(set! ,x ,expr)
     (define k (gensym 'k-set!))
     `(lambda (,k) ,(with-binding `(,k (set! ,x ,(bind expr)))))]
    ['add1
     `(lambda (k-add1) (k-add1 (lambda (n cont) (cont (add1 n)))))]
    ['list
     '(lambda (k-list) (k-list (lambda args ((last args) (all-but-last args)))))]
    ['vector
     '(lambda (k-vector) (k-vector (lambda args ((last args) (list->vector (all-but-last args))))))]
    [`(if ,cnd ,thn ,els)
     (define k (gensym 'k-if))
     (define thn^ (cps-transform thn))
     (define els^ (cps-transform els))
     `(lambda (,k)
        ,(with-binding
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
     `(lambda (,k) ,(with-binding (append (map bind (cons f xs)) (list k))))]
    [_
     (define k (gensym 'k-const))
     `(lambda (,k) (,k ,expr))]))

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
(define-algebraic-effect with-binding
  ; that's right, we're compiling continuations with continuations!!!
  [(bind expr k)
   (define v (gensym 'v-bind))
   (define expr^ (cps-transform expr))
   `(,expr^ (lambda (,v) ,(k v)))])

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
  (teval (reset (list (shift k (vector (k 1) (k 2))))))
  (teval (let ([k (reset (shift k k))]) (add1 (k 1))))
  (teval (let ([k (reset (list (shift k k) 1))]) (vector (k 2) (k 3))))
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


what if continuations took in a value and a mark mapping instead of storing it? then, we wouldn't need mutation. from p, int the (p v) case, we could just
call k with a modified mapping. That would behave differently in that weird jump-to-before-mutation case, so if the other strategy doesn't match racket behavior, think about this one.

|#
