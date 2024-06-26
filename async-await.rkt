#lang racket

; something like js promises and async await sugar
; unrelated to racket promises
; see promise-run/async for something close

; I implemented an async runner for promises too, but I think the cool part is the
; desugaring.
; The async runner is totally single threaded with no parallelism or anything.
; But that could be implemented with a thread-safe promise queue I think.
; You'd just call resolve from a future or whatever.

(module+ test (require rackunit))
(require "./algebraic-effect-2.rkt")

; A (Promise X) is one of
(struct promise [body])
; where body is a ((X -> any) -> any) function, where the argument is like js resolve
(struct promise-then [p callback])
; where p is a (Promise Y) and callback is a (Y -> (Promise X))

; I chose an interpretable representation so we could do sync or async if we wanted
; This is essentially the continuation monad.

; X -> (Promise X)
; a promise that immediately resolves to a value
(define (promise-of v) (promise (lambda (resolve) (resolve v))))

; sort of like shift, except it's a promise.
; calling k doesn't return anything to the callback in my current runners.
; calling k doesn't abort.
; k is called with the final result of the body. If you don't want that, use the promise constructor directly.
; In a sense, these continuations are delimited to the enclosing async, so
; (await (async ...)) is reset
(define (shift/promise callback)
  ; basically the promise constructor, but calls resolve on the result of the callback.
  (promise (lambda (k) (k (callback k)))))

; sequence promises one after the other
(define (promise-sequence . ps)
  (for/fold ([p-seq (promise-of (void))])
            ([p ps])
    (promise-then p-seq (const p))))

; lifts plain values to promise-of
(define (ensure-promise p)
  (if (or (promise? p) (promise-then? p))
      p
      (promise-of p)))

; (Promise X) -> X
; synchronously get the (first) resolved value of a promise. error if it doesn't resolve.
(define (promise-force p)
  (match p
    [(promise body)
     (define resolved-v #f)
     (define resolved? #f)
     (body (lambda (v)
             ; only first
             (unless resolved?
               (set! resolved-v v)
               (set! resolved? #t))))
     (if resolved? resolved-v (error 'promise-force "promise never resolved"))]
    [(promise-then p callback)
     (promise-force (callback (promise-force p)))]))

(module+ test
  (define promise-2 (promise-of 2))
  (define promise-2-3 (promise (lambda (resolve) (resolve 2) (resolve 3))))
  (check-equal? (promise-force promise-2)
                2)
  (check-equal? (promise-force promise-2-3)
                2)
  (check-equal? (promise-force (promise-then promise-2 (lambda (v) (promise-of (add1 v)))))
                3)
  (check-equal? (promise-force (promise-then promise-2-3 (lambda (v) (promise-of (sub1 v)))))
                1))

; (Promise X) {(X -> any)} -> any
; synchronously run the promise.
; Doesn't stop after the first resolve.
; optionally takes in a callback that is called with resolved values.
(define (promise-run p [k void])
  (match p
    [(promise body)
     (body k)]
    [(promise-then p callback)
     (promise-run p (lambda (v) (promise-run (callback v) k)))]))

(module+ test
  (define vs '())
  (define k-append-to-vs (lambda (v) (set! vs (append vs (list v)))))
  (define (promise-run-vs p)
    (set! vs '())
    (promise-run p k-append-to-vs)
    vs)
  (check-equal? (promise-run-vs promise-2) '(2))
  (check-equal? (promise-run-vs promise-2-3) '(2 3))
  (check-equal? (promise-run-vs (promise-then promise-2-3
                                              (lambda (v) (promise (lambda (resolve)
                                                                     (resolve (* 5 v))
                                                                     (resolve (* 7 v)))))))
                '(10 14 15 21))
  ; never resolves
  (define promise-never (promise void))
  (check-equal? (promise-run-vs (promise-then
                                 (promise-then
                                  promise-2-3
                                  (lambda (v) (promise (lambda (resolve)
                                                         (resolve (add1 v))
                                                         (resolve (+ 2 v))))))
                                 (lambda (v) promise-never)))
                '()))

; runs them asynchronously
(define (promise-run/async p [k void])
  ; queue of promises to fulfill
  (define promises (list p))
  ; queue of callbacks corresponding to promises. they get called with the resolved value(s)
  ; k stands for continuation lol
  (define ks (list k))
  (define (pop!)
    (define p (first promises))
    (define k (first ks))
    (set! promises (rest promises))
    (set! ks (rest ks))
    (values p k))
  ; push to end
  (define (push! p k)
    (set! promises (append promises (list p)))
    (set! ks (append ks (list k))))
  ; push to next
  (define (push-next! p k)
    (set! promises (cons p promises))
    (set! ks (cons k ks)))
  (let loop ()
    (unless (empty? promises)
      (define-values (p k) (pop!))
      (match p
        [(promise body)
         (body k)]
        [(promise-then p callback)
         ; "peel off" a layer from the "then"
         ; and move the callback into k^
         ; the inner promise's resolutions will push to the end of the queue
         (define (k^ v) (push! (callback v) k))
         ; push to next bc this promise's inner body hasn't run yet
         (push-next! p k^)])
      (loop))))

(module+ test
  (define (promise-run/async-vs p)
    (set! vs '())
    (promise-run/async p k-append-to-vs)
    vs)
  (check-equal? (promise-run/async-vs promise-2) '(2))
  (check-equal? (promise-run/async-vs promise-2-3) '(2 3))
  (check-equal? (promise-run/async-vs (promise-then promise-2-3
                                              (lambda (v) (promise (lambda (resolve)
                                                                     (resolve (* 5 v))
                                                                     (resolve (* 7 v)))))))
                '(10 14 15 21))
  (check-equal? (promise-run/async-vs (promise-then
                                 (promise-then
                                  promise-2-3
                                  (lambda (v) (promise (lambda (resolve)
                                                         (resolve (add1 v))
                                                         (resolve (+ 2 v))))))
                                 (lambda (v) promise-never)))
                '()))

; compiler

; simple sexpr preprocessor for a racket subset that supports async await

; An Expr is one of
; symbol?
; (async Expr ...)                   like a begin. whole thing becomes a promise
; (await Expr)
; (lambda (symbol? ...) Expr ...)
; (let ([symbol? Expr]) Expr ...)
; (if Expr Expr Expr)
; (Expr ...)                         application

(define-namespace-anchor anc)
(define ns (namespace-anchor->namespace anc))
(define (eval/async expr)
  (eval (desugar expr) ns))

; Expr -> Expr
; desugars async await to promises
; uses alpha normal form (ANF) https://en.wikipedia.org/wiki/A-normal_form
; inside async, but await binds variables with promise-then instead of let
(define (desugar expr)
  (match expr
    [`(async ,exprs ...) (desugar/async* exprs)]
    [`(await . ,_) (error 'desugar "can't use await outside of async")]
    [`(lambda ,args ,body ...)
     `(lambda ,args ,@(map desugar body))]
    [`(let ([,x ,rhs]) ,body ...)
     (desugar `((lambda (,x) ,@body) ,rhs))]
    [`(if ,cnd ,thn ,els)
     `(if ,(desugar cnd) ,(desugar thn) ,(desugar els))]
    ; application
    [(? cons? exprs) (map desugar exprs)]
    ; variable/constant
    [_ expr]))

; (listof Expr) -> Expr
; desugar an async block
(define (desugar/async* exprs)
  (define exprs^ (for/list ([expr exprs])
                   `(ensure-promise ,(desugar/async expr))))
  `(promise-sequence ,@exprs^))

; Expr -> Expr
; desugar an expression in async
(define (desugar/async expr)
  ; we use continuations to translate to ANF, which can be confusing.
  ; But the code is concise, at least.
  ; we are building a nesting of bindings to simple things and then something simple in the inner body
  ; 'if' is an exception to this, but it's fine.
  ; the bind effects add a binding (either a let binding or a promise-then lambda binding) around
  ; the eventual answer and return the variable that the expression gets bound to.
  ; Only bind to simple expressions (ones that don't have an await that we need to deal with).
  ; loop desugars an expression, adding bindings around us, and returns what it gets bound to.
  ; if it's a complicated expression use loop. if its simple, use a bind effect.
  (anf (let loop ([expr expr])
         (match expr
           [`(let ([,x ,rhs]) ,body)
            ; TODO handle multiple bodies
            (lift (list x (loop rhs)))
            (loop body)]
           [(cons 'lambda _)
            (let-bind (desugar expr))]
           [`(await ,expr)
            (promise-bind (loop expr))]
           [`(if ,cnd ,thn ,els)
            ; this is cheating but whatever
            ; you either have to cheat, or thread what comes next into both branches or something
            ; you could make a new effect ig, but avoid duplicating what comes next.
            ; I think the effect would need to loop lol
            (promise-bind `(if ,(loop cnd) ,(desugar `(async ,thn)) ,(desugar `(async ,els))))]
           ; application
           [(? cons? exprs)
            (let-bind (map loop exprs))]
           ; variable/constant, await, lambda, or let
           [_ expr]))))

; I think this is what they do in "compiling with continuations".
; generates an expression that binds the subexpressions you bind
; and replaces each call to bind with the name the expression gets bound to.
; Example:
; (anf (f (let-bind expr))) ~> `(let ([x ,expr]) ,(f 'x))
(define-algebraic-effect anf
  [(let-bind expr k)
   (match expr
     [(? cons?)
      (define x (gensym 'let-x))
      `(let ([,x ,(desugar expr)]) ,(k x))]
     ; it's a constant, don't bother
     [_ (k expr)])]
  [(promise-bind expr k)
   (define x (gensym 'then-x))
   `(promise-then ,(desugar expr) (lambda (,x) (ensure-promise ,(k x))))]
  ; call with (list var constant)
  [(lift binding k)
   `(let (,binding) ,(k (first binding)))])

; direct implementation of async await as an algebraic effect

(define-algebraic-effect async
  #:body-wrapper (lambda (thnk) (ensure-promise (thnk)))
  [(await p k)
   ; this shows that promises are just CPS
   (promise-then p k)])
; comparing this to our anf, the implementation of binding an await looks
; like an eta expansion of this effect if you squint. this is no coincidence.
; we don't have to do let-binding anf because the racket compiler "anfs"
; for us and we're just hooking into continuations. racket actually does
; cps instead of anf of course, but that accomplishes the same thing as our anf:
; controlling evaluation order and binding expressions to variables.

(module+ test
  ; expect a list of all resolved values
  ; tests the sexpr implementation and the direct implementation
  (define-syntax-rule (teval expr vs)
    (begin
      (check-equal? (promise-run-vs (ensure-promise expr)) vs)
      (check-equal? (promise-run-vs (ensure-promise (eval/async 'expr))) vs)))
  (teval (async (+ (await (promise-of 2)) 3))
         '(5))
  (teval (let ([plus1 (lambda (x) (async (+ (await (promise-of 1)) x)))])
            (async (list (await (plus1 1)) (await (plus1 5)))))
         '((2 6)))
  ; use async instead of promise-of
  (teval (let ([plus1 (lambda (x) (async (+ (await (async 1)) x)))])
            (async (list (await (plus1 1)) (await (plus1 5)))))
         '((2 6)))
  ; simple if with await cnd
  (teval (async (if (await (async #t)) 1 (/ 1 0)))
         '(1))
  ; await in an if
  (teval (async (if (await (async #t)) (await (async 1)) (/ 1 0)))
         '(1))
  ; await in an if in a call
  (teval (async (add1 (if (await (async #t)) (await (async 1)) (/ 1 0))))
         '(2))
  ; deep await
  (teval (async (add1 (add1 (* (await (async 3)) 5))))
         '(17))
  ; await in await
  (teval (async (+ 1 (await (promise-of (await (async 2))))))
         '(3))
  ; let in async
  (teval (async (+ (let ([x (await (async 1))]) (+ x (await (async 2)))) 3))
         '(6)))
