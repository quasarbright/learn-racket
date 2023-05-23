#lang racket

; an "interpreter" for a tiny language with delimited continuations
; really just a pre-processing step. Invokes racket's `eval` after transforming
; the source program to cps

; To get the essence of this, look at the rules for lambda, application, call/cc, shift, and reset in cps-transform

(module+ test (require rackunit))
(require racket/control)

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
    #;['call/cc/use
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
     (define expr^ (cps-transform expr))
     (define v (gensym 'v-set!))
     `(lambda (,k) (,expr^ (lambda (,v) (,k (set! ,x ,v)))))]
    ['add1
     `(lambda (k-add1) (k-add1 (lambda (n cont) (cont (add1 n)))))]
    ['list
     '(lambda (k-list) (k-list (lambda args ((last args) (all-but-last args)))))]
    ['vector
     '(lambda (k-vector) (k-vector (lambda args ((last args) (list->vector (all-but-last args))))))]
    [`(if ,cnd ,thn ,els)
     (define k (gensym 'k-if))
     (define vcnd (gensym 'v-cnd))
     (define cnd^ (cps-transform cnd))
     (define thn^ (cps-transform thn))
     (define els^ (cps-transform els))
     `(lambda (,k)
        (,cnd^
         (lambda (,vcnd)
           (if ,vcnd
               (,thn^ ,k)
               (,els^ ,k)))))]
    [`(lambda ,args ,body)
     (define k (gensym 'k-lam))
     (define cont (gensym 'cont))
     (define body^ (cps-transform body))
     `(lambda (,k) (,k (lambda (,@args ,cont) (,body^ ,cont))))]
    [`(,f ,xs ...)
     (define k (gensym 'k-app))
     `(lambda (,k) ,(cps-transform-app (cons f xs) k))]
    [_
     (define k (gensym 'k-const))
     `(lambda (,k) (,k ,expr))]))

; translate function application to cps
; Example:
#;{ (cps-transform-app (list f x y) '() k)
    ->
    (lambda (k)
      (f^
       (λ (vf)
         (x^
          (λ (vx)
            (y^
             (λ (vy)
               (vf vx vy k))))))))}
;; It's like monadic bind, or callbacks
;; (CPS f) gives you a callback which is like
;; "What do you want to do with this?"
;; And you say "I want to do (lambda (vf) ...)"
;; And in the end, you call the function value
;; with all the arguments and the outer k,
;; since functions take in a continuation
; (list-of core-expr) symbol -> cps-expr
(define (cps-transform-app exprs k)
  (define exprs^ (map cps-transform exprs))
  (define vs (map (lambda (_) (gensym 'v-app)) exprs))
  (foldr (lambda (expr^ v body) `(,expr^ (lambda (,v) ,body)))
         (append vs (list k))
         exprs^
         vs))

; TODO lift primitives like +
; TODO lift higher order stuff like map such that you can do call/cc during map

(module+ test
  (define-syntax-rule
    (teval expr)
    (check-equal? (eval/cps 'expr) (eval 'expr ns)))
  (teval (let ([x 1]) x))
  (teval (if #t 1 2))
  (teval (if #f 1 2))
  (teval ((lambda (x) (if x 1 2)) #t))
  (teval (call/cc (lambda (k) 2)))
  (teval (call/cc (lambda (k) (k 2))))
  (teval (call/cc (lambda (k) (let ([x 1] [y (k 3)]) x))))
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
  (teval (let ([k (reset (list (shift k k) 1))]) (vector (k 2) (k 3)))))

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
|#
