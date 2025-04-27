#lang racket

; a little type checker/interpreter for a dependently typed language
; initially taken from https://www.andres-loeh.de/LambdaPi/LambdaPi.pdf
; but expanded on in several ways
; booleans (with dependent if)
; "jit type checking" (not sure what the actual name for this is)

; TODO add naturals
; TODO add vectors
; TODO add staging so there is an environment for evaluations during type checking
#;
(let-for-type ([x (lambda ...)])
  (define y : (x Number)
    ...))
;; TODO even better, support that with just let. there'd be no separation between checking-time and evaluation-time
;; Just-in-time type checking lol
;; you'll need types as values for (let ([x Bool]) (: #t x))
;; TODO more convenient syntax for lambda annotation
;; TODO remove boolElim? pretty sure you could just do the same thing with a lambda and if
;; TODO recursion with termination checking

;; surface syntax

; An Expr is one of
; '*                               (the kind of types)
; (forall (: symbol Expr) Expr)    (dependent function type)
; symbol                           (variable)
; (: Expr Expr)                    (type annotaation)
; (lambda (symbol) Expr)
; (let [(symbol Expr)] Expr)
; (Expr Expr)
; #t
; #f
; (if Expr Expr Expr)
; (boolElim Expr Expr Expr Expr)   (dependent if)
; Represents the surface syntax of a program as an s-expression

; The meaning of (forall (: x t1) t2) is a function type analogous to (t1 -> t2).
; It can more clearly be written as (x : t1) -> t2
; t1 is the type of value that gets passed in for x. t2 is the return type.
; But t2 can depend on the _value_ of x.
; Dependent example:
; (n : Nat) -> StringVec n
; (forall (: n Nat) (StringVec n))
; that takes in a natural number and then returns a string vector of that length, which is statically checked.
; ordinary functions like Nat -> Bool are a special case where the return type
; does not depend on the argument value: (forall (: x Nat) Bool)
; more examples
; identity : (forall (: a *) (forall (: x a) a))
; requires explicit type application: ((identity Bool) #t) ~> #t
; const : (forall (: a *) (forall (: b *) (forall (_ : a) (forall (_ : b) a))))
; ((((const Bool) Nat) #t) 1) ~> #t

;; runtime

; A Value is one of
; #t
; #f
; '*                                (the kind of types)
; 'Bool                             (the type of booleans)
; (Value -> Value)                  (function value)
(struct pi [t-x x->t-ret]);         (dependent function type)
;; where
;; t-x is a Type
;; x->t-ret is a Value -> Type
; NeutralExpr                       (irreducible expression)
; Represents a value from evaluating an expression.
; Function types are represented by Racket functions

; A Type is a Value

; A NeutralExpr is one of
; symbol
; (list NeutralExpr Value)                        (application)
; (list 'if NeutralExpr Value Value)
; (list 'boolElim Expr NeutralExpr Value Value)   (dependent if)
;;                ^ expr because it's only relevant to type-checking
; Represents an irreducible expression

; An Env is a (hash symbol Value)
(define empty-env (hasheq))

; A Context is a (hash symbol (or Type Kind))
; mapping to type is for term variables, mapping to kind is for type variables. don't worry about collision for now
(define empty-ctx (hasheq))

(module+ test (require (except-in rackunit check)))

;; Expr Ctx Env -> Expr
;; infers the type and evaluates it
(define (run expr ctx env)
  (define t (quote-value (infer expr ctx)))
  (define v (normalize expr env))
  `(: ,v ,t))

(module+ test
  (check-equal? (run '(if #t #t #f) empty-ctx empty-env)
                '(: #t Bool))
  (check-equal? (run '(: (lambda (x) x)
                         (forall (: x Bool) Bool)) empty-ctx empty-env)
                '(: (lambda (_.0) _.0)
                    (forall (: _.0 Bool) Bool))))

; Expr -> Expr
; reduce an expression to its canonical form.
; note that the result is an expression.
; any beta or alpha equivalent expressions should normalize to the same expression.
(define (normalize expr [env empty-env]) (quote-value (eval expr env)))

(module+ test
  (check-equal? (normalize '(let ([x (lambda (y) y)]) (x x)))
                '(lambda (_.0) _.0)))

; Expr -> Value
(define (eval expr env)
  (match expr
    ['* '*]
    [(? symbol? x) (hash-ref env x x)]
    [(? boolean? b) b]
    [`(: ,expr ,_) (eval expr env)]
    [`(lambda (,x) ,body)
     (lambda (v-x) (eval body (hash-set env x v-x)))]
    [`(let [(,x ,rhs)] ,body)
     (define v-rhs (eval rhs env))
     (eval body (hash-set env x v-rhs))]
    [`(forall (: ,x ,p-x) ,p-ret)
     ; remember, p-x and p-ret are expressions
     ; p-x is (an expression for) the type of x
     ; p-ret can depend on the _value_ of x
     (define t-x (eval p-x env))
     (pi t-x (lambda (v-x) (eval p-ret (hash-set env x v-x))))]
    [`(if ,cnd ,thn ,els)
     (match (eval cnd env)
       [#t (eval thn env)]
       [#f (eval els env)]
       [n
        ;; neutral case, evaluate branches as much as we can
        ;; we're type-checked, so we don't have to worry about
        ;; it being a non-bool!
        `(if ,n
             ,(eval thn env)
             ,(eval els env))])]
    [`(boolElim ,m ,cnd ,thn ,els)
     (match (eval cnd env)
       [#t (eval thn env)]
       [#f (eval els env)]
       [n
        ;; neutral case, evaluate branches as much as we can
        ;; we're type-checked, so we don't have to worry about
        ;; it being a non-bool!
        `(boolElim ,m ,n
           ,(eval thn env)
           ,(eval els env))])]
    [`(,rator ,rand)
     (match (eval rator env)
       [(and f (? procedure?)) (f (eval rand env))]
       [(or '* (pi _ _)) (error 'eval "bad application")]
       [n
        ;; neutral
        `(,n ,(eval rand env))])]))

; Value -> Expr
(define (quote-value v)
  (define count 0)
  ;; generates values like '_.0, '_.1, ...
  (define (my-gensym)
    (begin0 (number->var count)
      (set! count (add1 count))))
  (let loop ([v v])
    (match v
      ['* '*]
      [(? symbol?) v]
      [(? boolean?) v]
      [`(,n-rator ,v-rand)
       `(,(loop n-rator) ,(loop v-rand))]
      [`(boolElim ,m ,n-cnd ,v-thn ,v-els)
       `(boolElim ,m ,(loop n-cnd) ,(loop v-thn) ,(loop v-els))]
      [(pi t-arg arg->t-ret)
       (define x (my-gensym))
       `(forall (: ,x ,(loop t-arg))
                ,(loop (arg->t-ret x)))]
      [(? procedure?)
       (define x (my-gensym))
       `(lambda (,x) ,(loop (v x)))])))

(module+ test
  (check-equal? (quote-value 'x) 'x)
  (check-equal? (quote-value '(x y)) '(x y))
  (check-equal? (quote-value `((x ,(lambda (y) y)) z))
                             '((x (lambda (_.0) _.0)) z))
  (check-equal? (quote-value `(boolElim m b ,(lambda (x) x) ,(lambda (x) #t)))
                             '(boolElim m b (lambda (_.0) _.0) (lambda (_.1) #t)))
  (check-equal? (quote-value (lambda (x) x)) '(lambda (_.0) _.0))
  (check-equal? (quote-value (lambda (x) (lambda (y) x)))
                '(lambda (_.0) (lambda (_.1) _.0)))
  (check-equal? (quote-value '*) '*)
  ; type of the identity function
  ; (forall (: a *) (forall (: x a) a))
  (check-equal? (quote-value (pi '* (lambda (a) (pi a (lambda (x) a)))))
                '(forall (: _.0 *) (forall (: _.1 _.0) _.0))))

;; Natural -> symbol
;; like minikanren
(define (number->var n)
  (string->symbol (format "_.~a" n)))

(module+ test
  (check-equal? (number->var 0) '_.0))

; Expr Context -> Type
(define (infer expr ctx)
  (match expr
    ['* '*]
    ['Bool '*]
    [(? symbol? x)
     (hash-ref ctx x (lambda () (error 'infer "unbound variable: ~a" x)))]
    [(? boolean? b) 'Bool]
    [`(: ,e ,p)
     (check p '* ctx)
     (define t (eval p empty-env))
     (check e t ctx)
     t]
    [`(forall (: ,x ,p-x) ,p-ret)
     (check p-x '* ctx)
     (define t-x (eval p-x empty-env))
     (check p-ret '* (hash-set ctx x t-x))
     '*]
    [`(let ([,x ,rhs]) ,body)
     (define t-rhs (infer rhs ctx))
     (infer body (hash-set ctx x t-rhs))]
    [(list lambda _ _) (error 'infer "cannot infer type of lambda")]
    [`(if ,cnd ,thn ,els)
     (check cnd 'Bool ctx)
     (define t (infer thn ctx))
     (check els t ctx)
     t]
    [`(boolElim ,m ,cnd ,thn ,els)
     ;; conceptually,
     ;; boolElim : (m : Bool -> *) (cnd : Bool) (thn : m #t) (els : m #f) -> m cnd
     ;; where m is called the "motive"
     ;; it's a way for the type to depend on the value condition
     (check m (pi 'Bool (lambda (_) '*)) ctx)
     (define b->t (eval m empty-env))
     (check cnd 'Bool ctx)
     (check thn (b->t #t) ctx)
     (check els (b->t #f) ctx)
     (define b (eval cnd empty-env))
     (b->t b)]
    [`(,rator ,rand)
     (define t-rator (infer rator ctx))
     (match t-rator
       [(pi t-rand rand->t-ret)
        (check rand t-rand ctx)
        ; this leads to re-evaluations and doesn't work as expected for variables
        ; TODO test that
        (define v-rand (eval rand empty-env))
        (rand->t-ret v-rand)]
       [_ (error 'infer "applied non-function: ~a" t-rator)])]))

; Expr Type Context -> Void
(define (check expr t-expected ctx)
  (match expr
    [`(lambda (,x) ,body)
     (match t-expected
       [(pi t-x x->t-ret)
        ; pass a neutral x to the function
        ; kind of weird. can this break?
        ; TODO test that
        (check body (x->t-ret x) (hash-set ctx x t-x))]
       [_ (error 'check "mismatch. expected a function type")])]
    [_
     (define t-inferred (infer expr ctx))
     (unless (same-value? t-expected t-inferred) (error 'check "mismatch. expected a ~a but got a ~a"
                                                        (quote-value t-expected)
                                                        (quote-value t-inferred)))]))

;; Value Value -> Boolean
(define (same-value? v1 v2)
  (equal? (quote-value v1)
          (quote-value v2)))

(module+ test
  (define ctx (hasheq 'unit 'Unit 'Unit '*))
  (check-equal? (eval 'x empty-env) 'x)
  (check-equal? (eval 'x (hasheq 'x 'y)) 'y)
  (check-equal? (normalize '(lambda (x) x)) '(lambda (_.0) _.0))
  (check-equal? (eval '((lambda (x) x) y) empty-env) 'y)
  (check-equal? (eval '(let ([x y]) x) empty-env) 'y)
  (check-equal? (normalize '(let ([x #t]) (lambda (x) x)))
                '(lambda (_.0) _.0))
  (check-equal? (infer #t ctx) 'Bool)
  (check-equal? (check #t 'Bool ctx) (void))
  (check-equal? (check '(lambda (x) x) (pi 'Bool (const 'Bool)) ctx) (void))
  (check-equal? (quote-value
                 (infer '(: (lambda (x) x)
                            (forall (: x Bool) Bool))
                        ctx))
                '(forall (: _.0 Bool) Bool))
  (check-equal? (infer '((: (lambda (x) x) (forall (: x Bool) Bool)) #t) ctx) 'Bool)
  (check-equal? (infer '(((: (lambda (x) (lambda (y) x))
                             (forall (: x a) (forall (: y b) a)))
                          i)
                         j)
                       (hasheq 'a '*
                               'b '*
                               'i 'a
                               'j 'b))
                'a)
  ; identity function for bools
  (check-equal? (infer '(((: (lambda (a) (lambda (x) x))
                             (forall (: a *) (forall (: x a) a)))
                          Bool)
                         #t)
                       ctx)
                'Bool)
  (check-equal? (check '(: (lambda (a) (lambda (x) x))
                           (forall (: a *) (forall (: x a) a)))
                       (pi '* (lambda (a) (pi a (lambda (x) a))))
                       empty-ctx)
                (void))
  (check-equal? (infer '(let ([id (: (lambda (a) (lambda (x) x))
                                     (forall (: a *) (forall (: x a) a)))])
                          ((id Bool) #t))
                       ctx)
                'Bool)
  ;; if
  (check-equal? (run '(if #t unit unit) ctx empty-env)
                '(: unit Unit))
  (check-equal? (infer '(boolElim (lambda (b) Unit) #t unit unit)
                       ctx)
                'Unit)
  ;; non-trivial dependent if
  (check-equal? (run '(boolElim (lambda (b) (boolElim (lambda (b) *) b Unit Bool)) #t unit #f)
                     ctx
                     empty-env)
                '(: unit Unit))
  ;; the other branch
  (check-equal? (run '(boolElim (lambda (b) (boolElim (lambda (b) *) b Unit Bool)) #f unit #t)
                     ctx
                     empty-env)
                '(: #t Bool))
  ;; neutral condition
  (check-equal? (infer '(boolElim (lambda (b) (boolElim (lambda (b) *) b Unit Bool)) cnd unit #t)
                       (hash-set ctx 'cnd 'Bool))
                '(boolElim (lambda (b) *) cnd Unit Bool))
  (check-equal? (eval '(boolElim m #t a b)
                      empty-env)
                'a)
  (check-equal? (eval '(boolElim m b t e) empty-env)
                '(boolElim m b t e))
  ;; closures work with neutrals by normalized substitution
  (check-equal? (normalize '(let ([x #t])
                              (: (lambda (y) x)
                                 (forall (: z Unit) Boolean))))
                '(lambda (_.0) #t))
  ;; type checking really does normalize
  (check-equal? (quote-value
                 (infer '(: (: (lambda (x) x)
                               (forall (: y Bool) Bool))
                            (forall (: z Bool) Bool))
                        ctx))
                '(forall (: _.0 Bool) Bool))
  ;; for jit
  #;(check-equal? (infer '(let ([X Bool]) (: #t X)) ctx)
                  ;; or should it be X?
                  'Bool))

#|
From talk with michael:
The reason we need neutrals is
you'll end up having things that can't be reduced,
but the checker will need to prove they're equal. but it's just syntactic equality which kind of sucks.
there is a tradeoff between how much equality the type checker does and how much burden goes on the prover.
On one end, you have the Eq a a type that you have to prove,
on the other you have syntactic equality automatically done by the checker.
|#

#|
adding booleans
e := ...
   | True
   | False
   | boolElim e_motive e_cnd e_thn e_els

t := ...
   | 'Bool

boolElim has type (m : Bool -> *) -> (b : Bool) -> m True -> m False -> -> m b
the motive tells you what the result type is for true and false. For example:

def boolElim {m : Bool → Type} (b : Bool) (thn: m true) (els: m false) : m b :=
  match b with
   | true => thn
   | false => els
def m (b : Bool) := if b then Nat else String
def natFromBoolElim := @boolElim m true (0 : Nat) "hello"

funny thing: to define a non-trivial motive (m : Bool -> *), you need to use boolElim

eval(#t) = #t
eval(#f) = #f
eval(boolElim m e-cnd e-thn e-els) = eval(e-thn) when eval(e-cnd) = #t
eval(boolElim m e-cnd e-thn e-els) = eval(e-els) when eval(e-cnd) = #f
;; neutral case
eval(boolElim m e-cnd e-thn e-els) = boolElim m n v-thn v-els
  when
    eval(e-cnd) = n
    eval(e-thn) = v-thn
    eval(e-els) = v-els
;; this is weird because we evaluate both branches in the neutral case,
;; but ig it's no weirder than pre-evaluating function bodies
|#

#|
just in time type checking
(let ([T (lambda (t) ...)])
  (: e (T Bool)))

constraints/goals:
- the VALUES of variables that are in scope must be available during type checking.
- expressions should evaluate at most once. i.e. evaluations in type checking shouldn't happen again
during evaluation.
- the type of an expression should be inferred/checked at most once.
- a runtime type error should be impossible,
but evaluation of runtime code before a type error is discovered is acceptable.
- however, ideally, we'd only evaluate just as much as is necessary for typing.
- same-value should give few false negatives (requires neutrals and good normalization)

you need to interleave type checking and evaluation.
ideally, it would be possible to type check one isolated piece of code,
then evaluate it, then type check the next, and so on.
But this is all one expression.

design:
every sub-expression gets inferred before evaluated

infer : Expr Ctx Env -> (Values Type Value)
check : Expr Type Ctx Env -> Value

infer x ctx env =
  error if x not in ctx
  return ctx[x], env[x]
infer (let ([x rhs]) body) ctx env =
  t-rhs, v-rhs = infer rhs ctx env
  t-body, v-body = infer body (ctx, x : t-rhs) (env, x = v-rhs)
  return t-body, v-body
infer (forall (: x A) B) ctx env =
  v-A = check A * ctx env
  ;; we set x = x when there is no value available to avoid shadowing weirdness between parallel ctx,env
  ;; unnecessary eval, want just check
  _ = check B * (ctx, x : v-A) (env, x = x)
  ;; unnecessary check, want just eval
  ;; very redundant, will happen every instantiation
  return *, (pi v-A (lambda (v-x) (check B * (ctx, x : v-A) (env, x = v-x))))
infer (e1 e2) ctx env =
  ;; really shouldn't eval e1 until e2 is checked
  (pi t2 v2->t), v1 = infer e1 ctx env
  v2 = check e2 t2 ctx env
  t = (v2->t v2)
  return t, (v1 v2)
infer (: e p) ctx env =
  t = check p * ctx env
  v = check e t ctx env
  return t, v

check (lambda (x) e) (pi t-x x->t-ret) ctx env =
  ;; unnecessary eval, want just check
  ;; supply neutral x to x->t-ret and env
  _ = check e (x->t-ret x) (ctx, x : t-x) (env, x = x)
  ;; unnecessary check, want just eval
  ;; very redundant, will happen every application
  return (lambda (v) (check e (x->t-ret v) (ctx, x : t-x) (env, x = v)))
check e t ctx env =
  t', v = infer e ctx env
  assertEquals t t'
  return v

Thinking about if neutrals and Expr->Expr reduction can save the day:
instead of lambdas and foralls evaluating to functions, they just reduce to expressions
(let ([x 1])
  (lambda (y)
    (+ x y)))
~>
(lambda (y) (+ 1 y))
But this causes duplicate evals
(lambda (n)
  (let ([y (+ n n)])
    (* y y)))
~>
(lambda (n)
  (* (+ n n) (+ n n)))

the interpreter does not have this problem right now.
we only get this problem if we reduce the body of a lambda/forall before application, and then apply later

ok, so typing requires evaluation, but not vice versa. We can use promises to minimize value evaluation,
and just have a should-type? flag to disable typing

everywhere you see promise, a non-delayed value is ok too

Ctx = Hash Symbol Type ; NOTE types are always forced since typing is strict
Env = Hash Symbol (Promise Value)
parameter should-type? = #t
infer : Expr Ctx Env -> (values Type (Promise Value))
check : Expr Type Ctx Env -> (Promise Value)
eval : Expr Env -> Value

TODO should-type?
infer x ctx env =
  assert x in ctx
  t = ctx[x]
  return t, env[x] ; remember env[x] is a promise/value so no need to delay
infer (let ([x rhs]) body) ctx env =
  t-rhs, vp-rhs = infer rhs ctx env
  t-body, vp-body = infer body (ctx, x : t-rhs) (env, x = vp-rhs)
  return t-body, vp-body
infer (forall (: x A) B) ctx env =
  tp-x = check A * ctx env
  t-x = force tp-x
  ;; supply neutral x
  _ = check B * (ctx, x : t-x) (env, x = x)
  ;; no need to delay value
  return *, (pi t-x (lambda (v) eval B (env, x = v)))
infer (e1 e2) ctx env =
  (pi t2 v2->t), v1p = infer e1 ctx env
  v2p = check e2 t2 ctx env
  ;; unexpected but ok: need to force operand evaluation to infer type of application
  v2 = force v2p
  t = (v2->t v2)
  ;; no need for lazy.
  ;; this is the only delay and it produces a value, not another promise.
  return t, (delay ((force v1p) v2))
infer (: e p) ctx env =
  tp = check p * ctx env
  t = force tp
  vp = check e t ctx env
  return vp

check (lambda (x) e) (pi t-x x->t-ret) ctx env =
  ;; supply neutral x
  _ = check e (x->t-ret x) (ctx, x : t-x) (env, x = x)
  return (lambda (v) eval e (env, x = v))
check e t ctx env =
  t', vp = infer e ctx env
  assert t == t'
  return vp

eval (lambda (x) e) env = without typing: check e #f #f env
eval e env =
  without typing:
    _,vp = infer e #f env
    return (force vp)

we only force the evaluation of types and application arguments.
however, the application force may end up forcing lots of other runtime evaluations.
also, a consequence of this is that function bodies will evaluate a little with neutrals, which is not ideal.

an alternative is to evaluate it against the empty environment and then rely on neutrals,
but that leads to re-evaluations to an extent.
another option is to detect when the return type does not depend on the argument value,
and skip the initial evaluation.

Lean evaluates the argument:
nVec : (n : Nat) → Vector Unit n
#check (nVec (fib 4) : Vector Unit 5) -- succeeds
But it tries not to evaluate it
#check (nVec (fib 1000) : Vector Unit 1) -- fails with maximum recursion error
#check (nVec (fib 1000) : Vector Unit (fib 1000)) -- succeeds without evaluating anything
#check (nVec (fib 1000) : Vector Unit (fib (1000 + 0))) -- succeeds via symbolic simplification
|#
