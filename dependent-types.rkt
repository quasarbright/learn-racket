#lang racket

; a little type checker/interpreter for a dependently typed language
; initially taken from https://www.andres-loeh.de/LambdaPi/LambdaPi.pdf
; but expanded on in several ways
; - booleans (with dependent if)
; - "just-in-time type checking" (not sure what the actual name for this is)
; you can do stuff like (let ([X Bool]) (: #t X)).
; evaluation is interleaved with type checking.
; not all runtime code is evaluated during type checking, but some is.
; there are no duplicate evaluations or checks,
; but sometimes code is evaluated earlier than it might need to be.

(module+ test (require (except-in rackunit check)))
(require racket/promise
         racket/trace)

;; TODO add naturals
;; TODO add vectors
;; TODO more convenient syntax for lambda annotation, and sugar in general
;; TODO recursion with termination checking
;; TODO optimization where we avoid forcing the value of an argument/if condition when we won't need to
;; TODO propositions, equality, decidability

;; surface syntax

; An Expr is one of
; '*                               (the kind of types)
; (forall (: symbol Expr) Expr)    (dependent function type)
; (exists (: symbol Expr) Expr)    (dependent pair type)
; symbol                           (variable)
; (: Expr Expr)                    (type annotaation)
; (lambda (symbol) Expr)
; (let [(symbol Expr)] Expr)
; (pair Expr Expr)                 (pair introduction)
; (fst Expr)                       (pair elimination)
; (snd Expr)                       (pair elimination)
; (Expr Expr)                      (function application)
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

; A Value is one of
; #t
; #f
; '*                                              (the kind of types)
; 'Bool                                           (the type of booleans)
(struct pair [fst snd]);                          (pairs); we don't just use cons bc then it's ambiguous with neutrals
; (Value -> Value)                                (function value)
(struct pi [t-x x->t-ret] #:transparent);         (dependent function type)
;; where
;; t-x is a Type
;; x->t-ret is a Value -> Type
(struct sigma [t-fst fst->t-snd]);                (dependent pair type)
;; where
;; t-x is a Type
;; x->t-snd is a Value -> Type
; NeutralExpr                                     (irreducible expression)
; Represents a value from evaluating an expression.
; Function types are represented by Racket functions

; A Type is a Value

; A NeutralExpr is one of
; symbol
; (list NeutralExpr Value)                        (application)
; (list 'if NeutralExpr Value Value)
; (list 'boolElim Expr NeutralExpr Value Value)   (dependent if)
;                 ^ Expr because it's only relevant to type-checking
; (list 'fst NeutralExpr)
; (list 'snd NeutralExpr)
; Represents an irreducible expression

; An Env is a (hash symbol (Promise Value))
(define empty-env (hasheq))

; A Context is a (hash symbol Type)
; mapping to type is for term variables, mapping to kind is for type variables. don't worry about collision for now
(define empty-ctx (hasheq))

;; Expr Ctx Env -> Expr
;; Infers expr type, evaluates it, then quotes and annotates it with its type
;; (run #t ctx env) ~> '(: #t Bool)
(define (run expr ctx env)
  (define-values (t vp) (infer expr ctx env #t))
  `(: ,(quote-value (force vp)) ,(quote-value t)))

(module+ test
  (check-equal? (run '(if #t #t #f) empty-ctx empty-env)
                '(: #t Bool))
  (check-equal? (run '(: (lambda (x) x)
                         (forall (: x Bool) Bool)) empty-ctx empty-env)
                '(: (lambda (_.0) _.0)
                    (forall (: _.0 Bool) Bool))))

#;
(define-syntax-rule (for-typing e ...)
  (cond
    [should-type-check?
     e ...]
    [else 'not-type-checking]))

; Expr Ctx Env -> Value
(define (eval expr ctx env)
  (define-values (_ vp) (infer expr ctx env #f))
  (force vp))

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
      [(pair v1 v2) `(pair ,(loop v1) ,(loop v2))]
      [`(fst ,n) `(fst ,(loop n))]
      [`(snd ,n) `(snd ,(loop n))]
      [`(boolElim ,m ,n-cnd ,v-thn ,v-els)
       `(boolElim ,(loop m) ,(loop n-cnd) ,(loop v-thn) ,(loop v-els))]
      [`(if ,n-cnd ,v-thn ,v-els)
       `(if ,(loop n-cnd) ,(loop v-thn) ,(loop v-els))]
      [(pi t-arg arg->t-ret)
       (define x (my-gensym))
       `(forall (: ,x ,(loop t-arg))
                ,(loop (arg->t-ret x)))]
      [(sigma t-fst fst->t-snd)
       (define x (my-gensym))
       `(exists (: ,x ,(loop t-fst))
                ,(loop (fst->t-snd x)))]
      [(? procedure?)
       (define x (my-gensym))
       `(lambda (,x) ,(loop (v x)))]
      [`(,n-rator ,v-rand)
       `(,(loop n-rator) ,(loop v-rand))])))

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
                '(forall (: _.0 *) (forall (: _.1 _.0) _.0)))
  (check-equal? (quote-value (sigma '* (lambda (a) (sigma a (lambda (x) a)))))
                '(exists (: _.0 *) (exists (: _.1 _.0) _.0)))
  (check-equal? (quote-value (pair (lambda (x) x) (lambda (x) x)))
                '(pair (lambda (_.0) _.0) (lambda (_.1) _.1)))
  (check-equal? (quote-value '(fst a))
                '(fst a))
  (check-equal? (quote-value '(snd a))
                '(snd a)))

;; Natural -> symbol
;; like minikanren
(define (number->var n)
  (string->symbol (format "_.~a" n)))

(module+ test
  (check-equal? (number->var 0) '_.0))

; Expr Context Env Boolean -> (values Type (Promise Value))
(define (infer expr ctx env should-type-check?)
  (define-syntax-rule (for-typing e ...)
    (cond
      [should-type-check?
       e ...]
      [else 'not-type-checking]))
  (match expr
    ;; no need to delay '*, force does nothing to non-promises
    ['* (values (for-typing '*) '*)]
    ['Bool (values (for-typing '*) 'Bool)]
    [(? symbol? x)
     (define t (for-typing (hash-ref ctx x (lambda () (error 'infer "unbound variable: ~a" x)))))
     (define vp (hash-ref env x x))
     ;; remember, the env holds promises of values
     (values t vp)]
    [(? boolean? b)
     (values (for-typing 'Bool) b)]
    [`(: ,e ,p)
     (define t (for-typing (force (check p '* ctx env should-type-check?))))
     (define vp (check e t ctx env should-type-check?))
     (values t vp)]
    [`(forall (: ,x ,p-x) ,p-ret)
     (define t-x (force (check p-x '* ctx env should-type-check?)))
     ;; pass neutral x to env
     ;; ignore neutrally evaluated p-ret
     (for-typing (check p-ret '* (hash-set ctx x t-x) (hash-set env x x) should-type-check?))
     (values (for-typing '*) (pi t-x (lambda (v-x) (eval p-ret (hash-set ctx x t-x) (hash-set env x v-x)))))]
    [`(exists (: ,x ,p-fst) ,p-snd)
     (define t-fst (force (check p-fst '* ctx env should-type-check?)))
     ;; pass neutral x to env
     ;; ignore neutrally evaluated p-snd
     (for-typing (check p-snd '* (hash-set ctx x t-fst) (hash-set env x x) should-type-check?))
     (values (for-typing '*) (sigma t-fst (lambda (v-fst) (eval p-snd (hash-set ctx x t-fst) (hash-set env x v-fst)))))]
    [`(let ([,x ,rhs]) ,body)
     (define-values (t-rhs vp-rhs) (infer rhs ctx env should-type-check?))
     ;; remember env stores promises
     (infer body (hash-set ctx x t-rhs) (hash-set env x vp-rhs) should-type-check?)]
    [`(lambda (,x) ,body)
     (if should-type-check?
         (error 'infer "cannot infer type of lambda")
         (values 'not-type-checking (lambda (v) (eval body ctx (hash-set env x v)))))]
    [`(pair ,a ,b)
     (define-values (t-a vp-a) (infer a ctx env should-type-check?))
     (define-values (t-b vp-b) (infer b ctx env should-type-check?))
     (values (for-typing (sigma t-a (lambda (_) t-b)))
             (delay (pair (force vp-a) (force vp-b))))]
    [`(fst ,e)
     (define-values (t-e vp-e) (infer e ctx env should-type-check?))
     (define t-fst
       (for-typing
        (match t-e
          [(sigma t-fst _) t-fst]
          [t (error 'infer "expected a pair, but got a ~a" (quote-value t))])))
     (values t-fst (delay (match (force vp-e)
                            [(pair fst _) fst]
                            [n `(fst ,n)])))]
    [`(snd ,e)
     (define-values (t-e vp-e) (infer e ctx env should-type-check?))
     (define t-snd
       (for-typing
        (match t-e
          [(sigma _ fst->t-snd)
           (define v-fst
             (match (force vp-e)
               [(pair fst _) fst]
               [n `(fst ,n)]))
           ;; TODO weird if neutral, test
           (fst->t-snd v-fst)]
          [t (error 'infer "expected a pair, but got a ~a" (quote-value t))])))
     (values t-snd (delay (match (force vp-e)
                            [(pair _ snd) snd]
                            [n `(snd ,n)])))]
    [`(if ,cnd ,thn ,els)
     (define vp-cnd (check cnd 'Bool ctx env should-type-check?))
     (define-values (t-thn vp-thn) (infer thn ctx env should-type-check?))
     (define-values (t-els vp-els) (infer els ctx env should-type-check?))
     ;; an unfortunate force, but necessary for better inference
     (match (force vp-cnd)
       [#t (values t-thn vp-thn)]
       [#f (values t-els vp-els)]
       [n
        ;; neutral case, evaluate branches.
        ;; we're type-checked, so we don't have to worry about cnd being a non-bool!
        (define t
          (if (same-value? t-thn t-els)
              ;; special case for (if b t t) ~> t
              ;; to aid type equality
              t-thn
              `(if ,n
                   ,t-thn
                   ,t-els)))
        (define vp
          (delay
            (define v-thn (force vp-thn))
            (define v-els (force vp-els))
            (if (same-value? v-thn v-els)
                ;; special case for (if b x x) ~> x
                ;; to aid type equality
                v-thn
                `(if ,n
                     ,v-thn
                     ,v-els))))
        (values t vp)])]
    [`(boolElim ,m ,cnd ,thn ,els)
     ;; conceptually,
     ;; boolElim : (m : Bool -> *) (cnd : Bool) (thn : m #t) (els : m #f) -> m cnd
     ;; where m is called the "motive"
     ;; it's a way for the type to depend on the value condition

     ;; ignore evaluated m
     (define b->t (if should-type-check?
                      (force (check m (pi 'Bool (lambda (_) '*)) ctx env should-type-check?))
                      (lambda (_) 'not-type-checking)))
     (define vp-cnd (check cnd 'Bool ctx env should-type-check?))
     (define vp-thn (check thn (b->t #t) ctx env should-type-check?))
     (define vp-els (check els (b->t #f) ctx env should-type-check?))
     ;; this is a behavioral difference between if and boolElim.
     ;; in if, we don't evaluate the condition to type
     (define b (force vp-cnd))
     (values (b->t b)
             (delay
               (match b
                 [#t (force vp-thn)]
                 [#f (force vp-els)]
                 [n
                  ;; neutral case, evaluate branches as much as we can
                  ;; we're type-checked, so we don't have to worry about
                  ;; it being a non-bool!
                  `(boolElim ,b->t ,n
                             ,(force vp-thn)
                             ,(force vp-els))])))]
    [`(,rator ,rand)
     (define-values (t-rator vp-rator) (infer rator ctx env should-type-check?))
     (define (do-apply v-rator v-rand)
       (match v-rator
                    [(and f (? procedure?)) (f v-rand)]
                    [n
                     ;; neutral
                     `(,n ,v-rand)]))
     (if should-type-check?
         (match t-rator
           [(pi t-rand rand->t-ret)
            ;; this force may force a lot of runtime evaluation
            (define v-rand (force (check rand t-rand ctx env should-type-check?)))
            (values (rand->t-ret v-rand)
                    (delay (do-apply (force vp-rator) v-rand)))]
           [_ (error "somehow applied non-function in type-checked code")])
         (let ([v-rand (eval rand ctx env)])
           (values 'not-type-checking
                   (delay (do-apply (force vp-rator) v-rand)))))]))

; Expr Type Context Env Boolean -> Void
(define (check expr t-expected ctx env should-type-check?)
  (define-syntax-rule (for-typing e ...)
    (cond
      [should-type-check?
       e ...]
      [else 'not-type-checking]))
  (match expr
    [`(lambda (,x) ,body)
     (for-typing
      (match t-expected
        [(pi t-x x->t-ret)
         ;; ignore the neutrally evaluated body
         ;; pass neutral x to env
         (check body (x->t-ret x) (hash-set ctx x t-x) (hash-set env x x) should-type-check?)]
        [_ (error 'check "mismatch. expected a ~a, but got a function" (quote-value t-expected))]))
     ;; non-delayed eval is ok bc it's a lambda
     (eval expr ctx env)]
    [_
     (define-values (t-inferred vp) (infer expr ctx env should-type-check?))
     (for-typing
      (unless (same-value? t-expected t-inferred) (error 'check "mismatch. expected a ~a but got a ~a"
                                                         (quote-value t-expected)
                                                         (quote-value t-inferred))))
     vp]))

;; Value Value -> Boolean
(define (same-value? v1 v2)
  (equal? (quote-value v1)
          (quote-value v2)))

;; maybe this is failing because of delayed evaluation interacting weirdly with the parameter.
;; in that case, one potential solution would be to manually pass should-typecheck? instead of using a parameter.
#|
> (define current-x (make-parameter 'bad))
> (define p (parameterize ([current-x 'good]) (delay (current-x))))
> (force p)
'bad
|#

(module+ test
  (define ctx (hasheq 'unit 'Unit
                      'Unit '*
                      'b-free 'Bool))
  (define env (hasheq 'unit 'unit
                      'Unit 'Unit
                      'b-free 'b-free))
  (define (trun e) (run e ctx env))
  (define-syntax-rule (test e expected)
    (check-equal? (trun 'e) 'expected))
  (test unit
        (: unit Unit))
  (test (: (lambda (x) x) (forall (: x Bool) Bool))
        (: (lambda (_.0) _.0) (forall (: _.0 Bool) Bool)))
  (test ((: (lambda (x) x) (forall (: x Bool) Bool)) #t)
        (: #t Bool))
  (test (let ([x #t]) x)
        (: #t Bool))
  ;; polymorphic identity function
  (test (let ([id (: (lambda (t) (lambda (x) x))
                     (forall (: a *) (forall (: x a) a)))])
          ((id Bool) #t))
        (: #t Bool))
  ;; if then
  (test (if #t #t #f)
        (: #t Bool))
  ;; if else
  (test (if #f #t #f)
        (: #f Bool))
  ;; if neutral
  (test (if b-free #t #f)
        (: (if b-free #t #f) Bool))
  ;; if neutral special case
  (test (if b-free unit unit)
        (: unit Unit))
  ;; dependent if
  (test (if b-free #t unit)
        (: (if b-free #t unit)
           (if b-free Bool Unit)))
  ;; dependent if eval
  (test (if #t #t unit)
        ;; it knows to choose the then branch of the type (if #t Bool Unit)
        (: #t Bool))
  ;; boolElim then
  (test (boolElim (lambda (b) Bool)
                  #t #t #f)
        (: #t Bool))
  ;; boolElim else
  (test (boolElim (lambda (b) Bool)
                  #f #t #f)
        (: #f Bool))
  ;; boolElim neutral
  (test (boolElim (lambda (b) Bool)
                  b-free #t #f)
        (: (boolElim (lambda (_.0) Bool) b-free #t #f)
           Bool))
  ;; boolElim dependent then
  (test (boolElim (lambda (b) (if b Unit Bool))
                  #t unit #f)
        (: unit Unit))
  ;; boolElim dependent else
  (test (boolElim (lambda (b) (if b Unit Bool))
                  #f unit #f)
        (: #f Bool))
  ;; boolElim dependent neutral
  (test (boolElim (lambda (b) (if b Unit Bool))
                  b-free unit #f)
        (: (boolElim (lambda (_.0) (if _.0 Unit Bool))
                     b-free unit #f)
           (if b-free Unit Bool)))
  ;; boolElim dependent squared
  (test (boolElim (lambda (b) (boolElim (lambda (_) *) b Unit Bool))
                  #t unit #f)
        (: unit Unit))
  ;; closures work with neutrals by normalized substitution
  (test (let ([x #t])
          (: (lambda (y) x)
             (forall (: z Unit) Bool)))
        (: (lambda (_.0) #t)
           (forall (: _.0 Unit) Bool)))
  ;; type checking really does normalize
  (test (: (: (lambda (x) x)
              (forall (: y Bool) Bool))
           (forall (: z Bool) Bool))
        (: (lambda (_.0) _.0)
           (forall (: _.0 Bool) Bool)))
  ;; jit type checking
  (test (let ([X Bool])
          (: #t X))
        (: #t Bool))
  (test (let ([X (if #t Bool Unit)])
          (: #t X))
        (: #t Bool)))

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

to avoid duplicate checks, pass in should-type-check?
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

#|
Thinking about getting rid of boolElim
ctx |- if cnd then thn else els => if cnd then t-thn else t-els
--------------------------------------------------------------- (IF)
ctx |- cnd <= Bool
ctx |- thn => t-thn
ctx |- els => t-els

doesn't make sense since cnd is a (possibly non-neutral) expression and t-thn and t-els are type values.
but if you eval cnd first it's alright.
This is analogous to evaluating application arguments, and mirrors what happens to the condition in boolElim.

that's definitely going to lead to false negatives for type equality.
will add special case to reduce (if n then v else v) ~> v

should still keep boolElim around to make it easier to explicitly specify motive
when all else fails
|#

#|
adding pairs

e := ...
   | (exists (: x e) e)
   | (pair e e)
   | (fst e)
   | (snd e)
v := ...
   | (sigma v (v -> v))

ctx |- e1 <= A
ctx, x = eval(e1) : A |- e1 <= B
----------------------------------------- (PAIR<=)
ctx |- (pair e1 e2) <= (exists (: x A) B)

ctx |- e1 => A
ctx |- e2 => B
----------------------------------------- (PAIR=>)
ctx |- (pair e1 e2) => (exists (: _ A) B)

ctx |- e => (exists (: x A) B)
------------------------------ (FST)
ctx |- (fst e) => A

ctx |- e => (exists (: x A) B)
------------------------------ (SND)
ctx |- (snd e) => B
|#

(error "left off about to do exists type check rule and think about potential better inference")
