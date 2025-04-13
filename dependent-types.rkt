#lang racket

; a little type checker/interpreter for a dependently typed language
; taken from https://www.andres-loeh.de/LambdaPi/LambdaPi.pdf

; TODO add booleans
; TODO add naturals
; TODO add vectors
; TODO add phasing so there is an environment for evaluations during type checking

;; surface syntax

; An Expr is one of
; '*                               (the kind of types)
; (forall (: symbol Expr) Expr)    (dependent function type)
; symbol                           (variable)
; (: Expr Expr)                    (type annotaation)
; (lambda (symbol) Expr)
; (let [(symbol Expr)] Expr)
; (Expr Expr)
; Represents the surface syntax of a program as an s-expression

; The meaning of (forall (: x t1) t2) is a function type analogous to (t1 -> t2).
; t1 is the type of value that gets passed in for x. t2 is the return type.
; But t2 can depend on the _value_ of x.
; t1 and t2 both have to be of kind *. Remember * is of kind *.
; Example: (forall (: x Int) Bool) is (Int -> Bool)
; Example: (forall (: a *) (forall (: x a) a))
;   is the type of the identity function, but it has to be instantiated with a type like ((id Nat) 1) ~> 1.
; Example: (forall (: a *) (forall (: b *) (forall (: x a) (forall (: y b) a))))
;   is the type of the const function (a -> (b -> a))
; Example: (forall (: a *) a)
;   is the type of a function that takes in a type and returns a value of that type (impossible)
; Example: (forall (: a *) (forall (: n Nat) (forall (: x a) (Vec n a))))
;   is the type of a function that takes in a vector length and a value and
;   creates a vector of that length filled with copies of the value.
;   Assuming Nat is of type *.

;; runtime

; A Value is one of
; '*                                (the kind of types)
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
; (list NeutralExpr Value)

; An Env is a (hash symbol Value)
(define empty-env (hasheq))

; A Context is a (hash symbol (or Type Kind))
; mapping to type is for term variables, mapping to kind is for type variables. don't worry about collision for now
(define empty-ctx (hasheq))

(module+ test (require (except-in rackunit check)))

; Expr -> Expr
(define (normalize expr) (quote-value (eval expr empty-env)))

; Expr -> Value
(define (eval expr env)
  (match expr
    ['* '*]
    [(? symbol? x) (hash-ref env x x)]
    [`(: ,expr _) (eval expr env)]
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
    [`(,rator ,rand)
     (match (eval rator env)
       [(and f (? procedure?)) (f (eval rand env))]
       [(or '* (pi _ _)) (error 'eval "bad application")]
       [n
        ;; neutral
        `(,n ,(eval rand env))])]))

; Value -> Expr
(define (quote-value v [count 0])
  (match v
    ['* '*]
    [(? symbol?) v]
    [`(,n-rator ,v-rand)
     `(,n-rator ,(quote-value v-rand count))]
    [(pi t-arg arg->t-ret)
     (define x (number->var count))
     ; you should probably use mutation for count.
     ; you probably want to thread the state through for these two recursive calls.
     ; technically doesn't matter, but still a little weird.
     `(forall (: ,x ,(quote-value t-arg count))
              ,(quote-value (arg->t-ret x) (add1 count)))]
    [(? procedure?)
     (define x (number->var count))
     `(lambda (,x) ,(quote-value (v x) (add1 count)))]))

(module+ test
  (check-equal? (quote-value 'x) 'x)
  (check-equal? (quote-value '(x y)) '(x y))
  (check-equal? (quote-value (lambda (x) x)) '(lambda (_.0) _.0))
  (check-equal? (quote-value (lambda (x) (lambda (y) x)))
                '(lambda (_.0) (lambda (_.1) _.0)))
  (check-equal? (quote-value '*) '*)
  ; type of the identity function
  ; (forall (: a *) (forall (: x a) x))
  (check-equal? (quote-value (pi '* (lambda (v) (pi v (lambda (w) w)))))
                '(forall (: _.0 *) (forall (: _.1 _.0) _.1))))

; Natural -> symbol
(define (number->var n)
  (string->symbol (format "_.~a" n)))

(module+ test
  (check-equal? (number->var 0) '_.0))

; Expr Context -> Type
(define (infer expr ctx)
  (match expr
    ['* '*]
    [(? symbol? expr)
     (hash-ref ctx expr (lambda () (error 'infer "variable not found in context")))]
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
  (define ctx (hasheq 'Bool '* 'true 'Bool 'false 'Bool))
  (check-equal? (eval 'x empty-env) 'x)
  (check-equal? (eval 'x (hasheq 'x 'y)) 'y)
  (check-equal? (normalize '(lambda (x) x)) '(lambda (_.0) _.0))
  (check-equal? (eval '((lambda (x) x) y) empty-env) 'y)
  (check-equal? (eval '(let ([x y]) x) empty-env) 'y)
  (check-equal? (infer 'true ctx) 'Bool)
  (check-equal? (check 'true 'Bool ctx) (void))
  (check-equal? (check '(lambda (x) x) (pi 'Bool (const 'Bool)) ctx) (void))
  (check-equal? (quote-value
                 (infer '(: (lambda (x) x)
                            (forall (: x Bool) Bool))
                        ctx))
                '(forall (: _.0 Bool) Bool))
  (check-equal? (infer '((: (lambda (x) x) (forall (: x Bool) Bool)) true) ctx) 'Bool)
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
                         true)
                       ctx)
                'Bool)
  (check-equal? (check '(: (lambda (a) (lambda (x) x))
                           (forall (: a *) (forall (: x a) a)))
                       (pi '* (lambda (a) (pi a (lambda (x) a))))
                       empty-ctx)
                (void))
  (check-equal? (infer '(let ([id (: (lambda (a) (lambda (x) x))
                                     (forall (: a *) (forall (: x a) a)))])
                          ((id Bool) true))
                       ctx)
                'Bool))
