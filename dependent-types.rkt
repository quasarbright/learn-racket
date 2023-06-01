#lang racket

; a little type checker/interpreter for a dependently typed language
; taken from https://www.andres-loeh.de/LambdaPi/LambdaPi.pdf

; a Type is one of
; symbol (base type)
; (-> Type Type)

; A Kind is '*

; An Expr is one of
; symbol (variable)
; (: Expr Type)
; (lambda (symbol) Expr)
; (Expr Expr)


; A Value is one of
; (symbol -> Value)
; NeutralExpr

; A NeutralExpr is one of
; symbol
; (NeutralExpr Value)

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
    [(? symbol? expr) (hash-ref env expr expr)]
    [`(: ,expr _) (eval expr env)]
    [`(lambda (,x) ,body)
     (lambda (v) (eval body (hash-set env x v)))]
    [`(,rator ,rand)
     (match (eval rator env)
       [(and f (? procedure?)) (f (eval rand env))]
       ; TODO check if it's a neutral once there are numbers and stuff
       [n `(,n ,(eval rand env))])]))

; Value -> Expr
(define (quote-value v [count 0])
  (match v
    [(? symbol?) v]
    [`(,n-rator ,v-rand)
     `(,n-rator ,(quote-value v-rand count))]
    [(? procedure?)
     (define x (number->var count))
     `(lambda (,x) ,(quote-value (v x) (add1 count)))]))

(module+ test
  (check-equal? (quote-value 'x) 'x)
  (check-equal? (quote-value '(x y)) '(x y))
  (check-equal? (quote-value (lambda (x) x)) '(lambda (_.0) _.0))
  (check-equal? (quote-value (lambda (x) (lambda (y) x)))
                '(lambda (_.0) (lambda (_.1) _.0))))

; Natural -> symbol
(define (number->var n)
  (string->symbol (format "_.~a" n)))

(module+ test
  (check-equal? (number->var 0) '_.0))

; Expr Context -> Type
(define (infer expr ctx)
  (match expr
    [(? symbol? expr)
     (hash-ref ctx expr (lambda () (error 'infer "variable not found in context")))]
    [`(: ,expr ,type)
     (check-type type ctx)
     (check expr type ctx)
     type]
    [`(lambda (,x) ,body) (error 'infer "cannot infer type of lambda")]
    [`(,rator ,rand)
     (define t-rator (infer rator ctx))
     (match t-rator
       [`(-> ,t-rand ,t-ret)
        (check rand t-rand ctx)
        t-ret]
       [_ (error 'infer "applied non-function")])]))

; Expr Type Context -> Void
(define (check expr type ctx)
  (match expr
    [`(lambda (,x) ,body)
     (match type
       [`(-> ,t-x ,t-body)
        (check body t-body (hash-set ctx x t-x))]
       [_ (error 'check "mismatch. expected a function type")])]
    [_
     (define t-infer (infer expr ctx))
     (unless (equal? type t-infer) (error 'check "mismatch"))]))

; Type Context -> Void
; make sure a type is well-formed in the context
(define (check-type type ctx)
  (match type
    [(? symbol? type)
     (define kind (hash-ref ctx type (lambda () (error 'check-type "type variable not found in context"))))
     (unless (eq? kind '*) (error 'check-type "type not well-formed"))]
    [`(-> ,t-arg ,t-ret)
     (check-type t-arg ctx)
     (check-type t-ret ctx)]))

(module+ test
  (check-equal? (eval 'x empty-env) 'x)
  (check-equal? (eval 'x (hasheq 'x 'y)) 'y)
  (check-equal? (normalize '(lambda (x) x)) '(lambda (_.0) _.0))
  (check-equal? (eval '((lambda (x) x) y) empty-env) 'y)
  (check-equal? (infer 'x (hasheq 'a '* 'x 'a)) 'a)
  (check-equal? (check 'x 'a (hasheq 'a '* 'x 'a)) (void))
  (check-equal? (check '(lambda (x) x) '(-> a a) empty-ctx) (void))
  (check-equal? (infer '(: (lambda (x) x) (-> a a)) (hasheq 'a '*)) '(-> a a))
  (check-equal? (infer '((: (lambda (x) x) (-> a a)) y) (hasheq 'a '* 'y 'a)) 'a)
  (check-equal? (infer '(((: (lambda (x) (lambda (y) x))
                             (-> a (-> b a)))
                          i)
                         j)
                       (hasheq 'a '*
                               'b '*
                               'i 'a
                               'j 'b))
                'a))
