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
; (lambda symbol Expr)
; (Expr Expr)


; A Value is one of
; (lambda symbol Value)
; NeutralExpr

; A NeutralExpr is one of
; symbol
; (NeutralExpr Value)

; A Context is a (hash symbol (or Type Kind))
; mapping to type is for term variables, mapping to kind is for type variables. don't worry about collision for now
(define empty-ctx (hasheq))

(module+ test (require (except-in rackunit check)))

; Expr -> Value
(define (eval expr)
  (match expr
    [(? symbol? expr) expr]
    [`(: ,expr _) (eval expr)]
    [`(lambda ,x ,body)
     `(lambda ,x ,(eval body))]
    [`(,rator ,rand)
     (match (eval rator)
       ; note body is a value, not an expr
       [`(lambda ,x ,body) (eval (subst body x (eval rand)))]
       ; TODO check if it's a neutral once there are numbers and stuff
       [n `(,n ,(eval rand))])]))

; Value symbol Value
(define (subst v x replacement)
  (match v
    [(? symbol? v) (if (eq? v x) replacement v)]
    [`(lambda ,arg ,body)
     `(lambda ,arg ,(if (eq? arg x)
                        body
                        (subst body x replacement)))]))

; Expr Context -> Type
(define (infer expr ctx)
  (match expr
    [(? symbol? expr)
     (hash-ref ctx expr (lambda () (error 'infer "variable not found in context")))]
    [`(: ,expr ,type)
     (check-type type ctx)
     (check expr type ctx)
     type]
    [`(lambda ,x ,body) (error 'infer "cannot infer type of lambda")]
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
    [`(lambda ,x ,body)
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
  (check-equal? (eval 'x) 'x)
  (check-equal? (eval '(lambda x x)) '(lambda x x))
  (check-equal? (eval '((lambda x x) y)) 'y)
  (check-equal? (infer 'x (hasheq 'a '* 'x 'a)) 'a)
  (check-equal? (check 'x 'a (hasheq 'a '* 'x 'a)) (void))
  (check-equal? (check '(lambda x x) '(-> a a) empty-ctx) (void))
  (check-equal? (infer '(: (lambda x x) (-> a a)) (hasheq 'a '*)) '(-> a a))
  (check-equal? (infer '((: (lambda x x) (-> a a)) y) (hasheq 'a '* 'y 'a)) 'a)
  (check-equal? (infer '(((: (lambda x (lambda y x))
                             (-> a (-> b a)))
                          i)
                         j)
                       (hasheq 'a '*
                               'b '*
                               'i 'a
                               'j 'b))
                'a))
