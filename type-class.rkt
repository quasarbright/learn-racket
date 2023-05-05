#lang racket

(require racket/hash)

; a statically typed language with type classes like haskell


; A (UnionFind A) is a
; (hash-of )

; An Env is a (hash-of symbol? Scheme)
; Maps surface names to schemes
; A Constraints is a (hash-of symbol? Type)
; Maps each type variable to its type

; A Type is one of
(struct t-var [name] #:transparent)
(struct t-fun [arg ret] #:transparent)
(struct t-number [] #:transparent)
(struct t-boolean [] #:transparent)

(define type? (disjoin t-var? t-fun? t-number? t-boolean?))

; A Scheme is one of
(struct scheme [var child] #:transparent)
; (scheme symbol? Scheme)
; A Type
; Represents universal quantification

; immutable parameter hasheq
(define current-env (make-parameter (make-hasheq)))
; mutable global hasheq. it's ok because new-t-var will never ever repeat
(define constraints (hasheq))

; Expr -> Type
(define (infer expr)
  (match expr
    [(? symbol?)
     (define t (hash-ref (current-env) expr (lambda () (error "unbound variable"))))
     (inst t)]
    [(? number?) (t-number)]
    [(? boolean?) (t-boolean)]
    [`(lambda (,argname) ,body)
     (define-t-var t-arg)
     (define t-ret (let-type ([argname t-arg]) (infer body)))
     (t-fun t-arg t-ret)]
    [`(let ([,x ,rhs]) ,body)
     (define t-x (gen (infer rhs)))
     (let-type ([x t-x]) (infer body))]
    ; type annotation
    [`(: ,e ,t) (check e t)]
    ; application
    [(list fun arg)
     (define-t-var t-arg)
     (define-t-var t-ret)
     (unify (t-fun t-arg t-ret) (infer fun))]))

(define (new-t-var [name #f]) (t-var (if name (gensym name) (gensym))))
(define-syntax-rule (define-t-var name) (define name (new-t-var 'name)))

; locally extend the environment with the given associations between surface names and schemes in body
(define-syntax-rule
  (let-type ([x t] ...) body ...)
  (parameterize ([current-env (hash-union (current-env) (make-hasheq (list (cons x t) ...)) (lambda (a b) b))]) body ...))

; Scheme -> Type
; instantiate a scheme with fresh vars replacing quantified vars
(define (inst schm)
  (match schm
    [(scheme old-name child)
     (define-t-var t-inst)
     (subst-type-var old-name t-inst schm)]
    [_ schm]))

; Type -> Scheme
; generalize a type by quantifying over its un-constrained vars
(define (gen typ)
  (define typ^ (expand-type typ))
  ; after expansion, any vars left are un-constrained
  (define vars (type-vars typ))
  (for/fold ([schm typ^])
            ([var vars])
    (scheme var schm)))

; Type -> Type
; expand typ by replacing constrained vars with their values
(define (expand-type typ)
  (match typ
    [(t-var name)
     ; #f means it's unconstrained and we're done
     (define typ^ (hash-ref constraints name #f))
     (if typ^ (expand-type typ^) typ)]
    [(t-fun t-arg t-ret)
     (t-fun (expand-type t-arg) (expand-type t-ret))]
    [_ typ]))

; Type -> (set-of symbol?)
(define (type-vars typ)
  (match typ
    [(t-var name) (seteq name)]
    [(t-fun t-arg t-ret) (set-union (type-vars t-arg) (type-vars t-ret))]
    [_ (seteq)]))

; Expr Type -> void
(define (check expr t-expected)
  (define t-actual (infer expr))
  (unify t-expected t-actual))

; Expr -> Value
(define (eval expr) 'todo)
