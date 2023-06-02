#lang racket

; implementation of https://www.cis.upenn.edu/~bcpierce/papers/lti-toplas.pdf
; I modified it to use type equality instead of subtyping and got rid of Top, Bot

(module+ test (require rackunit))

; An Expr is one of
; symbol (variable)
; (lambda (symbol ...) ((: symbol Type) ...) Expr)
; (Expr (Type ...) (Expr ...)) (application)
; (let ([x Expr]) Expr)
; (letrec ([(: x Type) Expr] ...) Expr)

; A Type is one of
; symbol (type variable)
; (forall (symbol ...) (Type ...) Type) (polymorphic function type)

; A Context is a
(struct context [type-vars var-types] #:transparent)
; where
; type-vars is a (set symbol) representing type variables in scope
; var-types is a (hash symbol Type) representing a mapping from term variables to their types

; Type Type -> Void
; Assert the two types are equal
(define (unify low high)
  ; ignore low high. that's from when this used to be a subtyping function
  (match* (low high)
    [(low high) #:when (equal? low high) (void)]
    ; TODO this won't think (forall (a) (a) a) is a subtype of (forall (a b) (a) b)
    ; doesn't matter because no longer a subtype function
    [(`(forall ,t-vars-low ,t-args-low ,t-ret-low)
      `(forall ,t-vars-high ,t-args-high ,t-ret-high))
     (unless (equal? t-vars-low t-vars-high)
       (error 'unify "quantified types have different type arguments: ~a ~a" t-vars-low t-vars-high))
     (unless (= (length t-args-low) (length t-args-high))
       (error 'unify "function types have different numbers of arguments"))
     (for ([t-arg-low t-args-low]
           [t-arg-high t-args-high])
       ; contravariant twist. not anymore
       (unify t-arg-high t-arg-low))
     (unify t-ret-low t-ret-high)]
    [(_ _) (error 'unify "type mismatch: ~a ~a" low high)]))

; Expr Context -> Type
(define (infer-type expr ctx)
  (match expr
    [(? symbol?) (context-lookup ctx expr)]
    [`(lambda ,type-arg-names ((: ,arg-names ,arg-types) ...) ,body)
     (define ctx^
       (context-extend* (context-add-type-vars ctx type-arg-names)
                       arg-names
                       arg-types))
     (define body-type (infer-type body ctx^))
     `(forall ,type-arg-names ,arg-types ,body-type)]
    [`(let ([,vars ,exprs] ...) ,body)
     (define ctx^
       (for/fold ([ctx^ ctx])
                 ([var vars] [expr exprs])
         ; use old ctx the whole time
         (context-extend ctx^ var (infer-type expr ctx))))
     (infer-type body ctx^)]
    [`(letrec ([(: ,vars ,var-types) ,exprs] ...) ,body)
     (define ctx^ (context-extend* ctx vars var-types))
     (for ([expr exprs] [type var-types])
       (check-type expr type ctx^))
     (infer-type body ctx^)]
    [`(,function ,type-args ,args)
     (define function-type (infer-type function ctx))
     (match function-type
       [`(forall ,type-arg-names ,arg-types ,return-type)
        (unless (= (length type-args)
                   (length type-arg-names))
          (error 'infer "type arity error"))
        (unless (= (length args)
                   (length arg-types))
          (error 'infer "arity error"))
        (define arg-types^
          (for/list ([arg-type arg-types])
            (subst* arg-type type-arg-names type-args)))
        (define return-type^ (subst* return-type type-arg-names type-args))
        (for ([arg args]
              [arg-type arg-types^])
          (check-type arg arg-type ctx))
        return-type^]
       [_ (error 'infer-type "application expected function type: ~a" function-type)])]))

; Expr Type Context -> Void
(define (check-type expr type ctx)
  (define expr-type (infer-type expr ctx))
  (unify expr-type type))

(define (context-lookup ctx var)
  (hash-ref (context-var-types ctx) var (lambda () (error 'context-lookup "unbound variable ~a" var))))

(define (context-extend* ctx vars types)
  (for/fold ([ctx ctx])
            ([var vars] [type types])
    (context-extend ctx var type)))

(define (context-extend ctx var type)
  (struct-copy context ctx
               [var-types
                (hash-set (context-var-types ctx) var type)]))

(define (context-add-type-vars ctx vars)
  (for/fold ([ctx ctx])
            ([var vars])
    (context-add-type-var ctx var)))

(define (context-add-type-var ctx var)
  (struct-copy context ctx
               [type-vars
                (set-add (context-type-vars ctx) var)]))

(define (subst* type vars types)
  (for/fold ([type^ type])
            ([var vars]
             [type types])
    (subst type^ var type)))

(define (subst type var replacement)
  (match type
    [(? symbol?)
     (if (eq? type var)
         replacement
         type)]
    [`(forall ,type-arg-names ,arg-types ,return-type)
     (if (member var type-arg-names)
         type
         `(forall ,type-arg-names
                  ,(for/list ([arg-type arg-types])
                     (subst arg-type var replacement))
                  ,(subst return-type var replacement)))]))

(module+ test
  (define ctx (context (seteq 'Bool) (hasheq 'true 'Bool 'false 'Bool)))
  (check-equal? (infer-type '(lambda (a) ((: x a)) x) ctx)
                '(forall (a) (a) a))
  (check-equal? (infer-type '((lambda (a) ((: x a)) x)
                              (Bool)
                              (true))
                            ctx)
                'Bool)
  (check-equal? (infer-type '(let ([id (lambda (a) ((: x a)) x)])
                               (id (Bool) (true)))
                            ctx)
                'Bool)
  (check-equal? (infer-type '(let ([const (lambda (a b) ((: x a) (: y b)) x)])
                               (const (Bool Bool) (true false)))
                            ctx)
                'Bool)
  (check-equal? (infer-type '(let ([const (lambda (a) ((: x a))
                                            (lambda (b) ((: y b)) x))])
                               (const (Bool) (true)))
                            ctx)
                '(forall (b) (b) Bool))
  (check-equal? (infer-type '(letrec ([(: loop (forall (a) () a))
                                       (lambda (a) ()
                                         (loop (a) ()))])
                               (loop ((forall (c d) (c) d)) ()))
                            ctx)
                '(forall (c d) (c) d)))
