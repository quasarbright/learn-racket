#lang racket

; started as an implementation of https://www.cis.upenn.edu/~bcpierce/papers/lti-toplas.pdf
; Ended up taking it in a different direction

; features:
; Higher rank polymorphism
; recursion
; algebraic data types
; requires annotated lambda arguments
; requires type application on function applications
; naive structural type equality

(module+ test (require rackunit))

; An Expr is one of
; symbol                                                            (variable)
; (lambda (symbol ...) ((: symbol Type) ...) Expr)
; (Expr (Type ...) Expr ...)                                        (application)
; (let ([x Expr] ...) Expr)                                         (variable binding)
; (letrec ([(: x Type) Expr] ...) Expr)                             (recursive variable binding)
; (let-data ((symbol symbol ...) (symbol Type ...) ...) Expr)       (data definition)
; (case Expr [(symbol symbol ...) Expr] ...)                        (case)
; (: Expr Type)                                                     (annotation)
; Examples
#;(((lambda (a b) ((: x a) (: y b)))
    [Bool (List Bool)]
    (True [])
    (Empty [Bool]))

   (let ([id (lambda [a] ((: x a)) x)])
     (id [Bool] (True [])))

   (letrec ([(: loop (forall [a] () a))
             (lambda [a] () (loop [a]))])
     (loop [Void]))

   (let-data ((List a) (Empty) (Cons a (List a)))
             ; list tail function
             (lambda [a] ((: lst (List a)))
               (case lst
                 [(Empty) (Empty [])]
                 [(Cons ele lst) lst]))))

; A Type is one of
; symbol (type variable)
; (forall (symbol ...) (Type ...) Type)   (polymorphic function type)
; (symbol Type ...)                       (data type application)

; Examples
#;(; polymorphic identity function
   (forall [a] (a) a)

   ; const function, higher rank polymorphism
   (forall [a] (a) (forall [b] (b) a))

   ; polymorphic list type
   (List a))

; A Context is a
(struct context [type-vars var-types data-defs] #:transparent)
; where
; type-vars is a (set symbol) representing type variables in scope
; var-types is a (hash symbol Type) representing a mapping from term variables to their types
; data-defs is a (hash symbol DataDef)
(define empty-ctx (context (seteq) (hasheq) (hasheq)))

; A DataDef is a
(struct data-def [name type-arg-names variants] #:transparent)
; where
; name is a symbol representing the name of the data type
; type-arg-names is a (listof symbol) representing the names of type arguments
; variants is a (listof Variant)

; A Variant is a
(struct variant [constructor-name field-types] #:transparent)
; where
; constructor-name is a symbol representing the name of the data constructor
; field-types is a (listof Type) representing the types of the fields

; Type Type -> Void
; Assert the two types are equal
(define (unify low high)
  ; ignore names low and high. that's from when this used to be a subtyping function
  (match* (low high)
    [(low high) #:when (equal? low high) (void)]
    [(`(forall ,t-vars-low ,t-args-low ,t-ret-low)
      `(forall ,t-vars-high ,t-args-high ,t-ret-high))
     (unless (equal? t-vars-low t-vars-high)
       (error 'unify "quantified types have different type arguments: ~a ~a" t-vars-low t-vars-high))
     (unless (= (length t-args-low) (length t-args-high))
       (error 'unify "function types have different numbers of arguments"))
     (for ([t-arg-low t-args-low]
           [t-arg-high t-args-high])
       (unify t-arg-high t-arg-low))
     (unify t-ret-low t-ret-high)]
    [(`(,name-high . ,type-args-high) `(,name-low ,type-args-low))
     (unless (eq? name-high name-low)
       (error 'unify "type mismatch: ~a ~a" low high))
     (unless (= (length type-args-low) (length type-args-high))
       (error 'unify "data types have different numbers of arguments"))
     (for ([type-arg-high type-args-high]
           [type-arg-low type-args-low])
       (unify type-arg-low type-arg-high))]
    [(_ _) (error 'unify "type mismatch: ~a ~a" low high)]))

; (listof Type) -> Void
; assert all types are equal
(define (unify* types)
  (match types
    [(list* low high types)
     (unify low high)
     (unify* (cons high types))]
    [_ (void)]))

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
    [`(let-data ((,name . ,type-arg-names) (,constructor-names . ,variant-field-typess) ...) ,body)
     (define variants
       (for/list ([constructor-name constructor-names]
                  [variant-field-types variant-field-typess])
         (variant constructor-name variant-field-types)))
     (define def (data-def name type-arg-names variants))
     (define constructor-types
       (for/list ([variant-field-types variant-field-typess])
         `(forall ,type-arg-names ,variant-field-types (,name . ,type-arg-names))))
     (define ctx^
       (context-extend* (context-add-data-def ctx def)
                        constructor-names
                        constructor-types))
     (infer-type body ctx^)]
    [`(case ,scrutinee
        [(,constructor-names . ,field-varss) ,bodies] ...)
     (define scrutinee-type (infer-type scrutinee ctx))
     (define true-constructor-names (context-get-constructor-names ctx scrutinee-type))
     ; TODO order-agnostic comparison
     (unless (equal? true-constructor-names constructor-names)
       (error 'infer-type "bad constructor names for case: ~a ~a" true-constructor-names constructor-names))
     (when (null? constructor-names)
       (error 'infer-type "cannot infer type of empty case"))
     (define body-types
       (for/list ([constructor-name constructor-names]
                  [field-vars field-varss]
                  [body bodies])
         (define field-types (context-get-field-types ctx scrutinee-type constructor-name))
         (unless (= (length field-vars) (length field-types))
           (error 'infer-type
                  "pattern arity error: ~a has ~a field(s), but ~a were provided"
                  constructor-name
                  (length field-types)
                  (length field-vars)))
         (define ctx^ (context-extend* ctx field-vars field-types))
         (infer-type body ctx^)))
     (unify* body-types)
     (first body-types)]
    [`(: ,expr ,type)
     (check-type expr type ctx)
     type]
    [`(,function ,type-args . ,args)
     (define function-type (infer-type function ctx))
     (match function-type
       [`(forall ,type-arg-names ,arg-types ,return-type)
        (unless (= (length type-args)
                   (length type-arg-names))
          (error 'infer-type "type arity error"))
        (unless (= (length args)
                   (length arg-types))
          (error 'infer-type "arity error"))
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
  (match expr
    [`(case ,scrutinee)
     (=> fail)
     (define scrutinee-type (infer-type scrutinee ctx))
     (define constructor-names (context-get-constructor-names ctx scrutinee-type))
     ; (case e : Void of) checks against any type
     (unless (null? constructor-names) (fail))]
    [_
     (define expr-type (infer-type expr ctx))
     (unify expr-type type)]))

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

(define (context-add-data-def ctx def)
  (struct-copy context ctx
               [data-defs
                (hash-set (context-data-defs ctx) (data-def-name def) def)]))

(define (context-get-constructor-names ctx type)
  (match type
    [`(,name . ,_)
     (define def (context-get-data-def ctx name))
     (for/list ([variant (data-def-variants def)])
       (variant-constructor-name variant))]
    [_ (error 'context-get-constructor-names "type is not a data type ~a" type)]))

(define (context-get-data-def ctx name)
  (hash-ref (context-data-defs ctx) name (lambda () 'context-get-data-def "no data definition found for ~a" name)))

(define (context-get-field-types ctx type constructor-name)
  (match type
    [`(,name . ,type-args)
     (define def (context-get-data-def ctx name))
     (define type-arg-names (data-def-type-arg-names def))
     (define variants (data-def-variants def))
     (define variant
       (findf (lambda (variant) (equal? constructor-name
                                        (variant-constructor-name variant)))
              variants))
     (unless variant (error 'context-get-field-types "variant not found: ~a" constructor-name))
     (unless (= (length type-arg-names) (length type-args))
       (error 'context-get-field-types "data type arity error"))
     (for/list ([field-type (variant-field-types variant)])
       (subst* field-type type-arg-names type-args))]
    [_ (error 'context-get-field-types "type is not a data type ~a" type)]))

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
                  ,(subst return-type var replacement)))]
    [`(,name . ,type-args)
     ; TODO subst name if you allow type var applications
     `(,name . ,(for/list ([type-arg type-args])
                (subst type-arg var replacement)))]))

(module+ test
  (define ctx (context (seteq 'Bool) (hasheq 'true 'Bool 'false 'Bool) (hasheq)))
  (check-equal? (infer-type '(: true Bool) ctx) 'Bool)
  (check-equal? (infer-type '(lambda (a) ((: x a)) x) ctx)
                '(forall (a) (a) a))
  (check-equal? (infer-type '((lambda (a) ((: x a)) x)
                              (Bool)
                              true)
                            ctx)
                'Bool)
  (check-equal? (infer-type '(let ([id (lambda (a) ((: x a)) x)])
                               (id (Bool) true))
                            ctx)
                'Bool)
  (check-equal? (infer-type '(let ([const (lambda (a b) ((: x a) (: y b)) x)])
                               (const (Bool Bool) true false))
                            ctx)
                'Bool)
  (check-equal? (infer-type '(let ([const (lambda (a) ((: x a))
                                            (lambda (b) ((: y b)) x))])
                               (const (Bool) true))
                            ctx)
                '(forall (b) (b) Bool))
  (check-equal? (infer-type '(letrec ([(: loop (forall (a) () a))
                                       (lambda (a) ()
                                         (loop (a)))])
                               (loop [(forall (c d) (c) d)]))
                            ctx)
                '(forall (c d) (c) d))
  ; bool data
  (check-equal? (infer-type '(let-data ((Bool) (True) (False))
                                       (True []))
                            empty-ctx)
                '(Bool))
  ; bool data with case
  (check-equal? (infer-type '(let-data ((Bool) (True) (False))
                                       (case (True [])
                                         [(True) (lambda [] () (False []))]
                                         [(False) (lambda [] () (True []))]))
                            empty-ctx)
                '(forall [] () (Bool)))
  ; bool list empty
  (check-equal? (infer-type '(let-data ((List a) (Empty) (Cons a (List a)))
                                       (Empty [Bool]))
                            ctx)
                '(List Bool))
  ; bool list cons
  (check-equal? (infer-type '(let-data ((List a) (Empty) (Cons a (List a)))
                                       (Cons [Bool] true (Empty [Bool])))
                            ctx)
                '(List Bool))
  ; map
  (check-equal? (infer-type '(let-data ((List a) (Empty) (Cons a (List a)))
                                       (letrec ([(: map (forall [a b] ((forall [] (a) b) (List a)) (List b)))
                                                 (lambda [a b] ((: f (forall [] (a) b)) (: xs (List a)))
                                                   (case xs
                                                     [(Empty) (Empty [b])]
                                                     [(Cons x xs)
                                                      (Cons [b] (f [] x) (map [a b] f xs))]))])
                                         map))
                            empty-ctx)
                '(forall [a b] ((forall [] (a) b) (List a)) (List b)))
  ; absurd via void
  (check-equal? (infer-type '(let-data ((Void))
                                       (lambda [a] ((: never (Void)))
                                         (: (case never) a)))
                            empty-ctx)
                '(forall [a] ((Void)) a)))

; An Environment is a
(struct environment [var-values] #:transparent)
; where
; var-values is a (hash symbol? Value) representing the values of variables
(define empty-env (environment (hasheq)))

; A Value is one of
(struct data-value [constructor-name fields] #:transparent)
; where
; constructor is a symbol
; fields is a (listof Value)
; (Value ... -> Value)

; Expr Environment -> Value
(define (eval expr env)
  (match expr
    [(? symbol?) (environment-lookup env expr)]
    [`(lambda ,_ ((: ,arg-names ,_) ...) ,body)
     (lambda args
       ; should be impossible after type checking
       (unless (= (length args) (length arg-names))
         (error 'eval "arity error (at runtime)"))
       (eval body (environment-extend* env arg-names args)))]
    [`(let ([,xs ,exprs] ...) ,body)
     (define exprs^ (for/list ([expr exprs]) (eval expr env)))
     (eval body (environment-extend* env xs exprs^))]
    [`(letrec ([(: ,xs ,_) ,exprs^] ...) ,body) 'todo]
    [`(let-data (,name (,constructor-names ,field-namess ...) ...) ,body)
     (define constructor-values
       (for/list ([constructor-name constructor-names]
                  [field-names field-namess])
         (lambda fields
           (unless (= (length field-names) (length fields))
             (error 'eval "arity error (at runtime)"))
           (data-value constructor-name fields))))
     (eval body (environment-extend* env constructor-names constructor-values))]
    [`(case ,scrutinee [(,constructor-names . ,field-var-namess) ,bodies] ...)
     (define scrutinee^ (eval scrutinee env))
     (unless (data-value? scrutinee^)
       (error 'eval "case on non-data (at runtime)"))
     (define scrutinee-constructor-name (data-value-constructor-name scrutinee^))
     ; assume at least one constructor matches
     (for/first ([pattern-constructor-name constructor-names]
                 [field-var-names field-var-namess]
                 [body bodies]
                 #:when (equal? pattern-constructor-name scrutinee-constructor-name))
       ; assume correct number of fields
       (eval body (environment-extend* env field-var-names (data-value-fields scrutinee^))))]
    [`(,fun ,_ . ,args)
     (define fun^ (eval fun env))
     ; should be impossible after type checking
     (unless (procedure? fun^)
       (error 'eval "applied non-procedure"))
     (apply fun^ (for/list ([arg args]) (eval arg env)))]))

(define (environment-extend* env vars vals)
  (for/fold ([env env])
            ([var vars]
             [val vals])
    (environment-extend env var val)))

(define (environment-extend env var val)
  (struct-copy environment env [var-values (hash-set (environment-var-values env) var val)]))

(define (environment-lookup env var)
  (hash-ref (environment-var-values env) var (lambda () (error 'environment-lookup "unbound var (at runtime): ~a" var))))

(module+ test
  (define (eval-test expr)
    (eval `(let-data ((Bool) (True) (False))
                     (let-data ((List a) (Empty) (Cons a (List a)))
                               (let-data ((Nat) (Zero) (Succ Nat))
                                         ,expr)))
          empty-env))
  (check-equal? (eval-test '((lambda [] () (True [])) (False []))) (data-value 'True '()))
  (check-equal? (eval-test '(case (Succ [] (Zero []))
                              [(Zero) (Succ [] (Zero []))]
                              [(Succ n) (Succ [] (Succ [] n))]))
                (eval-test '(Succ [] (Succ [] (Zero []))))))
