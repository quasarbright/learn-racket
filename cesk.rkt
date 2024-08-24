#lang racket

; https://matt.might.net/articles/cesk-machines/

(require racket/hash)

#|
lam := (lambda (var ...) exp)
aexp := lam
      | var
      | #t | #f
      | integer
      | (prim aexp ...)
cexp := (aexp ...+)
      | (if aexp exp exp)
      | (call/cc aexp)
      | (set! var aexp)
      | (letrec ([var aexp] ...) exp)
exp := aexp
     | cexp
     | (let ((var exp)) exp)
prim = + | - | * | equal?

val := void | number | #t | #f | (clo lam env) | (cont k)

env is a (hasheq var addr) (immutable)

addr is a gensym

store is a (hasheq addr val) (immutable)

k := halt | (letk var expr env k)

st := (state exp env store k)
|#

; atomic expression. supposed to have no side effects and guaranteed to terminate.
; but prims can throw errors.
(define (aexp? e)
  (match e
    [(or `(lambda ,(list (? symbol?) ...) ,(? exp?))
         (cons (? prim?) (list (? aexp?) ...))
         (? symbol?)
         (? number?)
         (? boolean?))
     #t]
    [_ #f]))

; complex expression.
(define (cexp? e)
  (match e
    [(or (list (? aexp?) ...)
         `(if ,(? aexp?) ,(? exp?) ,(? exp?))
         `(call/cc ,(? aexp?))
         `(set! ,(? symbol?))
         `(letrec ([,(? symbol?) ,(? aexp?)] ...) ,(? exp?)))
     #t]
    [_ #f]))

(define (exp? e)
  (match e
    [(or (? aexp?)
         (? cexp?)
         `(let ([,(? symbol?) ,(? exp?)]) ,(? exp?)))
     #t]
    [_ #f]))

(struct clo [lam env] #:transparent)
(struct cont [k] #:transparent)

; k is one of
(struct letk [var exp env k] #:transparent)
; represents a continuation where the result gets bound to var in exp
; and then continue in k.
; basically (lambda (var) exp) closing over env.
(struct halt [] #:transparent)

; st is a
(struct st [exp env store k] #:transparent)

(define prims
  (hasheq
   '+ +
   '- -
   '* *
   'equal? equal?))
(define (prim? v) (hash-has-key? prims v))

(define (st0 exp)
  (st exp (hasheq) (hasheq) (halt)))

; expr -> val
(define (eval exp)
  (match-define
    (st aexp env store (halt))
    ; wrap exp with let so the program never sees a halt
    (step* (st0 `(let ([x ,exp]) x))))
  (eval-aexp aexp env store))

; st -> st
; step until done
(define (step* state)
  (if (and (aexp? (st-exp state)) (halt? (st-k state)))
          state
          (step* (step state))))

; st -> st
(define (step state)
  (match-define (st exp env store k) state)
  (match exp
    [(? aexp? aexp)
     (apply-cont k (eval-aexp aexp env store) store)]
    [`(if ,(? aexp? cnd) ,thn ,els)
     (if (eval-aexp cnd env store)
         (st thn env store k)
         (st els env store k))]
    [`(let ([,x ,rhs]) ,body)
     (define k^ (letk x body env k))
     (st rhs env store k^)]
    [`(set! ,x ,aexp)
     (define store^ (mutate-var x env store (eval-aexp aexp env store)))
     (apply-cont k (void) store^)]
    [`(letrec ([,xs ,aexps] ...) ,body)
     (define addrs (for/list ([_ xs]) (new-addr)))
     (define env^ (hash-union env (for/hasheq ([x xs]
                                               [addr addrs])
                                    (values x addr))))
     (define vals (for/list ([aexp aexps]) (eval-aexp aexp env^ store)))
     (define store^ (hash-union store (for/hasheq ([addr addrs]
                                                   [val vals])
                                        (values addr val))))
     (st body env^ store^ k)]
    [`(call/cc ,(? aexp? aexp))
     (define proc (eval-aexp aexp env store))
     (define val/cc (cont k))
     (apply-proc proc (list val/cc) store k)]
    ; procedure application
    [(list (? aexp? proc-aexp) (? aexp? arg-aexps) ...)
     ; rands are aexps
     (define proc (eval-aexp proc-aexp env store))
     (define args (for/list ([arg-aexp arg-aexps]) (eval-aexp arg-aexp env store)))
     (apply-proc proc args store k)]
    [_ (error 'eval "invalid exp ~a" exp)]))

; aexp env store -> val
(define (eval-aexp aexp env store)
  (match aexp
    [`(lambda . ,_)
     (clo aexp env)]
    [(? symbol? var)
     (var-lookup var env store)]
    [`(,(? prim? prim) ,arg-aexps ...)
     (apply (hash-ref prims prim)
            (for/list ([arg-aexp arg-aexps])
              (eval-aexp arg-aexp env store)))]
    [(cons _ _) (error 'eval-aexp "invalid aexp ~a" aexp)]
    ; integer or boolean
    [_ aexp]))

(define (var-lookup var env store)
  (store-lookup store (env-lookup env var)))

(define (env-lookup env var)
  (hash-ref env var (lambda () (error 'eval "unbound variable ~a" var))))

(define (store-lookup store addr)
  (hash-ref store
            addr
            (lambda () (error 'eval "unbound address ~a" addr))))

(define (mutate-var var env store val)
  (hash-set store (env-lookup env var) val))

(define (new-addr) (gensym 'addr))

; val (listof val) store k -> val
(define (apply-proc proc args store k)
  (match proc
    [(clo `(lambda ,vars ,body) env)
     (unless (= (length args) (length vars))
       (error 'eval "arity error"))
     (define addrs (for/list ([_ vars]) (new-addr)))
     (define env^ (hash-union env (for/hasheq ([var vars]
                                               [addr addrs])
                                    (values var addr))))
     (define store^ (hash-union store (for/hasheq ([addr addrs]
                                                   [val args])
                                        (values addr val))))
     (st body env^ store^ k)]
    [(cont k)
     (match args
       [(list arg)
        (apply-cont k arg store)]
       [_ (error 'eval "arity error")])]
    [_ (error 'eval "application of non-procedure")]))

(define (apply-cont k val store)
  (match k
    [(letk var exp env k)
     (define addr (new-addr))
     (st exp (hash-set env var addr) (hash-set store addr val) k)]
    [(halt) (assert-unreachable)]))

(module+ test
  (require rackunit)
  (check-equal? (eval 1)
                1)
  (check-equal? (eval '(+ 1 1))
                2)
  (check-equal? (eval '(if #t 1 2))
                1)
  (check-equal? (eval '(let ([x 1]) x))
                1)
  (check-equal? (eval '((lambda (x) x) 1))
                1)
  (check-equal? (eval '(let ([x 1]) (let ([_ (set! x 2)]) x)))
                2)
  (check-equal? (eval '(+ (+ 1 2) (+ 3 4)))
                10)
  (check-equal? (eval '(letrec ([fac (lambda (n) (if (equal? n 0) 1 (let ([tmp (fac (- n 1))]) (* n tmp))))])
                         (fac 4)))
                24)
  ; TODO test call/cc more thoroughly. hard to make an interesting case with anf
  (check-equal? (eval '(call/cc (lambda (k) (k 1))))
                1)
  (check-equal? (eval '(let ([x (call/cc (lambda (k) (k 1)))]) x))
                1))
