#lang racket

; zfc++

(module+ test (require rackunit))

(require "algebraic-effect-2.rkt")

; An Expr is a
; (Set Expr ...)
; (! Expr)
; (~ Expr)
; (symbol Expr ...)

; A Defns is a (listof Defn)
; A Defn is a (define (symbol symbol ...) Expr)

; A Program is a (list Defns Expr)

; A Value is a (set-of Value)

; A Function is a ((listof Value) -> Value)

; An Env is a
(struct env [funcs vals] #:transparent)
; Where
; funcs is a (hash/c symbol Function)
; vals is a (hash/c symbol Value)

;; effects


; non-determinism via sets

(define (handler s k)
  (self-union (for/set ([v s])
     (k v))))

; (set-of (set-of X)) -> (set-of X)
(define (self-union sets)
  (for/fold ([union (set)])
            ([s sets])
    (set-union union s)))

(define-syntax-rule (with-branching body ...)
  (with-effect-handler handler (set (let () body ...))))

(define (branch s) (perform s))

(module+ test
  (check-equal?
   (with-branching
     (list (branch (set 1 2 3)) (branch (set 4 5 4))))
   (set '(1 4) '(1 5) '(2 4) '(2 5) '(3 4) '(3 5)))
  (check-equal?
   (with-branching
     (list (branch (set (with-branching 1) 2 3)) (branch (set 4 5 4))))
   (set (list (set 1) 4) (list (set 1) 5) '(2 4) '(2 5) '(3 4) '(3 5))))

; Env Expr -> Value
(define (eval env expr)
  (match expr
    [(? symbol?)
     ; singleton
     (hash-ref (env-vals env) expr (lambda () (error 'eval "unbound value reference: ~a" expr)))]
    [`(~ ,expr)
     (branch (eval env expr))]
    [(cons rator rands)
     (define func (hash-ref (env-funcs env) rator (lambda () (error 'eval "unbound function reference: ~a" rator))))
     (define arg-lists
       (with-branching
         (for/list ([rand rands])
           (eval env rand))))
     (self-union (for/set ([args arg-lists])
                   (func args)))]))

; Program -> Value
(define (run prog)
  (match prog
    [(list defns expr)
     (define env (run-defns defns))
     (eval env expr)]))

; (listof Defn) -> Env
(define (run-defns defns)
  (define funcs (initial-funcs))
  (for ([defn defns])
    (run-defn! defn funcs))
  (env funcs (hasheq)))

; Defn (hash/c symbol? Function) -> Void
(define (run-defn! defn funcs)
  (match defn
    [`(define (,name ,argnames ...)
        ,body)
     (define (func sets)
       (unless (= (length argnames) (length sets))
         (error name "arity error. Expected ~a arguments, but got ~a" (length argnames) (length sets)))
       (define vals
         (for/hasheq ([argname argnames]
                      [s sets])
           (values argname s)))
       (eval (env funcs vals) body))
     (hash-set! funcs name func)]))

(define (builtin-set sets)
  (apply set sets))

(define (builtin-! sets)
  (match sets
    [(list s)
     (if (set-empty? s)
         (set (set))
         (set))]
    [_ (error '! "arity error. Unary operator received ~a arguments" (length sets))]))

(define prelude
  '((define (id x) x)
    (define (self-union x) (id (~ x)))
    (define (union x y) (self-union (set x y)))
    (define (not x) (! x))
    (define (bool x) (not (not x)))
    (define (false) (set))
    (define (true) (set (set)))
    (define (if1 x y) y)
    (define (if cnd thn els)
      (union (if1 (~ x) y) (if1 (~ (not x)) z)))
    (define (and x y)
      (if x y x))
    (define (or x y)
      (if x x y))
    (define (xor x y)
      (if x (not y) y))
    (define (any x) (self-union x))
    (define (all x) (not (any (map-not x))))
    (define (map-not x) (map-not1 (~ x)))
    (define (map-not1 x) (set (not x)))
    (define (equal? x y)
      (and (subset? x y) (subset? y x)))
    (define (subset? x y)
      (all (subset?1 (~ x) y)))
    (define (subset?1 x y)
      (set (set-member? x y)))
    (define (set-member? s x)
      (any (set-member?1 (~ s) x)))
    (define (set-member?1 x y)
      (set (equal? x y)))
    ; TODO
    #;(define (intersection x y)
      )))

(define (initial-funcs) (make-hasheq (list (cons 'set builtin-set) (cons '! builtin-!))))

(module+ test
  (check-equal?
   (run '(() (set)))
   (set))
  (check-equal?
   (run '(((define (f x) x))
          (f (set (set)))))
   (set (set)))
  (check-equal?
   (run '(((define (f x y) x))
          (f (set (set)) (set))))
   (set (set)))
  (check-equal?
   (run '(((define (f x y) (set x y)))
          (f (set (set) (set (set))) (set (set (set))))))
   (set (set (set) (set (set))) (set (set (set)))))
  (check-equal?
   (run '(((define (f x y) (set x y)))
          (f (~ (set (set) (set (set)))) (set (set (set))))))
   (set (set) (set (set)) (set (set (set))))))
