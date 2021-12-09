#lang racket

(require macro-debugger/expand)

(module+ test (require rackunit))

;; Translates a program into continuation-passing-style
;; This is a global transformation and does not compose with other
;; macros
;; CPS-ing an expression `e` results in a function that takes in
;; a callback/continuation and calls it with the result of evaluating `e`
;; The continuation is a callback saying "what do you want to do with
;; the result?"
;; Nothing ever returns. "Returning" is just calling k with the result
(define-syntax CPS
  (syntax-rules (lambda let prim->CPS)
    ; special rule for lifting racket functions
    [(CPS (prim->CPS f)) (prim->CPS f)]
    ; take in an extra continuation argument and
    ; apply the CPS'ed body to it. The cont that
    ; is passed in will come from a function application
    [(CPS (lambda (x ...) body))
     (lambda (k) (k (lambda (x ... cont) ((CPS body) cont))))]
    ; expands to equivalent lambda. Should just be a macro
    [(CPS (let ([x e] ...) body)) (CPS ((lambda (x ...) body) e ...))]
    ; "get" the condition value,
    ; and pass k to either thn or els depending on its value
    [(CPS (if cnd thn els))
     (lambda (k)
       ((CPS cnd)
        (lambda (vcnd)
          (if vcnd
              ((CPS thn) k)
              ((CPS els) k)))))]
    ; application delegates to helper
    [(CPS (f x ...)) (CPS-app (f x ...))]
    ; constants and variable references just get wrapped
    [(CPS expr) (lambda (k) (k expr))]))

;; Helper macro that translates applications into CPS
;; Example:
#;{ (CPS-app (f x y))
    ->
    (lambda (k)
      ((CPS f)
       (λ (vf)
         ((CPS x)
          (λ (vx)
            ((CPS y)
             (λ (vy)
               (vf vx vy k))))))))}
;; It's like monadic bind, or callbacks
;; (CPS f) gives you a callback which is like
;; "What do you want to do with this?"
;; And you say "I want to do (lambda (vf) ...)"
;; And in the end, you call the function value
;; with all the arguments and the outer k,
;; since functions take in a continuation
(define-syntax CPS-app
  (syntax-rules ()
    ; initial case: wrap with a (lambda (k) ...) and initialize
    ; values and k accumulators
    [(CPS-app (f x ...)) (lambda (k) (CPS-app (f x ...) () k))]
    ; "bind" the result of e1 to v1, snoc it to the values
    [(CPS-app (e1 e2 ...) (v ...) k)
     ((CPS e1)
      (lambda (v1)
        (CPS-app (e2 ...) (v ... v1) k)))]
    ; We're done, apply the function to the arguments and k
    [(CPS-app () (v ...) k)
     (v ... k)]))

(define-syntax-rule (run-cps e) ((CPS e) identity))

(module+ test
  (check-equal? (run-cps 1) 1)
  (check-equal? (run-cps ((lambda (x) x) 1)) 1)
  (check-equal? (run-cps (let ([id (lambda (x) x)]) (id 1))) 1)
  (check-equal? (run-cps (let ([x 1] [y 2]) y)) 2)
  (check-equal? (run-cps ((lambda () 1))) 1)
  (check-equal? (run-cps (if #t 1 0)) 1)
  (check-equal? (run-cps (if #f 1 0)) 0))

;; Convert a primitive racket function to CPS-land
;; Doesn't work with higher-order functions
(define (prim->CPS f)
  (define (f-cps . args)
    (match args
      [(list args ... k) (k (apply f args))]))
  (lambda (k) (k f-cps)))

; Doesn't work, need some extra wrapping
#;(define +/cps (prim->CPS +))

(module+ test
  (check-equal? (run-cps ((prim->CPS +) 1 2)) 3)
  (check-equal? (run-cps ((prim->CPS +) 1 2 3 4)) 10)
  (check-equal? (run-cps ((prim->CPS +))) 0)
  #;(check-equal? (run-cps (+/cps 1 2)) 3))

;; call/cc
;; Callable from CPS-land
(define (call-k f k)
  ; f is the function passed to call-k.
  ; this lambda is the k that f uses to abort.
  ; Since f may call it, it needs to look like a user-level
  ; lambda (lambda (arg cont) ...)
  ; This lambda will be called with some value and
  ; some other continuation, and will call the old
  ; continuation on that value, ignoring cont.
  ; cont contains the program up to abort, I think
  (f (lambda (val cont) (k val)) k))
;; If you wanted algebraic effects, you wouldn't ignore cont.
;; You'd pass cont to the handler, and it would resume
;; by calling cont with something. Use similar mechanism to
;; exception handling for bubbling cont up.

(define saved-k #f)
;; Like call-k, except it saves the continuation
;; to saved-k. Using this, you can resume the program
;; from that point by filling in the hole,
;; even after it finishes running
(define (call-k/save f k)
  (set! saved-k k)
  (call-k f k))

(module+ test
  (check-equal? (run-cps (call-k (lambda (k) (k 1)))) 1)
  (check-equal? (run-cps (call-k (lambda (k) ((prim->CPS +) 2 (k 3)))))
                3)
  (check-equal? (run-cps (let ([x (call-k (lambda (k) (k 3)))]) x))
                3)
  (check-equal? (run-cps (let ([x (call-k (lambda (k) (k 3)))]) 2))
                2)
  (check-equal? (run-cps (let ([x (call-k (lambda (k) 1))]) ((prim->CPS +) x 2)))
                3)
  (check-equal? (run-cps (let ([x (call-k/save (lambda (k) 1))]) ((prim->CPS +) x 3))) 4)
  (check-equal? (saved-k 2) 5)
  (check-equal? (saved-k 4) 7))

