#lang racket

;; A different version of for*-like loops inspired by haskell's list monad.
;; It's essentially some nice syntax over generators and reducers.
;; NOTE: mutually recursive definitions may not work in loop body.
;; NOTE: loop uses generators internally, so yielding from inside the loop body will break stuff.

;; TODO abstract away generator. use custom algebraic effect

(provide
 loop
 loop/fold
 ;; loop macros
 unless
 ;; collectors
 sum
 product
 all
 some
 to-list
 to-hash
 to-set
 collect-first
 collect-last)
(module+ test (require rackunit))
(require racket/generator
         syntax-spec
         (for-syntax syntax/parse
                     paren-shape/pattern-expander))

;; example
(module+ test
  (check-equal?
   (loop
    #:collector to-list
    ;; like haskell do's <-
    ;; square brackets are required for recognition
    [a (in-range 1 20)]
    [b (in-range 1 20)]
    ;; like haskell do's let
    (define a2b2 (+ (* a a) (* b b)))
    [c (in-range 1 20)]
    (define c2 (* c c))
    ;; like haskell's guard
    (when (<= a b c))
    (when (= 1 (gcd a b c)))
    (when (= a2b2 c2))
    ;; implicit haskell return
    (list a b c))
   '((3 4 5)
     (5 12 13)
     (8 15 17))))

(syntax-spec
  (binding-class loop-var #:reference-compiler immutable-reference-compiler)
  (extension-class loop-macro #:binding-space loop)
  (nonterminal/nesting clause (nested)
    #:binding-space loop
    #:allow-extension loop-macro

    (begin/loop c:clause ...)
    #:binding (nest c ... nested)

    (when e:racket-expr)

    (~> (~brackets x:id e:expr)
        #'(<- x e))
    (~> (~brackets (x:id ...) e:expr)
        #'(<- (x ...) e))
    (<- x:loop-var e:racket-expr)
    #:binding (scope (bind x) nested)
    (<- (x:loop-var ...) e:racket-expr)
    #:binding (scope (bind x) ... nested)

    ;; TODO break, final

    ;; NOTE this makes mutually recursive definitions impossible
    b:racket-body
    #:binding (scope (import b) nested))
  (host-interface/expression
    (loop/host #:arity arity:number c:clause ...)
    #:binding (nest c ... [])
    (define/syntax-parse (c^ ...) (flatten-begins (attribute c)))
    #'(in-generator #:arity arity (let () (compile-clauses c^ ...)))))

(define-syntax loop
  (syntax-parser
    [(loop (~alt (~optional (~seq #:collector collector) #:defaults ([collector #'void]))
                 (~optional (~seq #:arity arity:number) #:defaults ([arity #'1])))
           ...
           c
           ...)
     #'(collector (loop/host #:arity arity c ...))]))

(begin-for-syntax
  (define flatten-begins
    (syntax-parser
      [() #'()]
      [(c0 c ...)
       (syntax-parse #'c0
         ;; it's suboptimal that this has to be a datum literal
         #:datum-literals (begin/loop)
         [(begin/loop c^ ...)
          (flatten-begins #'(c^ ... c ...))]
         [_
          (define/syntax-parse (c^ ...) (flatten-begins #'(c ...)))
          #'(c0 c^ ...)])])))

(define-syntax compile-clauses
  (syntax-parser
    #:datum-literals (when <-)
    [(_)
     #'(void)]
    [(_ (~or (when . _)
             (<- . _)))
     (raise-syntax-error 'list-monad "last clause must be a regular racket expression" this-syntax)]
    [(_ e) #'(call-with-values (lambda () e) yield)]
    [(_ c0 c ...)
     #'(compile-clause c0 (compile-clauses c ...))]))

(define-syntax compile-clause
  (syntax-parser
    #:datum-literals (when do <-)
    [(_ (when condition) body)
     #'(when condition
         body)]
    [(_ (<- lhs e) body)
     #'
     (for ([lhs e])
       body)]
    [(_ e body)
     #'(begin e body)]))

;; yield everything from the sequence
(define (yield* seq)
  (for ([v seq]) (yield v)))

(define-dsl-syntax unless loop-macro
  (syntax-rules ()
    [(unless e)
     (when (not e))]))

(define-syntax loop/fold
  (syntax-parser
    [(_ ([x init] ...) c ... final)
     (define/syntax-parse (x^ ...) (generate-temporaries (attribute x)))
     (define/syntax-parse arity (length (attribute x)))
     #'(let ([x init] ...)
         (loop
          #:arity arity
          ;; gives the last iteration's values
          #:collector (lambda (seq) (for/fold ([x^ #f] ...) ([(x ...) seq]) (values x ...)))
          (yield x ...)
          c
          ...
          (let-values ([(x^ ...) (let () final)])
            (set! x x^)
            ...
            (values x ...))))]))

(module+ test
  (check-equal?
   (loop/fold ([sum 0])
     [x (in-range 5)]
     (when (even? x))
     (+ sum x))
   6)
  (test-case "fold with multiple values"
    (define-values (sum product)
      (loop/fold ([sum 0]
                      [product 1])
        [x (in-range 1 5)]
        (when (even? x))
        (values (+ sum x)
                (* product x))))
    (check-equal? sum 6)
    (check-equal? product 8)))

;; collectors
(define-syntax-rule (for->collector for/xyz)
  (lambda (seq) (for/xyz ([x seq]) x)))
(define sum (for->collector for/sum))
(define (product seq)
  (for/fold ([product 1])
            ([x seq])
    (* product x)))
(define all (for->collector for/and))
(define some (for->collector for/or))
(define to-list (for->collector for/list))
(define (to-hash seq) (for/hash ([(k v) seq]) (values k v)))
(define to-set (for->collector for/set))
(define collect-first (for->collector for/first))
(define collect-last (for->collector for/last))

(module+ test
  (check-equal?
   (loop
    #:collector to-list
    [x (list 1 2 3)]
    [y (list 4 5 6)]
    (* x y))
   '(4 5 6
     8 10 12
     12 15 18))
  (check-equal?
   (loop
    #:collector to-list
    [a (list 1 2 3 4 5)]
    [b (list 1 2 3 4 5)]
    [c (list 1 2 3 4 5)]
    (when (<= a b c))
    (define ab (+ (* a a) (* b b)))
    (when (= ab (* c c)))
    (list a b c))
   '((3 4 5))))
