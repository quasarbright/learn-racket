#lang racket

;; A different version of for*-like loops inspired by haskell's list monad.
;; It's essentially some nice syntax over generators and reducers.

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
    (begin c:clause ...)
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
    (loop/host c:clause ...)
    #:binding (nest c ... [])
    (define/syntax-parse (c^ ...) (flatten-begins (attribute c)))
    #'(in-generator (let () (compile-clauses c^ ...)))))

(define-syntax loop
  (syntax-parser
    [(loop (~optional (~seq #:collector collector) #:defaults ([collector #'void])) c ...)
     #'(collector (loop/host c ...))]))

(begin-for-syntax
  (define flatten-begins
    (syntax-parser
      [() #'()]
      [(c0 c ...)
       (syntax-parse #'c0
         #:literals (begin)
         [(begin c^ ...)
          (flatten-begins #'(c^ ... c ...))]
         [_
          (define/syntax-parse (c^ ...) (flatten-begins #'(c ...)))
          #'(c0 c^ ...)])])))

#|
do
  x <- xs
  y < ys
  return (x + y)
~>
xs >>= \x -> ys >>= \y -> [x + y]
|#

(define-syntax compile-clauses
  (syntax-parser
    #:datum-literals (when <-)
    [(_)
     #'(void)]
    [(_ (~or (when . _)
             (<- . _)))
     (raise-syntax-error 'list-monad "last clause must be a regular racket expression" this-syntax)]
    [(_ e) #'(yield e)]
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

#;
(define-dsl-syntax when loop-macro
  (syntax-rules ()
    [(when e)
     [_ (if e (list #f) (list))]]))
(define-dsl-syntax unless loop-macro
  (syntax-rules ()
    [(unless e)
     (when (not e))]))

(define-syntax for/fold/loop
  ;; TODO unclear how this should/could work
  'todo)

#;; this is what I want
(for/fold/loop ([sum 0])
  [x lst]
  (+ sum x))

;; collectors
(define (sum seq) (for/sum ([x seq]) x))
(define (product seq)
  (for/fold ([product 1])
            ([x seq])
    (* product x)))
(define (all seq) (for/and ([x seq]) x))
(define (some seq) (for/or ([x seq]) x))
(define (to-list seq) (sequence->list seq))
(define (to-hash seq) (for/hash ([(k v) seq]) (values k v)))
(define (to-set seq) (for/set ([x seq]) x))

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
