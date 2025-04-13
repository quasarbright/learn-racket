#lang racket

;; a different version of for inspired by haskell's list monad

;; TODO support sampling from arbitrary sequences and for/fold collection

(module+ test (require rackunit))
(require syntax-spec
         (for-syntax syntax/parse
                     paren-shape/pattern-expander))

(syntax-spec
  (binding-class loop-var #:reference-compiler immutable-reference-compiler)
  (extension-class loop-macro #:binding-space list-monad)
  (nonterminal/nesting clause (nested)
    #:binding-space list-monad
    #:allow-extension loop-macro
    (begin c:clause ...)
    #:binding (nest c ... nested)
    (when e:racket-expr)
    (do b:racket-body ...)
    #:binding (scope (import b) ... nested)
    ;; define is non-recursive
    (define x:loop-var e:racket-expr)
    #:binding (scope (bind x) nested)

    (~> (~brackets x:id e:expr)
        #'(<- x e))
    (<- x:loop-var e:racket-expr)
    #:binding (scope (bind x) nested)
    ;; TODO break, final
    e:racket-expr
    )
  (host-interface/expression
    (list-monad c:clause ...)
    #:binding (nest c ... [])
    (define/syntax-parse (c^ ...) (flatten-begins (attribute c)))
    #'(compile-clauses c^ ...)))

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
    #:datum-literals (when unless do define <-)
    [(_)
     #'(list)]
    [(_ (~or (when . _)
             (do . _)
             (define . _)
             (<- . _)))
     (raise-syntax-error 'list-monad "last clause must be a list expression" this-syntax)]
    [(_ e) #'e]
    [(_ c0 c ...)
     #'(compile-clause c0 (compile-clauses c ...))]))

(define-syntax compile-clause
  (syntax-parser
    #:datum-literals (when do define <-)
    [(_ (when condition) body)
     #'(if condition
           body
           (list))]
    [(_ (do b ...) body)
     #'(let ()
         b
         ...
         body)]
    [(_ (define x e) body)
     #'(let ([x e]) body)]
    [(_ (<- x e) body)
     #'(append-map (lambda (x) body) e)]
    [(_ e body)
     (raise-syntax-error 'list-monad "list expression can only be used as last clause" #'e)]))

(define-dsl-syntax unless loop-macro
  (syntax-rules ()
    [(unless e)
     (when (not e))]))

(module+ test
  (check-equal?
   (list-monad
    [x (list 1 2 3)]
    [y (list 4 5 6)]
    (list (* x y)))
   '(4 5 6
     8 10 12
     12 15 18))
  (check-equal?
   (list-monad
    [a (list 1 2 3 4 5)]
    [b (list 1 2 3 4 5)]
    [c (list 1 2 3 4 5)]
    (when (<= a b c))
    (define ab (+ (* a a) (* b b)))
    (when (= ab (* c c)))
    (list (list a b c)))
   '((3 4 5))))
