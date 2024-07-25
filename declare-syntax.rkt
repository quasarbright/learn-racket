#lang racket

(provide declare-syntax)
(module+ test (require rackunit))
(require racket/hash (for-syntax syntax/parse))

; an implementation of https://dl.acm.org/doi/pdf/10.1145/41625.41632
; which is basically syntax-rules

; an Env is a (Hash Symbol (cons Natural SExp))
; mapping a name to its ellipsis depth and the source SExp

; a Pat is one of
; Symbol
; ()
; (Pat . Pat)
; (Pat ooo)
; ooo means an ellipsis in the pattern itself
; So ellipsis can only appear at the end of a pattern
; Represents a syntax pattern

; A Template is one of
; Pat
; (Pat ooo . Pat)
; It's a Pat but ellipsis doesn't have to appear at the very end

; We're building declare-syntax, which is like
; (define-syntax
;   (declare-syntax name [pat tmp] ...+)
;   (define-syntax name (syntax-rules () [pat tmp] ...)))
; but it works on s-expressions and has no hygiene

(define-syntax-rule
  (declare-syntax name [pat tmp] ...)
  (begin
    (define (trans expr) (run-syntax-rules 'name expr (list (list 'pat 'tmp) ...)))
    (define-syntax name
      (syntax-parser
        [stx #'(trans 'stx)]))))

(module+ test
  (declare-syntax id
                  [(id e) e])
  (check-equal? (id x) 'x)
  (let ()
    (declare-syntax let
                    [(let ([x e] ...) body)
                     ((lambda (x ...) body) e ...)])
    (check-equal? (let ([x one] [y two]) (+ x y))
                  '((lambda (x y) (+ x y)) one two)))
  (let ()
    (declare-syntax or
                    [(or) true]
                    [(or a) a]
                    ; don't worry about hygiene
                    [(or a b) (if a a b)]
                    [(or e es ...) (or e (or es ...))])
    (check-equal? (or) 'true)
    (check-equal? (or x) 'x)
    (check-equal? (or x y) '(if x x y))
    (check-equal? (or w x y z)
                  '(or w (or x y z)))))

; Symbol SExpr (Listof (List Pat Template)) -> SExpr
(define (run-syntax-rules who-sym expr clauses)
  (match clauses
    [(cons (list pat tmp) rest-clauses)
     (if (pattern-matches? pat expr)
         (let ([env (pattern-match pat expr)])
           (template-expand tmp env))
         (run-syntax-rules who-sym expr rest-clauses))]
    [_ (error who-sym "bad syntax")]))

(module+ test
  (check-equal? (run-syntax-rules 'id '(id x) '([(id e) e]))
                'x)
  (check-equal? (run-syntax-rules 'let '(let ([x one] [y two]) (+ x y))
                                  '([(let ([x e] ...) body)
                                     ((lambda (x ...) body) e ...)]))
                '((lambda (x y) (+ x y)) one two)))

; Pat SExpr -> Boolean
; Does the pattern match the expr?
(define (pattern-matches? pat expr)
  (match (list pat expr)
    ['... (error 'declare-syntax "invalid use of ellipsis")]
    [(list (? symbol?) _) #t]
    [(list '() '()) #t]
    [(list (list pat '...)
           (? list? exprs))
     (andmap (lambda (expr) (pattern-matches? pat expr))
             exprs)]
    [(list (cons car-pat cdr-pat)
           (cons car-expr cdr-expr))
     (and (pattern-matches? car-pat car-expr)
          (pattern-matches? cdr-pat cdr-expr))]
    [_ #f]))

(module+ test
  (check-true (pattern-matches? 'x '()))
  (check-true (pattern-matches? '() '()))
  (check-false (pattern-matches? '() 'b))
  (check-false (pattern-matches? '() '(a b)))
  (check-true (pattern-matches? '(a b) '(a (b c))))
  (check-false (pattern-matches? '(a b) 'a))
  (check-true (pattern-matches? '(a ...) '(a b c d e))))

; Pat SExpr -> Env
; Build up the environment mapping pattern variables to
; parts of the input SExpr.
; Assumes the pattern matches.
(define (pattern-match pat expr)
  (match (list pat expr)
    [(list (? symbol? id) expr)
     (hasheq id (cons 0 expr))]
    [(list '() '()) (hasheq)]
    [(list (list pat '...)
           exprs)
     (define envs
       (for/list ([expr exprs])
         (pattern-match pat expr)))
     (define env^ (combine-envs envs))
     ; this is necessary in case expr is '(). You'd get an empty environment.
     (for/hasheq ([id (pattern-bound-vars pat)])
       (values id (hash-ref env^ id '())))]
    [(list (cons car-pat cdr-pat)
           (cons car-expr cdr-expr))
     (hash-union (pattern-match car-pat car-expr)
                 (pattern-match cdr-pat cdr-expr)
                 #:combine/key (lambda (id _ __) (error 'declare-syntax "duplicate pattern variable ~a" id)))]
    [_ (error 'pattern-match "pattern didn't match")]))

(module+ test
  (check-equal? (pattern-match 'a '()) (hasheq 'a (cons 0 '())))
  (check-equal? (pattern-match '(a b) '(c d)) (hasheq 'a (cons 0 'c) 'b (cons 0 'd)))
  (check-equal? (pattern-match '(a ...) '(b c d))
                (hasheq 'a (cons 1 '(b c d))))
  (check-equal? (pattern-match '(a b ...) '(x y z))
                (hasheq 'a (cons 0 'x)
                        'b (cons 1 '(y z))))
  (check-equal? (pattern-match '(let ([x e] ...) body)
                               '(let ([x one] [y two]) (+ x y)))
                (hasheq 'let (cons 0 'let)
                        'x (cons 1 '(x y))
                        'e (cons 1 '(one two))
                        'body (cons 0 '(+ x y))))
  (check-equal? (pattern-match '(cond [cnd body ...] ...)
                               '(cond [good? one two]
                                      [bad? three four]))
                (hasheq 'cond (cons 0 'cond)
                        'cnd (cons 1 '(good? bad?))
                        'body (cons 2 '((one two) (three four))))))

; (Listof Env) -> Env
; combines the environments of an ellipsis sub-pattern's matches
(define (combine-envs envs)
  (define envs^
    (for/list ([env envs])
      (hash-map/copy env
                     (lambda (k v)
                       (match v
                         [(cons depth expr)
                          (values k (cons (add1 depth) (list expr)))])))))
  (apply hash-union
         envs^
         #:combine (lambda (info1 info2) (cons (car info1) (append (cdr info1) (cdr info2))))))

; Pat -> (Listof Symbol)
(define (pattern-bound-vars pat)
  (match pat
    [(? symbol? id) (list id)]
    ['() '()]
    [(list pat '...)
     (pattern-bound-vars pat)]
    [(cons car-pat cdr-pat) (append (pattern-bound-vars car-pat)
                                    (pattern-bound-vars cdr-pat))]
    [_ (error 'pattern-bound-vars "invalid pattern: ~a" pat)]))

; Template Env -> Expr
(define (template-expand tmp env)
  (match tmp
    [(? symbol? id)
     (define info (hash-ref env id #f))
     (match info
       ; unbound identifier in template expands to itself
       [#f id]
       [(cons depth expr)
        (unless (zero? depth)
          (error 'declare-syntax "missing ellipsis with pattern variable in template: ~a" id))
        expr])]
    ['() '()]
    [(list* tmp '... cdr-tmp)
     (foldr cons
            (template-expand cdr-tmp env)
            (template-expand/ellipsis tmp env))]
    [(cons car-tmp cdr-tmp)
     (cons (template-expand car-tmp env)
           (template-expand cdr-tmp env))]))

(module+ test
  (check-equal? (template-expand 'a (hasheq 'a (cons 0 'b)))
                'b)
  (check-equal? (template-expand '(a b) (hasheq 'a (cons 0 'c)
                                                'b (cons 0 'd)))
                '(c d))
  (check-equal? (template-expand '(a ...) (hasheq 'a (cons 1 '(b c d))))
                '(b c d)))

; Template Env -> (Listof SExpr)
; expand an ellipsis sub-template for each expr in the env
(define (template-expand/ellipsis tmp env)
  (define fvs (template-free-variables tmp))
  (define filtered-env
    (for/hasheq ([(id v) (in-hash env)]
                 #:when (member id fvs))
      (values id v)))
  (define envs (env-split filtered-env))
  (for/list ([env envs])
    (template-expand tmp env)))

; Template -> (Listof Symbol)
(define (template-free-variables tmp)
  (match tmp
    [(? symbol? id) (list id)]
    ['() '()]
    [(or (list* tmp '... cdr-tmp)
         (cons tmp cdr-tmp))
     (append (template-free-variables tmp)
             (template-free-variables cdr-tmp))]))

; Env -> (Listof Env)
; Split an environment containing deep variables into an environment per match
(define (env-split env)
  (define repetition-length (env-repetition-length env))
  (for/list ([i (in-range repetition-length)])
    (for/hasheq ([(id info) (in-hash env)])
      (match info
        [(cons 0 _) (values id info)]
        [(cons n exprs)
         (values id (cons (sub1 n) (list-ref exprs i)))]))))

; Env -> Natural
; How many times does the (ellipsis-template-filitered) environment repeat?
; Should be the same for all deep vars. Error if not.
(define (env-repetition-length env)
  (define repetition-length #f)
  (for ([(id info) (in-hash env)])
    (match-define (cons depth exprs) info)
    (unless (zero? depth)
      (cond
        [repetition-length
         (unless (= repetition-length (length exprs))
           (error 'declare-syntax "incompatible ellipsis match counts for template"))]
        [else (set! repetition-length (length exprs))])))
  (unless repetition-length
    (error 'declare-syntax "too many ellipses in template"))
  repetition-length)

(module+ test
  (check-exn
   #rx"too many ellipses in template"
   (lambda ()
     (declare-syntax foo [(foo a) (foo a ...)])
     (foo b)))
  (check-exn
   #rx"missing ellipsis with pattern variable in template: a"
   (lambda ()
     (declare-syntax foo [(foo a ...) (foo a)])
     (foo b)))
  (declare-syntax zip [(zip (a ...) (b ...)) ((a b) ...)])
  (check-equal? (zip (a b c) (x y z))
                '((a x) (b y) (c z)))
  (check-exn
   #rx"incompatible ellipsis match counts for template"
   (lambda ()
     (zip (a b) (x y z))))
  (declare-syntax flatten [(flatten (a ...) ...) (a ... ...)])
  ; skipped, our template parsing doesn't understand this as a double splice
  #;(check-equal? (flatten (foo bar) (baz)) '(foo bar baz)))
