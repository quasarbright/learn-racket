#lang racket/base

(provide (all-defined-out) (for-space pm (all-defined-out)))

(require racket/list
         syntax-spec
         (for-syntax racket/base syntax/parse))

(syntax-spec
  (binding-class pat-var)
  (extension-class pat-macro #:binding-space pm)
  (nonterminal/two-pass pat
    #:allow-extension pat-macro
    #:binding-space pm
    x:pat-var
    #:binding (export x)
    (var x:pat-var)
    #:binding (export x)
    (and2 p1:pat p2:pat)
    #:binding [(re-export p1) (re-export p2)]
    (? pred:racket-expr)
    (app proc:racket-expr p:pat)
    #:binding (re-export p)
    (not p:pat)
    ; you don't want to export from a `not`
    #:binding {(recursive p)}
    (list p:lvp ...)
    #:binding (re-export p))
  (nonterminal/two-pass lvp
    #:allow-extension pat-macro
    #:binding-space pm
    (~literal ...)
    p:pat
    #:binding (re-export p))
  (nonterminal clause
    #:binding-space pm
    [p:pat body:racket-expr ...+]
    #:binding {(recursive p) body})
  (host-interface/expression
   (match target:racket-expr c:clause ...)
   #'(with-reference-compilers ([pat-var immutable-reference-compiler])
       (let ([target-pv target])
         (match-clauses target-pv c ...)))))

(define current-failure-proc (make-parameter 'unset))
; only call in tail, not an escape
(define (fail-match) ((current-failure-proc)))

(define-syntax match-clauses
  (syntax-parser
    [(_ target:id c ...)
     (syntax-parse #'(c ...)
       [() #'(error 'match "no matching clause for ~a" target)]
       [([p body ...+] c ...)
        #'(parameterize ([current-failure-proc (lambda () (match-clauses target c ...))])
            (do-match target p (begin body ...)))])]))

(define-syntax do-match
  (syntax-parser
    [(_ target:id pat on-success)
     (syntax-parse #'pat
       ; TODO something better then datum
       #:datum-literals (var and2 ? app not list)
       [x:id #'(let ([x target]) on-success)]
       [(var x:id) #'(let ([x target]) on-success)]
       [(and2 p1 p2)
        #'(do-match target p1 (do-match target p2 on-success))]
       [(? pred)
        #'(if (pred target)
              on-success
              (fail-match))]
       [(app proc p)
        #'(let ([new-target (proc target)])
            (do-match new-target p on-success))]
       [(not p)
        #'(let ([old-failure-proc (current-failure-proc)])
            (parameterize ([current-failure-proc (lambda () on-success)])
              (do-match target p (old-failure-proc))))]
       [(list lvp ...)
        #'(if (list? target)
              ; do-list-match may trash failure-proc for backtracking, so fix it to avoid redundant backtracks
              (let ([old-failure-proc (current-failure-proc)])
                (do-list-match target (lvp ...) (parameterize ([current-failure-proc old-failure-proc])
                                                  on-success)))
              (fail-match))])]))

(define-syntax do-list-match
  (syntax-parser
    [(_ target:id (lvp ...) on-success)
     (syntax-parse (attribute lvp)
       [() #'(do-match target (? null?) on-success)]
       [(p (~literal ...) lvp ...)
        #`(do-repeated-match target p target^ (do-list-match target^ (lvp ...) on-success))]
       [(p lvp ...)
        #'(if (cons? target)
              (let ([car-target (car target)]
                    [cdr-target (cdr target)])
                (do-match car-target p
                          (do-match cdr-target (list lvp ...) on-success)))
              (fail-match))])]))

(define-syntax do-repeated-match
  (syntax-parser
    ; greedily match the pattern on the list target.
    ; variables bound are bound to a list of their matches.
    ; binds resulting target list to target^ (after consuming matches).
    ; naive and greedy. (match '(1 1) [(list 1 ... 1) #t]) will fail bc 1 ... will eat it all up.
    ; TODO backtracking if you eat too much and cause the rest of the list to fail when it shouldn't
    [(_ target:id p target^:id on-success)
     (define/syntax-parse (v* ...) (bound-vars #'p))
     (define/syntax-parse (iter-v* ...) (generate-temporaries (attribute v*)))
     (define/syntax-parse (old-iter-v* ...) (generate-temporaries (attribute v*)))
     ; what you want is to parse this. then, try parsing more. if this ends up in an overall failure,
     ; then back track and don't parse this. Just pretend this parse failed and use on-success.
     ; what'll happen is you'll parse greedily. Then if that fails, you'll backtrack and parse 1 less
     ; and see if that worked. Then, you'll keep doing that until you succeed or backtrack into 0 parses.
     ; From the perspective of this call, it's either parse and continue or parse nothing and use on-success
     ; Only do set! after you know you don't need to backtrack. Then you may not need to reverse.
     #'(let ([iter-v* '()] ...)
         (let loop ([target^ target])
           ; match rest of lvps
           (define (continue)
             ; needs to be defined inside to close over target^
             (let ([v* (reverse iter-v*)] ...) on-success))
           (if (null? target^)
               (continue)
               (let ([first-target (first target^)])
                 ; save old state in case you need to backtrack
                 (define old-failure-proc (current-failure-proc))
                 (define old-iter-v* iter-v*) ...
                 ; if the individual match fails, continue to rest of lvps
                 (parameterize ([current-failure-proc (lambda () (continue))])
                   (do-match first-target p
                             ; individual match succeeded.
                             ; keep trying to match more. if a failure follows,
                             ; act like this match never happened and continue to rest of lvps
                             (parameterize ([current-failure-proc (lambda ()
                                                                    ; act like this match never happened and continue to rest of lvps
                                                                    (set! iter-v* old-iter-v*) ...
                                                                    (parameterize ([current-failure-proc old-failure-proc])
                                                                      (continue)))])
                               (set! iter-v* (cons v* iter-v*)) ...
                               (loop (rest target^)))))))))]))

(begin-for-syntax
  (define (bound-vars p)
    ; TODO
    (syntax-parse p
      #:datum-literals (var and2 ? app not list)
      [x:id (list #'x)]
      [(var x:id) (list #'x)]
      [(and2 p1 p2) (append (bound-vars #'p1) (bound-vars #'p2))]
      [(? _) '()]
      [(app _ p) (bound-vars #'p)]
      [(not _) '()]
      [(list p ...) (apply append (map bound-vars (attribute p)))])))

(define-syntax define-match-expander
  (syntax-parser
    [(_ name:id trans:expr)
     #`(define-syntax #,((make-interned-syntax-introducer 'pm) #'name 'add)
         (pat-macro trans))]))

(define-match-expander _
  (syntax-parser
    [(~datum _) #'ignored]))
(define-match-expander and
  (syntax-parser
    [(_) #'_]
    [(_ p0 p ...)
     #'(and2 p0 (and p ...))]))
(define-match-expander cons
  (syntax-parser
    [(_ car-pat cdr-pat)
     #'(and (? cons?)
            (app car car-pat)
            (app cdr cdr-pat))]))
(define-match-expander equal?
  (syntax-parser
    [(_ val)
     #'(? (lambda (x) (equal? x val)))]))
(define-match-expander quote
  (syntax-parser
    [(_ lit)
     #'(equal? 'lit)]))
(define-match-expander quasiquote
  (syntax-parser
    [(_ ((~datum unquote) p)) #'p]
    ; TODO unquote-splicing
    [(_ (qp-car . qp-cdr)) #'(cons `qp-car `qp-cdr)]
    [(_ x) #''x]))


(module+ test
  (require rackunit)
  (check-equal? (match 2 [x x]) 2)
  (check-equal? (match 2 [(? odd?) 'bad] [(? even?) 'good]) 'good)
  (check-equal? (match 2
                  [(and2 (? odd?) (? even?)) 'bad]
                  [(and2 (? even?) (? odd?)) 'bad]
                  [(and2 (? even?) (? even?)) 'good])
                'good)
  (check-equal? (match 2
                  [(app add1 x) x])
                3)
  (check-equal? (match 2
                  [(not (? even?)) 'bad]
                  [(not (? odd?)) 'good])
                'good)
  ; macro cons pattern
  (check-equal? (match '(1 2)
                  [(cons a _) a])
                1)
  ; doesn't shadow regular cons
  (check-equal? (cons 1 '(2)) '(1 2))
  ; doesn't shadow regular cons in match body
  (check-equal? (match '(1 2)
                  [(cons a b) (cons a b)])
                '(1 2))
  (check-equal? (match 1 [_ 2]) 2)
  (check-equal? (match 1 ['2 'bad] ['1 'good])
                'good)
  (check-equal? (match '(1 2)
                  [(list a b) (list b a)])
                '(2 1))
  (check-equal? (match '(1) [(var cons) cons]) '(1))
  ; currently an ambiguity error
  ;(check-equal? (match '(1) [(and (var cons) (cons a b)) (cons a b)]) '(1))
  (check-equal? (match '(1 a 2) [`(,a a ,b) (list a b)])
                '(1 2))
  ; pattern variables should not be in scope in expression positions of other patterns
  ; TODO this shouldn't work, but I don't think preventing that can be expressed in ss
  (check-equal? (match 2 [(and2 x (app (lambda (y) x) z)) (list x z)])
                '(2 2))
  ; TODO this fails, but in the racket expander, not the DSL expander.
  ; ss thinks it's ok because vars are exported in a recursive def ctx
  ; nesting would make it catch this, but the previous test would still wrongly work
  #;
  (check-equal? (match 2 [(and2 (app (lambda (y) x) z) x) (list x z)])
                '(2 2))
  ; lvp
  (check-equal? (match '(1 1 1) [(list '1 ...) #t])
                #t)
  (check-equal? (match '(1 1 1) [(list '2 ... '1 '1 '1) #t])
                #t)
  (check-equal? (match '((1 2) (3 4) (5 6))
                  [(list (list a b) ...) (list a b)])
                '((1 3 5) (2 4 6)))
  ; not naively greedy
  (check-equal? (match '(1 2 3 4 5)
                  [(list a ... '4 '5)
                   a]
                  [_ 'bad])
                '(1 2 3))
  ; make sure 'not' maintains bindings
  (check-equal? (match 1 [(and x (not (? even?)) y) (list x y)]) '(1 1))
  (check-equal? (match '(1 2 3 4 5) [(list a ... '20) 'bad] [_ 'good]) 'good)
  ; this will lead to extra backtracks if failure handler isn't properly maintained. this test would still pass, but slowly
  (check-equal? (match '(1 2 3 4 5) [(and (list a ...) (? (lambda (x) #f))) 'bad] [_ 'good])
                'good))
