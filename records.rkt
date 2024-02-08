#lang racket

(module+ test (require rackunit))
(require (for-syntax syntax/parse syntax/parse/lib/function-header)
         racket/hash)

; something like js records
; features:
; x identifier-based, asbtract away symbols or whatever
; x easy de-structuring and creation
; x integrate with match
; x something like `const x = 1; const obj = {x};`
; x spread? or just have a merge operation
; x chain field access
; x chain field setting

; A (record/c X) is a (hash/c symbol? X)
(define (record/c c) (and/c (hash/c symbol? c) hash-eq?))
(define (record? rcd) (and (hash-eq? rcd) (for/and ([(k v) (in-hash rcd)]) (symbol? k))))

(define-syntax make-record
  (syntax-parser
    [(_ pair ...)
     #'(make-immutable-hasheq (make-record/assocs pair ...))]))

(define-syntax make-record/assocs
  (syntax-parser
    [(_) #''()]
    [(_ [name:id val] pair ...)
     #'(cons (cons 'name val) (make-record/assocs pair ...))]
    [(_ [header:function-header body ...+] pair ...)
     #'(cons (cons 'header.name (let () (define header body ...) header.name)) (make-record/assocs pair ...))]
    [(_ name:id pair ...)
     #'(cons (cons 'name name) (make-record/assocs pair ...))]))

(define-syntax-rule (record-get rcd name) (hash-ref rcd 'name))
(define-syntax-rule (record-get* rcd name ...)
  (for/fold ([val rcd])
            ([name^ (list 'name ...)])
    (hash-ref val name^)))
(define-syntax-rule (record-set rcd name val) (hash-set rcd 'name val))
(define-syntax record-set*
  (syntax-parser
    [(_ rcd name ...+ val) #'(record-set*/rt rcd (list 'name ...) val)]))
(define (record-set*/rt rcd names val)
  (match names
    [(list name) (hash-set rcd name val)]
    [(cons name names) (hash-set rcd name (record-set*/rt (hash-ref rcd name) names val))]))
(define record-merge hash-union)
(define-syntax-rule (record-has-field? rcd name) (hash-has-key? rcd 'name))

(module+ test
  (check-equal? (make-record [a 1] [b 2] [c 3]) (hasheq 'a 1 'b 2 'c 3))
  (let ()
    (define x 2)
    (check-equal? (make-record x) (hasheq 'x 2)))
  (let ()
    (define rcd (make-record [(fact x) (if (zero? x) 1 (* x (fact (sub1 x))))]))
    (check-equal? ((record-get rcd fact) 4) 24))
  (let ()
    (define rcd (make-record [a (make-record [b (make-record [c 2])])]))
    (check-equal? (record-get* rcd a b c) 2))
  (let ()
    (define rcd (make-record [a 1] [b 2]))
    (check-equal? (record-set rcd a 3) (make-record [a 3] [b 2])))
  (let ()
    (define rcd (make-record [a (make-record [b (make-record [c 1])])]))
    (check-equal? (record-set* rcd a b c 2)
                  (make-record [a (make-record [b (make-record [c 2])])]))))

(define-match-expander record
  (syntax-parser
    [(_) #'(? record?)]
    [(_ pair0 pair ...)
     #'(and (record/field pair0) (record pair ...))]))

(define-match-expander record/field
  (syntax-parser
    [(_ name:id) #'(record/field [name name])]
    [(_ [name:id pat])
     #'(and (? record?)
            (? (lambda (rcd) (record-has-field? rcd name)))
            (app (lambda (rcd) (record-get rcd name)) pat))]))

(module+ test
  (check-equal? (match (make-record [a 1] [b (make-record [c 2])])
                  [(record a [b (record c)])
                   (list a c)])
                '(1 2)))
