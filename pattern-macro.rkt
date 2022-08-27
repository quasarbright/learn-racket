#lang racket

; an implementation of something like syntax-rules

#|
go through pattern with literals around.
for list, recur. for an identifier, if it is symbolically equal to a literal, assert datum equality.
otherwise, bind. for other datums, assert datum equality.
To actually get the output syntax, you can rely on datum->syntax and the bindings of pattern variables.

For templates:
if list, recur.
if variable: if bound by pattern, substitute. Else, keep old syntax.

Hygiene should be taken care of by define-syntax. This just needs to be a pure procedure from syntax to syntax
|#

(module+ test (require rackunit))
(provide (all-defined-out))

(require syntax/parse syntax/stx (for-syntax syntax/parse syntax/stx racket/match))

; like syntax-rules
(define-syntax my-syntax-rules
  (syntax-parser
    [(_ (literal:id ...) clause ...)
     #'(λ (stx) (apply-rules (list 'literal ...) stx #'(clause ...)))]))

#;(-> (list-of symbol?) syntax? syntax? syntax?)
; apply the syntax rules to transform target
(define (apply-rules literals target clauses)
  (syntax-parse clauses
    [([pattern template] clause ...)
     (try-clause literals target #'pattern #'template
                 (λ () (apply-rules literals target (attribute clause))))]
    [() (raise-syntax-error #f "bad syntax oh no" target)]))

#;(-> (listof symbol?) syntax? syntax? syntax? (-> syntax?) syntax?)
; try matching a clause. if it fails, use the fallback thunk on-fail
(define (try-clause literals target pattern template on-fail)
  (let ([subs (match-pattern literals target pattern)])
    (if subs
        (substitute-template subs template)
        (on-fail))))

#;(-> (listof symbol?) syntax? syntax? (maybe (listof (list identifier? syntax?))))
; get a list of substitutions to apply in the template, or return #f if the pattern fails
(define (match-pattern literals target pattern)
  (syntax-parse pattern
    [(~datum _) '()]
    [var:id
     #:when (member (syntax->datum #'var) literals)
     ; for (datum) literals, perform a symbolic equality check
     (and (equal? (syntax->datum target) (syntax->datum #'var)) '())]
    [var:id
     (list (list #'var target))]
    [(pat ...)
     (let ([pats (attribute pat)]
           [targets (syntax->list target)])
       (and targets
            (= (length pats) (length targets))
            (let ([subss (for/list ([pattern pats] [target targets])
                           (match-pattern literals target pattern))])
              (and (andmap identity subss)
                   (apply append subss)))))]
    [datum
     (and (equal? (syntax->datum target) (syntax->datum #'datum))
          '())]))

#;(-> (listof (list identifier? syntax?)) syntax? syntax?)
; apply the substitutions to the template
(define (substitute-template subs template)
  (syntax-parse template
    [var:id
     (let ([result (lookup #'var subs)])
       (or result #'var))]
    [(template ...)
     (datum->syntax #'(template ...)
                    (stx-map (λ (template) (substitute-template subs template))
                             (attribute template)))]
    [datum #'datum]))

#;(-> identifier? (listof (list identifier? syntax?)) syntax?)
; look up the variable in the substitution
(define (lookup v subs)
  (match subs
    ['() #f]
    [(cons (list u stx) subs)
     (if (bound-identifier=? v u)
         stx
         (lookup v subs))]))

(module+ test
  (define-check (check-datum-equal? a b) (check-equal? (syntax->datum a) (syntax->datum b)))
  ; basic usage
  (check-datum-equal? ((my-syntax-rules () [_ 1]) #'foo) #'1)
  ; identity function, use of var in template
  (check-datum-equal? ((my-syntax-rules () [a a]) #'foo) #'foo)
  ; use of list pattern and template
  (check-datum-equal? ((my-syntax-rules () [(a b) (b a)]) #'(foo bar)) #'(bar foo))
  ; clause failure is handled properly
  (check-datum-equal? ((my-syntax-rules () [(fail) foo] [a 2]) #'hi) #'2)
  ; matching a literal
  (check-datum-equal? ((my-syntax-rules (lit) [(a lit b) 1] [(c d e) 2]) #'(foo lit bar)) #'1)
  ; failing to match a literal
  (check-datum-equal? ((my-syntax-rules (lit) [(a lit b) 1] [(c d e) 2]) #'(foo baz bar)) #'2))
