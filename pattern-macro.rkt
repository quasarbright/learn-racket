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

(require syntax/parse syntax/stx syntax/id-set (for-syntax syntax/parse syntax/stx racket/match))

(define (rose/c leaf/c) (λ (v) ((or/c leaf/c (listof (rose/c leaf/c))) v)))
(define (substition? v) ((listof (list identifier? substition-value?)) v))
(define substition-value? (rose/c syntax?))
; a substitution represents a mapping from names to syntax values, or lists of syntax values, or lists of those, etc.
; lists represent ellipsis-bound identifiers

(module+ test
    (define-check (check-datum-equal? a b) (check-equal? (syntax->datum a) (syntax->datum b))))

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

#;(-> (listof symbol?) syntax? syntax? (maybe substition?))
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
    ; ... is special to racket, so I'm just using ooo to get around that
    [(pat (~datum ooo))
     ; simplified ellipsis pattern. equivalend to (pat ...), can't be used like (pat1 pat2 ... pat3)
     (let ([targets (syntax->list target)])
       ; target must be a list
       (and targets
            ; get the substition for matching pat on each sub-target
            (let ([subss (for/list ([target targets]) (match-pattern literals target #'pat))])
              (and (andmap identity subss)
                   ; if they all match, group the substitions
                   (group-subss subss)))))]
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

#;(-> (listof (listof (list identifier? any/c)))
      (listof (list identifier? (listof any/c))))
; take a list of substitions and compute a single substition which has each identifier bound to a list of
; its values in all substitions.
; assumes each substition has the same variables
(define (group-subss subss)
  (if (null? subss)
      '()
      (let* ([first-subs (first subss)]
             [vars (map first first-subs)])
        (for/list ([var vars])
          (list var (map (λ (subs) (lookup var subs)) subss))))))

#;(-> substition? syntax? (rose/c syntax?))
; apply the substitutions to the template
; depth=0 calls should produce a syntax. ellipsized, deep calls will produce a list
(define (substitute-template subs template)
  (syntax-parse template
    [var:id
     (let ([result (lookup #'var subs)])
       (if result
           (if (syntax? result)
               result
               (raise-syntax-error #f "missing ellipsis with pattern variable in template" #'var))
           #'var))]
    [(template (~datum ooo))
     (let ([subss (ungroup-subs subs #'template)])
       (datum->syntax #'template
                      (for/list ([subs subss])
                        (substitute-template subs #'template))))]
    [(template ...)
     #;(let ([templates (attribute template)])
       (for/fold ([ans '()]) ([template templates])
         (let ([result (substitute-template subs template)])
           )))
     (datum->syntax #'(template ...)
                    (stx-map (λ (template) (substitute-template subs template))
                             (attribute template)))]
    [datum #'datum]))

#|
template ((a b) ...)
a -> (#'1 #'2 #'3)
b -> (#'4 #'5 #'6)
(a b) -> ((1 2 3) (4 5 6)) the outer list is a stx list, the inner is a non-det list. hmmm
(a b) ... -> (#'(1 4) #'(2 5) #'(3 6))


/// left off here thinking
two possible designs:
* variable lookup (and template subst in general) always returns a single syntax. to make that happen, you have to split the substitution
for ... templates into a list of substitions, going from (var -> (listof thing)) (listof (var -> thing)). tricky part is that flatly bound ids need to stay
> (syntax-parse #'(1 2 3 4) [(b a ...) #'((b a) ...)])
#<syntax:string:1:39 ((1 2) (1 3) (1 4))>

* variable lookup (and template subst in general) returns a rose of syntax. variable lookup is ok with returning a rose
(not true in the other option, you must guard). The tricky part is what to do for regular list templates.
... templates would just "unlist" a single level.
but you can't just datum->syntax i think, because it might be a deep rose inside of deep ellipses.
or in that case, could you just go one level above the leaves and datum->syntax each parent?
unlist the bottom level value(s), not the top level value
you might need to differentiate between structural lists and non-determinism lists if that's not right. messy

example:
(syntax-rules () [(my-let* ([var (rhs ...)]) (body ...))])
(my-syntax-rules () [(my-let* ([var (... rhs)]) (... body))])
> ((my-syntax-rules () [(... (... (a b))) (... ((... a) (... b)))]) #'(((1 2) (3 4)) ((5 6) (7 8) (9 0))))
#'(((1 3) (2 4)) (5 7 9) (6 8 0))
|#


#;(-> substition? syntax? (list-of substition?))
; does the opposite of group-subss, but only looks at ellipsized identifiers in the template
; produces a list of substitions, one for each element of the list of substition values bound to
; an ellipsized identifier
; flattens a substition binding a variables to lists, to a list of substitutions
(define (ungroup-subs subs template)
  (define pattern-vars (template-pattern-vars subs template))
  ; pattern-vars are from the subs. lookup expects vars from the template, but it should be fine
  (define pattern-vals (for/list ([var pattern-vars]) (lookup var subs)))
  (define list-pattern-vals (filter list? pattern-vals))
  (define lengths (map length list-pattern-vals))
  (when (null? lengths) (raise-syntax-error #f "too many ellipses in template" template))
  (unless (apply = lengths) (raise-syntax-error #f "incompatible ellipsis match counts for template" template))
  ; ([a (1 2 3)] [b (4 5 6)])
  (define list-subs (for/list ([var pattern-vars] #:when (list? (lookup var subs)))
                     (list var (lookup var subs))))
  ; ((1 2 3) (4 5 6))
  (define list-valss (map second list-subs))
  ; (a b)
  (define list-vars (map first list-subs))
  ; ((1 4) (2 5) (3 6))
  (define transposed-vals (apply map list list-valss))
  ; (([a 1] [b 4]) ([a 2] [b 5]) ([a 3] [b 6]))
  (define new-subss (map (λ (vals) (map list list-vars vals)) transposed-vals))
  ; just combines each new subs with the old subs, replacing old listy vars with new flattened ones
  (map (λ (new-subs) (combine-subss new-subs subs)) new-subss))

(module+ test
  ; (syntax-parse #'(b c d) [(a ...) #'(a ...)])
  ; ([a (b c d)]) -> (([a b]) ([a c]) ([a d]))
  (let ([ungrouped (ungroup-subs (list [list #'a (list #'b #'c #'d)]) #'a)])
    (check-equal? (length ungrouped) 3)
    (check-datum-equal? (lookup #'a (first ungrouped)) #'b)
    (check-datum-equal? (lookup #'a (second ungrouped)) #'c)
    (check-datum-equal? (lookup #'a (third ungrouped)) #'d))
  ; (syntax-parse #'((1 2 3) (4 5 6)) [((a ...) (b ...)) #'((a b) ...)])
  ; ([a (1 2 3)] [b (4 5 6)]) -> (([a 1] [b 4]) ([a 2] [b 5]) ([a 3] [b 6]))
  (let ([ungrouped (ungroup-subs (list [list #'a (list #'1 #'2 #'3)]
                                       [list #'b (list #'4 #'5 #'6)])
                                 #'(a b))])
    (check-equal? (length ungrouped) 3)
    (check-datum-equal? (lookup #'a (first ungrouped)) #'1)
    (check-datum-equal? (lookup #'b (first ungrouped)) #'4)
    (check-datum-equal? (lookup #'a (third ungrouped)) #'3)
    (check-datum-equal? (lookup #'b (third ungrouped)) #'6)))

#;(-> substition? syntax? (listof identifier?))
; get all the pattern-bound variables in the template according to the substition
; returns vars from the subst, not the template
(define (template-pattern-vars subs template)
  (define all-vars (sequence->list (template-vars template)))
  (define subs-vars (map first subs))
  (filter (λ (subs-var) (ormap (λ (template-var) (bound-identifier=? subs-var template-var))
                                   all-vars))
          subs-vars))

(module+ test
  (check-equal? (map syntax->datum (template-pattern-vars (list (list #'a #'b) (list #'c #'d))
                                        #'((a) e ((f)))))
                (list 'a)))

#;(-> syntax? free-id-set?)
(define (template-vars template)
  (syntax-parse template
    [var:id (free-id-set-add (immutable-free-id-set) #'var)]
    [(template (~datum ooo)) (template-vars #'template)]
    [() (immutable-free-id-set)]
    [(template ...+) (apply set-union (map template-vars (attribute template)))]
    [datum (immutable-free-id-set)]))

(module+ test
  (check-equal? (sequence-length (template-vars (quote-syntax (a b c ((d e) ooo)))))
                5))

#;(-> substitution? ... substition?)
; combines substitions, only keeping the first instance of each variable
(define (combine-subss . subss)
  (clean-subs (apply append subss)))

(module+ test
  (let ([combined (combine-subss (list (list #'a #'1)
                                       (list #'b #'2))
                                 (list (list #'c #'3)
                                       (list #'a (list #'1 #'4))
                                       (list #'b (list #'2 #'5))))])
    (check-equal? (length combined) 3)
    (check-datum-equal? (lookup #'a combined) #'1)
    (check-datum-equal? (lookup #'b combined) #'2)
    (check-datum-equal? (lookup #'c combined) #'3)))

#;(-> substition? substition?)
; clean up duplicate variable bindings in a substititon, keeping only the first
(define (clean-subs subs)
  ; it is ok to use equal? because we're expecting the same syntax value to be a key twice
  (let recur ([seen-so-far (immutable-bound-id-set)] [subs subs])
    (match subs
      ['() '()]
      [(cons (list var val) subs)
       (if (set-member? seen-so-far var)
           (recur seen-so-far subs)
           (cons (list var val) (recur (set-add seen-so-far var) subs)))])))

(module+ test
  (let* ([subs (list (list #'a #'foo) (list #'b #'bar) (list #'a #'baz) (list #'c #'quux))]
         [cleaned (clean-subs subs)])
    (check-equal? (length cleaned) 3)
    (check-datum-equal? (lookup #'a cleaned) #'foo)
    (check-datum-equal? (lookup #'b cleaned) #'bar)
    (check-datum-equal? (lookup #'c cleaned) #'quux)))

#;(-> substition? syntax? natural?)
; how many copies does the ellipsized template need?
; errors if there is a conflict of match counts or depth for variables
#;(define (num-template-copies subs template)
  (let* ([vars (get-referenced-ellipsis-vars subs template)]
         [ellipsized-sub (for/list ([var vars])
                (lookup var subs))])
    (if (null? vals)
        (raise-syntax-error #f "too many ellipses in template" #'template)
        (if (apply = (map length vals))
            (first lengths)
            (raise-syntax-error #f "incompatible ellipsis match counts for template")))))

#;(-> identifier? substition? syntax?)
; look up the variable in the substitution
(define (lookup v subs)
  (match subs
    ['() #f]
    [(cons (list u stx) subs)
     (if (bound-identifier=? v u)
         stx
         (lookup v subs))]))

(module+ test
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
  (check-datum-equal? ((my-syntax-rules (lit) [(a lit b) 1] [(c d e) 2]) #'(foo baz bar)) #'2)
  ; ellipsis pattern
  (check-datum-equal? ((my-syntax-rules () [(a ooo) (a ooo)]) #'(1 2 3)) #'(1 2 3))
  ; more complicated ellipsis pattern
  (check-datum-equal? ((my-syntax-rules () [((a ooo) (b ooo)) ((a b) ooo)]) #'((1 2 3) (4 5 6)))
                      #'((1 4) (2 5) (3 6)))
  ; depth 2 ellipses. just maps the previous example over a list
  (check-datum-equal? ((my-syntax-rules () [(((a ooo) (b ooo)) ooo)
                                            (((a b) ooo) ooo)])
                       #'(((1 2 3) (4 5 6))
                          ((7 8) (9 0))))
                      #'(((1 4) (2 5) (3 6))
                         ((7 9) (8 0)))))
