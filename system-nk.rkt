#lang racket

(module+ test
  (require (except-in rackunit check)))

(require (for-syntax syntax/parse))

; a checker for proofs in system NK (see https://en.wikipedia.org/wiki/Sequent_calculus)
; this might actually be system LK or something, idk.

; TODO variadic rules for and/or and latex

; A Formula is one of
; symbol?                            variable
; (not Formula)                      negation
; (and Formula ...)                  conjunction
; (or Formula ...)                   disjunction
; (=> Formula Formula)               implication
; (forall symbol? Formula)           universal quantification
; (exists symbol? Formula)           existential quantification
;
; for later:
; (<=> Formula Formula)              bidirectional implication
; (exists! symbol? Formula)          unique existential quantification
; (= symbol? symbol?)                equality
; (symbol? symbol? ...)              operator from a theory

; A Context is a (listof Formula) representing formulae that are assumed to be true

; A Judgement is written in math like
; ctx |- p
; which means that under the context ctx, formula p is true

; A Rule is written in math like
; precondition ...
; ----------------
; judgement
; which means the judgement follows from the preconditions, where preconditions
; are judgements or abstract requirements like "x is not a free variable of p"
; Example:
; ctx, p1 |- p2
; --------------- =>R
; ctx |- p1 => p2
; This means p1 => p2 is true under ctx if it can be shown that p2 is true under ctx with the added assumption that p1 is true

; A Proof of a formula under a context is a tree of rule applications showing that it is true
; The tree's leaves are rules like
; p in ctx
; -------- I
; ctx |- p
; Which is the rule for using an assumption/axiom. The leaves are applications of rules which have no judgements on top

; Now to implement a checker for proofs in this system

; Use the data definitions for Formula and Context from above

; A Judgement is a (list Context Formula)
; Representing a formula that may be true under a context

; A Rule is a function that takes in
; * a Judgement
; optionally
; * some Formulae. Like forallL needs to know t
; and returns
; (listof Judgement)
; The input judgement is the conclusion that is to be proven.
; The extra formulae that a rule may expect are used to inform what the outputs must be.
; This is necessary because it is not always possible to infer output judgements from the input alone, like forallL
; The output represents a list of sup-proofs that are necessary to prove the input judgement
; A rule is responsible for checking whether it can be applied

; Example
; ctx |- p1   ctx |- p2
; ---------------------
; ctx |- p1 and p2
(define andR
  (lambda (j)
    (match j
      [(list ctx `(and ,p1 ,p2))
       (list (list ctx p1)
             (list ctx p2))]
      [_ (error "rule not applicable")])))
; This rule means to prove p1 and p2, you must supply a proof for p1 and a proof for p2

; p in ctx
; --------
; ctx |- p
(define I
  (lambda (j)
    (match j
      [(list ctx p)
       (unless (member p ctx)
         (error 'I "formula not in context ~a ~a" p ctx))
       '()])))

; (forall x p-body) in ctx    ctx,p-body[t/x] |- p
; ------------------------------------------------
; ctx |- p
#;
(define forallL
  (lambda (j p/forall t)
    (match* (j p/forall)
      [((list ctx p) (and p-forall `(forall ,x ,p-body)))
       (unless (member p-forall ctx)
         (error "provided forall is not in the context"))
       (list (cons (subst p-body x t) ctx) p)]
      [_ (error "rule not applicable")])))
; This rule means if you assume a forall, you can "instantiate" it with any term and assume its body
; This instantiation uses variable substitution
; The rule takes in p/forall so it knows which forall you're talking about, since this is
; not inferrable from p
; The rule takes in t so it knows what term you want to instantiate the formula with, since this is
; also not inferrable from p

; In general, a rule takes in the conclusion judgement and anything it needs to infer what the required
; sub-judgements are, makes sure the rule can be applied, and returns the required sub-judgements

; Proofs

#|
Using rules raw would be pretty verbose. You should be able to start with some context and then have it threaded
for you. The conclusion too.

A Proof is a
(list Context Formula ProofTree)

A RuleApplication is a (list RuleProcedure Formula ...)
Represents an application of a rule procedure with the conclusion judgement implicitly passed in
The Formula ... are the extra arguments

A ProofTree is a (list RuleApplication ProofTree ...)
which is equivalent to (cons RupleApplication (listof ProofTree))
Represents the use of a rule and proofs of its sub-judgements

An InferenceTree is a (list Judgement RuleProcedure (listof InferenceTree))
Representing the completed inference tree followed during a Proof
The Judgement is the thing that was proven
The symbol? is the rule name
The list of inference trees is the sub-proofs

|#
; Prove a,b |- (and a b)
(define proof1
  `((a b) ; ctx
    (and a b) ; p
    ((,andR) ; prove (and a b)
     ((,I)) ; prove a
     ((,I))))) ; prove b

; Proof -> InferenceTree
; Check the proof, error if it is not valid.
(define (check-proof proof)
  (match proof
    [(list ctx p tree)
     (check-proof-tree ctx p tree)]))

; Context Formula ProofTree -> InferenceTree
; Check that the proof tree proves the formula under the context, error if it doesn't
(define (check-proof-tree ctx p tree)
  (match tree
    [(cons (list rule args ...) subtrees)
     (match-define (list (list subcontexts subformulae) ...) (apply rule (list ctx p) args))
     (unless (= (length subtrees) (length subcontexts))
       (error "incorrect number of subproofs"))
     (list (list ctx p) rule
           (for/list ([ctx subcontexts]
                      [p subformulae]
                      [tree subtrees])
             (check-proof-tree ctx p tree)))]))

(module+ test
  (check-not-exn (lambda () proof1)))

(define proof-misuse-I
  `((b)
    a
    ((,I))))

(module+ test
  (check-exn exn:fail?
             (lambda () (check-proof proof-misuse-I))))

(define-syntax-rule
  (check ctx p tree)
  (check-proof
   `(ctx
     p
     ,(check/tree tree))))
(define-syntax-rule
  (check/tree ((rule arg ...) subtree ...))
  `((,rule arg ...) ,(check/tree subtree) ...))

(module+ test
  (check-not-exn
   (lambda ()
     ; proof1
     (check
      (a b) (and a b)
      ((andR)
       ((I))
       ((I)))))))

; ctx |- (or p r)   ctx, q |- s
; ----------------------------- =>L
; ctx, p=>q |- r or s
(define =>L
  (lambda (j impl)
    (match* (impl j)
      [(`(=> ,p ,q) (list ctx `(or ,r ,s)))
       (unless (member `(=> ,p ,q) ctx)
         (error "implication not in context"))
       (list (list ctx `(or ,p ,q))
             (list (cons q ctx) s))]
      [(_ _) (error "rule not applicable")])))

; ctx |- q  ctx, q |- p
; --------------------- cut
; ctx |- p
(define Cut
  (lambda (j q)
    (match j
      [(list ctx p)
       (list (list ctx q)
             (list (cons q ctx) p))])))

; ctx |- p or p
; ------------- CR
; ctx |- p
(define CR
  (lambda (j)
    (match j
      [(list ctx p)
       (list (list ctx `(or ,p ,p)))])))

; ctx |- p
; ------------- OrR1
; ctx |- p or q
(define OrR1
  (lambda (j)
    (match j
      [(list ctx `(or ,p ,_))
       (list (list ctx p))]
      [_ (error "rule not applicable")])))

; ctx |- q
; ------------- OrR2
; ctx |- p or q
(define OrR2
  (lambda (j)
    (match j
      [(list ctx `(or ,_ ,q))
       (list (list ctx q))]
      [_ (error "rule not applicable")])))

; -------- Debug
; ctx |- p
; Used to view the context and formula to prove.
; Can be used for an interactive experience.
(define Debug
  (lambda (j [name #f])
    (match j
      [(list ctx p)
       (when name (displayln (format "Debug ~a" name)))
       (displayln (format "~a |- ~a" ctx p))
       '()])))

; -------- TrustMe
; ctx |- p
; Used when you're lazy!
(define TrustMe
  (lambda (j)
    (match j
      [(list ctx p)
       ; so you don't forget that you're using this
       (displayln "I trust you!")
       '()])))

(module+ test
  ; modus ponens
  (check-not-exn
   (lambda ()
     (check
      (a (=> a b)) b
      ((CR)
       ((=>L (=> a b))
        ((OrR1)
         ((I)))
        ((I))))))))

; InferenceTree -> string?
(define (inference-tree->latex it)
  (match it
    [(list (list ctx p) rule its)
     (format "\\frac{\\displaystyle ~a}{\\displaystyle ~a \\ \\vdash \\ ~a} ~a"
             (inference-trees->latex its)
             (context->latex ctx)
             (formula->latex p)
             (object-name rule))]))

; string? (listof string?) -> string?
(define (string-join sep strs)
  (match strs
    ['() ""]
    [(cons str (? cons? strs))
     (format "~a~a~a"
             str
             sep
             (string-join sep strs))]
    [(list str) str]))

; (listof InferenceTree) -> string?
(define (inference-trees->latex its)
  (string-join " \\qquad " (map inference-tree->latex its)))

; Context -> string?
(define (context->latex ctx)
  (string-join " , " (map formula->latex ctx)))

; Formula -> string?
(define (formula->latex p)
  (match p
    [(? symbol?) (symbol->string p)]
    [`(not ,p) (format "(\\neg ~a)" (formula->latex p))]
    [`(and ,p ,q) (format "(~a \\wedge ~a)" (formula->latex p) (formula->latex q))]
    [`(or ,p ,q) (format "(~a \\vee ~a)" (formula->latex p) (formula->latex q))]
    [`(=> ,p ,q) (format "(~a \\rightarrow ~a)" (formula->latex p) (formula->latex q))]
    [`(forall ,x ,p) (format "(\\forall ~a . ~a)" (formula->latex x) (formula->latex p))]
    [`(exists ,x ,p) (format "(\\exists ~a . ~a)" (formula->latex x) (formula->latex p))]))

#;
(displayln
  (inference-tree->latex
  (check
   (a (=> a b)) b
   ((CR)
    ((=>L (=> a b))
     ((OrR1)
      ((I)))
     ((I)))))))
