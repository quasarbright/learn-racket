#lang racket

(module+ test
  (require (except-in rackunit check)))

(require (for-syntax syntax/parse)
         racket/syntax)

; a checker for proofs in system NK (see https://en.wikipedia.org/wiki/Sequent_calculus)
; this might actually be system LK or something, idk.

; This module is roughly laid out in the  order I developed it.
; So initially, we write proofs as raw data. But then we implement macros and use those.
; TODO once you're done, move this into a separate repo and organize it

; TODO syntax-spec frontend!
; TODO variadic rules for and/or and latex
; TODO what programs do these proofs correspond to?
; TODO make a branch and reformulate everything in terms of forall and => lol
; TODO pattern expanders for formulae?
; TODO proof shape validation or something for better errors
; TODO make it so the proof for a checked rule only runs once on generics,
; not every time you use it. Only good for some checked rules, might not be worth.
; TODO de-gensym when printing, but still avoid name conflicts
; TODO pass 'auto to curried rule and have it grab the first thing that fits
; TODO pattern matching and context membership assertion in define-rule.
; maybe even make a sophisticated macro for it like turnstile

; A Formula is one of
; symbol?                            variable
; (and Formula ...)                  conjunction
; (or Formula ...)                   disjunction
; (=> Formula Formula)               implication
; (forall symbol? Formula)           universal quantification
; (exists symbol? Formula)           existential quantification
; (symbol? symbol? ...)              operator from a theory
;

; A Context is a (listof Formula) representing formulae that are assumed to be true
; First one is most recent.

; Formula ... -> Context
(define (context . ps) ps)

(define (assert-in-context p ctx [who-sym #f])
  (unless (in-context? p ctx)
    (if who-sym
        (error who-sym "~a not found in context ~a" p ctx)
        (error "~a not found in context ~a" p ctx))))

; Formula Context -> boolean?
(define (in-context? p ctx)
  (member p ctx alpha-eqv?))

; (Formula -> Any) Context -> boolean?
(define (find-in-context proc ctx)
  (findf proc ctx))

; Context Formula ... -> Context
(define (extend-context ctx . ps)
  (union-contexts (flatten-and ps) ctx))

; Context ... -> Context
(define (union-contexts . ctxs)
  (apply append ctxs))

; A Judgement is written in math like
; ctx |- p
; which means that under the context ctx, formula p is true

; Context Formula -> Judgement
; for making judgements. can't use |- unfortunately
(define (/- ctx p) (list ctx p))

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

; A Rule is a (Context Formula -> (listof Judgement))
; The input judgement is the conclusion that is to be proven.
; It takes in the context and the formula as separate arguments for convenience.
; The output represents a list of sup-proofs that are necessary to prove the input judgement
; A rule is responsible for checking whether it can be applied
; For rules that need more information, curried functions are used.

(struct rule [proc name]
  #:property prop:object-name (lambda (rul) (rule-name rul))
  #:property prop:procedure (lambda (rul . args) (apply (rule-proc rul) args)))

(define-syntax define-rule
  (syntax-rules ()
    [(_ ((name . args) ctx p) body ...)
     (define (name . args)
       (rule (lambda (ctx p)
               body
               ...)
             'name))]
    [(_ (name ctx p) body ...)
     (define name
       (rule (lambda (ctx p)
               body
               ...)
             'name))]))

; Example
; ctx |- p1   ctx |- p2
; ---------------------
; ctx |- p1 and p2
(define-rule (AndR ctx p)
  (match p
    [`(and ,p1 ,p2)
     (list (/- ctx p1)
           (/- ctx p2))]
    [_ (error 'AndR "rule not applicable")]))
; This rule means to prove p1 and p2, you must supply a proof for p1 and a proof for p2

; p in ctx
; --------
; ctx |- p
(define-rule (I ctx p)
  (assert-in-context p ctx 'I)
  '())

; (forall x p-body) in ctx    ctx,p-body[t/x] |- p
; ------------------------------------------------
; ctx |- p
(define-rule ((ForallL p-forall t) ctx p)
  (match p-forall
    [`(forall ,x ,p-body)
     (assert-in-context p-forall ctx 'ForallL)
     (list (/- (extend-context ctx (subst p-body x t)) p))]
    [_ (error 'ForallL "rule not applicable")]))
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

A ProofTree is a (list Rule ProofTree ...) or Rule
which is equivalent to (cons RupleApplication (listof ProofTree))
Represents the use of a rule and proofs of its sub-judgements
In the Rule case, it's shorthand for (list rul)

An InferenceTree is a (list Judgement Rule (listof InferenceTree))
Representing the completed inference tree followed during a Proof
The Judgement is the thing that was proven
The symbol? is the rule name
The list of inference trees is the sub-proofs

|#
; Prove a,b |- (and a b)
(define proof1
  `((a b) ; ctx
    (and a b) ; p
    (,AndR ; prove (and a b)
     ,I ; prove a
     ,I))) ; prove b

; Context Formula ProofTree -> InferenceTree
; Check that the proof tree proves the formula to be true under the context
(define (check-proof ctx p tree)
  (match tree
    [(? rule? rul)
     ; using a rule by itself like I is the same as (list I)
     (check-proof ctx p (list rul))]
    [(cons rule subtrees)
     (match-define (list (list subcontexts subformulae) ...) (rule ctx p))
     (unless (= (length subtrees) (length subcontexts))
       (error 'check-proof "incorrect number of subproofs. Expected ~a, given ~a. Rule: ~a" (length subcontexts) (length subtrees) rule))
     (list (/- ctx p) rule
           (for/list ([ctx subcontexts]
                      [p subformulae]
                      [tree subtrees])
             (check-proof ctx p tree)))]))

(module+ test
  (check-not-exn (lambda () proof1)))

(define proof-misuse-I
  `((b)
    a
    ,I))

(module+ test
  (check-exn exn:fail?
             (lambda () (apply check-proof proof-misuse-I))))

(module+ test
  (check-not-exn
   (lambda ()
     ; proof1
     (check-proof
      '(a b) '(and a b)
      `(,AndR
       ,I
       ,I)))))

; ctx |- (or p r)   ctx, q |- s
; ----------------------------- =>L^
; ctx, p=>q |- r or s
; included for completeness. Annoying to use
(define-rule ((=>L^ impl) ctx p)
  (match* (impl p)
    [(`(=> ,p ,q) `(or ,r ,s))
     (assert-in-context impl ctx '=>L^)
     (list (/- ctx `(or ,p ,r))
           (/- (extend-context ctx q) s))]
    [(_ _) (error '=>L^ "rule not applicable. Did you forget an or?")]))

; ctx |- p    ctx, p, q |- r
; ----------------------- =>L
; ctx, p=>q |- r
; to use an implication, prove the antecedent, then use the consequent
(define-rule ((=>L impl) ctx r)
  (match impl
    [`(=> ,p ,q)
     (assert-in-context impl ctx '=>L)
     (list (/- ctx p)
           (/- (extend-context ctx p q) r))]
    [_ (error '=>L "rule not applicable")]))

; ctx |- q  ctx, q |- p
; --------------------- cut
; ctx |- p
(define-rule ((Cut q) ctx p)
  (list (/- ctx q)
        (/- (extend-context ctx q) p)))

; ctx |- p or p
; ------------- CR
; ctx |- p
(define-rule (CR ctx p)
  (list (/- ctx `(or ,p ,p))))

; ctx |- p
; ------------- OrR1
; ctx |- p or q
(define-rule (OrR1 ctx p)
  (match p
    [`(or ,p ,_)
     (list (/- ctx p))]
    [_ (error 'OrR1 "rule not applicable")]))

; ctx |- q
; ------------- OrR2
; ctx |- p or q
(define-rule (OrR2 ctx p)
  (match p
    [`(or ,_ ,q)
     (list (/- ctx q))]
    [_ (error 'OrR2 "rule not applicable")]))

; -------- Debug
; ctx |- p
; Used to view the context and formula to prove.
; Can be used for an interactive experience.
(define-rule (Debug ctx p)
  (displayln (format "~a |- ~a" ctx p))
  '())

; -------- TrustMe
; ctx |- p
; Used when you're lazy!
(define-rule (TrustMe ctx p)
  ; so you don't forget that you're using this
  (displayln "I trust you!")
  '())

(module+ test
  ; modus ponens
  (check-not-exn
   (lambda ()
     (check-proof
      '(a (=> a b))
      'b
      `(,CR
        (,(=>L^ '(=> a b))
         (,OrR1
          ,I)
         ,I))))))

; when you prove a theorem, you can make a rule of it

; ----------------- ModusPonens
; ctx, p, p->q |- q
(define-rule ((ModusPonens p) ctx q)
  (assert-in-context `(=> ,p ,q) ctx 'ModusPonens)
  (assert-in-context p ctx 'ModusPonens)
  '())

; ctx, p-body[y/x] |- p
; --------------------------- ExistsL
; ctx, (exists x p-body) |- p
(define-rule ((ExistsL p-exists y) ctx p)
  (match p-exists
    [`(exists ,x ,p-body)
     (when (or (occurs-free? y p) (occurs-free?/context y ctx))
       (error 'ExistsL "cannot instantiate existential with a variable that occurs free in lower sequents"))
     (list (/- (extend-context ctx (subst p-body x y)) p))]
    [_ (error 'ExistsL "rule not applicable")]))

; ctx |- p-body[y/x]
; ------------------------ ForallR
; ctx |- (forall x p-body)
(define-rule ((ForallR y) ctx p)
  (match p
    [`(forall ,x ,p-body)
     ; important to use p. x = y can be ok
     (when (or (occurs-free? y p) (occurs-free?/context y ctx))
       (error "cannot instantiate forall with a variable that occurs free in lower sequents"))
     (list (/- ctx (subst p-body x y)))]
    [_ (error 'ForallR "rule not applicable")]))

; Formula Formula Formula -> Formula
; p[replacement/target]
(define (subst p target replacement)
  (match p
    [(== target alpha-eqv?)
     replacement]
    [(? symbol?) p]
    [(list (and quantifier (or 'forall 'exists)) a body)
     (if (occurs-free? a target)
         p
         (list quantifier a (subst body target replacement)))]
    [(cons op ps)
     (cons op (for/list ([p ps]) (subst p target replacement)))]))

; Formula -> (listof symbol?)
(define (free-vars p)
  (match p
    [(? symbol?) (list p)]
    [(list (and quantifier (or 'forall 'exists)) a body)
     (set-subtract (free-vars body) (list a))]
    [(cons op ps)
     (apply append (map free-vars ps))]))

; symbol? Context -> boolean?
(define (occurs-free?/context x ctx)
  (for/or ([p ctx]) (occurs-free? x p)))

; symbol? Formula -> boolean?
(define (occurs-free? x p)
  (match p
    [(? symbol?)
     (eq? x p)]
    [(list (or 'forall 'exists) a p)
     (and (not (eq? x a)) (occurs-free? x p))]
    [(cons op ps)
     (for/or ([p ps]) (occurs-free? x p))]))

; symbol? Formula -> boolean?
(define (occurs-bound? x p)
  (match p
    [(? symbol?) #f]
    [(list (or 'forall 'exists) a p)
     (or (eq? x a) (occurs-free? x p))]
    [(cons op ps)
     (for/or ([p ps]) (occurs-bound? x p))]))

; Formula Formula {(hash-of symbol? symbol?) (hash-of symbol? symbol?)} -> boolean?
; Does there exist a renaming of bound variables that makes
; the two formulae equal?
; The two hashes map bound vars to gensyms.
(define (alpha-eqv? p q [pvars (hasheq)] [qvars (hasheq)])
  (match* (p q)
    [((? symbol?) (? symbol?))
     (eq? (hash-ref pvars p p)
          (hash-ref qvars q q))]
    [((list quantifier a p) (list quantifier b q))
     #:when (member quantifier '(forall exists))
     (define v (gensym))
     (alpha-eqv? p q (hash-set pvars a v) (hash-set qvars b v))]
    [((cons op ps) (cons op qs))
     #:when (eq? (length ps) (length qs))
     (for/and ([p ps] [q qs])
       (alpha-eqv? p q pvars qvars))]
    [(_ _) #f]))

(module+ test
  (check-true (alpha-eqv? 'a 'a))
  (check-false (alpha-eqv? 'a 'b))
  (check-true (alpha-eqv? (forall a a) (forall b b)))
  (check-true (alpha-eqv? (exists a a) (exists b b)))
  (check-false (alpha-eqv? (forall a a) (exists b b)))
  (check-true (alpha-eqv? (forall (a b) (=> a b))
                          (forall (b c) (=> b c))))
  (check-false (alpha-eqv? (forall (a b) (=> a b))
                           (forall (b c) (disj b c))))
  (check-false (alpha-eqv? (forall (a b) (=> a b))
                           (forall (b b) (=> b b))))
  (check-false (alpha-eqv? (forall (b b) (=> b b))
                           (forall (a b) (=> a b))))
  (check-false (alpha-eqv? (forall (a b) (=> a b))
                           (forall (a b) (=> b a)))))

; rename bound variables in a repeatable way,
; such that alpha-equivalent formulae become equal?
(define (alpha-normalize p [count 0] [vars (hasheq)])
  (match p
    [(? symbol?)
     (hash-ref vars p p)]
    [(list quantifier a p)
     #:when (member quantifier '(forall exists))
     (define v (format-symbol "_.~a" count))
     (list quantifier v (alpha-normalize p (add1 count) (hash-set vars a v)))]
    [(cons op ps)
     (cons op (for/list ([p ps]) (alpha-normalize p count vars)))]))

(module+ test
  (check-equal? (alpha-normalize 'a) 'a)
  (check-equal? (alpha-normalize (forall a a))
                '(forall _.0 _.0))
  (check-equal? (alpha-normalize '(forall b (forall b (=> b b))))
                '(forall _.0 (forall _.1 (=> _.1 _.1)))))

(define proof-with-cuts
  `(()
    b
    (,(Cut 'a)
     ,TrustMe
     (,(Cut '(=> a b))
      ,TrustMe
      (,(ModusPonens 'a))))))
#;
(module+ test
  (check-not-exn
   (lambda ()
     (apply check-proof proof-with-cuts))))

; useful for sequencing suproofs. Ex:
; (Sequence Rule1 Rule2 ... proof)
; proof
; ---------- RuleN
; ...
; ---------- Rule2
; ctx2 |- p2
; ---------- Rule1
; ctx1 |- p1
; where the last argument is the final subproof
; TODO make this a procedure lol
(define-syntax Sequence
  (syntax-rules ()
    [(_ proof) proof]
    [(_ rule0 rule ...) (list rule0 (Sequence rule ...))]))

; useful for branching for multiple subproofs of one rule application
; (Branch Rule subproof ...)
; subproof ...
; ------------ Rule
; ctx |- p
(define Branch list)

; useful for sequencing cuts
(define-syntax Cuts
  (syntax-rules ()
    [(_ () proof)
     proof]
    [(_ ([lemma lemma-proof] pairs ...) proof)
     (Branch
      (Cut lemma)
      lemma-proof
      (Cuts (pairs ...) proof))]))

(define proof-with-Cuts
  `(()
    b
    ,(Cuts (['a TrustMe]
            ['(=> a b) TrustMe])
       `(,(ModusPonens 'a)))))
#;
(module+ test
  (check-not-exn
   (lambda ()
     (apply check-proof proof-with-Cuts))))

(module+ test
  ; modus ponens
  (check-not-exn
   (lambda ()
     (check-proof
      '(a (=> a b))
      'b
      (Sequence
       CR
       (Branch (=>L^ '(=> a b))
               (Sequence
                OrR1
                I)
               (Sequence I)))))))

; macros for formulae
(define-syntax-rule
  (fresh (x ...) body ...)
  (let ([x (mk-fresh-var 'x)] ...) body ...))
(define fresh-counter 0)
; {symbol?} -> symbol?
; generate a fresh variable name.
; different calls to this procedure will never be equal? to each other.
; can optionally pass in base name.
(define (mk-fresh-var [base-name '_])
  (set! fresh-counter (add1 fresh-counter))
  (mk-var base-name fresh-counter))
; symbol? natural? -> symbol?
(define (mk-var x n) (format-symbol "~a:~a" x n))

(define (disj p q) (list 'or p q))
(define (conj p q) (list 'and p q))
(define (=> p q) (list '=> p q))
(define-syntax forall
  (syntax-rules ()
    [(_ () p) p]
    [(_ (x0 x ...) p)
     (fresh (x0) (list 'forall x0 (forall (x ...) p)))]
    [(_ x p) (forall (x) p)]))
(define-syntax exists
  (syntax-rules ()
    [(_ () p) p]
    [(_ (x0 x ...) p)
     (fresh (x0) (list 'exists x0 (exists (x ...) p)))]
    [(_ x p) (exists (x) p)]))

(module+ test
  ; modus ponens
  (check-not-exn
   (lambda ()
     (fresh
      (a b)
      (check-proof
       (context a (=> a b)) b
       (Sequence
        CR
        (Branch (=>L^ (=> a b))
                (Sequence
                 OrR1
                 I)
                (Sequence I))))))))

; ctx,p |- q
; ------------- =>R
; ctx |- p => q
(define-rule (=>R ctx p)
  (match p
    [`(=> ,p ,q)
     (list (/- (extend-context ctx p) q))]))

; ctx,a,b |- p
; ------------- AndL
; ctx, a^b |- p
; unfolds all ands automatically
(define-rule (AndL ctx p)
  (define ctx^ (foldr (lambda (p ctx)
                        (match p
                          [`(and . ,ps)
                           (union-contexts (apply context (flatten-and ps))
                                           ctx)]
                          [_ (extend-context ctx p)]))
                      '()
                      ctx))
  (list (/- ctx^ p)))

; (listof Formula) -> (listof Formula)
; takes the arguments of an and formula
; and flattens out nested ands
(define (flatten-and ps)
  (foldr (lambda (p flattened)
           (match p
             [`(and . ,ps)
              (append (flatten-and ps) flattened)]
             [p (cons p flattened)]))
         '()
         ps))
(module+ test
  (check-equal? (flatten-and '(a1 (and a2 a3) (and (and (and a4 a5) a6))))
                '(a1 a2 a3 a4 a5 a6)))

(module+ test
  ; modus ponens theorem
  (check-not-exn
   (lambda ()
     (check-proof
      '() (forall p (forall q (=> (conj p (=> p q)) q)))
      (fresh
       (p q)
       (Sequence
        (ForallR p)
        (ForallR q)
        =>R
        AndL
        CR
        (Branch
         (=>L^ (=> p q))
         (Sequence
          OrR1
          I)
         I))))))
  ; absurd
  (check-not-exn
   (lambda ()
     (fresh
      (a)
      (check-proof
       (context (forall x x)) a
       (Sequence
        (ForallL (forall x x) a)
        I))))))

; use to instantiate nested conclusion foralls
(define-syntax ForallR*
  (syntax-rules ()
    [(_ () proof) proof]
    [(_ (x0 x ...) proof)
     (fresh
      (x0)
      (Sequence
       (ForallR x0)
       (ForallR* (x ...) proof)))]))

(define-syntax ExistsL*
  (syntax-rules ()
    [(_ () proof) proof]
    [(_ ([p-exists x] pair ...) proof)
     (fresh
      (x)
      (Sequence
       (ExistsL p-exists x)
       (ExistsL* (pair ...) proof)))]))

; ctx |- p[t/x]
; ------------------- ExistsR
; ctx |- (exists x p)
; if you can prove that a t satisfies p,
; t is something that exists that satisfied p!
(define-rule ((ExistsR t) ctx p)
  (match p
    [`(exists ,x ,p)
     (list (/- ctx (subst p x t)))]
    [_ (error 'ExistsR "rule not applicable")]))

(module+ test
  ; modus ponens theorem
  (check-not-exn
   (lambda ()
     (check-proof
      '() (forall (p q) (=> (conj p (=> p q)) q))
      (ForallR*
       (p q)
       (Sequence
        =>R
        AndL
        CR
        (Branch
         (=>L^ (=> p q))
         (Sequence
          OrR1
          I)
         I))))))
  ; (p => q) => ((exists x p) => (exists y q))
  (check-not-exn
   (lambda ()
     (check-proof
      (context (exists (x y) (conj x y))) (exists z z)
      (ExistsL*
       ([(exists (x y) (conj x y)) w]
        ; notice how you have access to w here
        [(exists y (conj w y)) w])
       (Sequence
        AndL
        (ExistsR w)
        I))))))

; equality

; shadows number =, but whatever
(define (= t1 t2) (list '= t1 t2))

; ctx |- p[t2/t1]
; --------------- =L
; ctx,t1=t2 |- p
; handles symmetry automatically
(define-rule ((=L target replacement) ctx p)
  (unless (or (in-context? (= target replacement) ctx)
              (in-context? (= replacement target) ctx))
    (error '=L "couldn't find equality in context"))
  (list (/- ctx (subst p target replacement))))

; ------------ =R
; ctx |- t = t
(define-rule (=R ctx p)
  (match p
    [`(= ,p ,q)
     (unless (alpha-eqv? p q)
       (error '=R "terms are not equal: ~a vs ~a" p q))
     '()]
    [_ (error '=R "rule not applicable")]))

(module+ test
  ; transitive property of equality
  (check-not-exn
   (lambda ()
     (check-proof
      '() (forall (a b c) (=> (conj (= a b) (= b c))
                              (= a c)))
      (ForallR*
       (a b c)
       (Sequence
        =>R
        AndL
        (=L a b)
        (=L b c)
        =R))))))

; formula macros

; bidirectional implication
(define (<=> p q) (conj (=> p q) (=> q p)))
; unique existence
(define (exists! x p)
  ; it's guaranteed that y is not free in p because exists uses fresh
  (exists x (forall y (<=> (subst p x y) (= x y)))))
; can be used to prove anything, impossible to prove (without itself or equivalent)
(define bottom (forall a a))
; logical negation
(define (neg p) (=> p bottom))
; useless as an assumption (except to prove itself kind of), can always be proven
(define top (exists a a))

(module+ test
  ; absurd
  (check-not-exn
   (lambda ()
     (check-proof
      '() (forall p (=> bottom p))
      (ForallR*
       (p)
       (Sequence
        =>R
        (ForallL bottom p)
        I)))))
  ; dual of absurd, idk what you'd call it
  (check-not-exn
   (lambda ()
     (check-proof
      '() (forall p (=> p top))
      (ForallR*
       (p)
       (Sequence
        =>R
        (ExistsR p)
        I))))))

; --------------- BottomL
; ctx,bottom |- p
(define-rule (BottomL ctx p)
  (assert-in-context bottom ctx 'BottomL)
  '())

; ---------- TopR
; ctx |- top
; ctx must not be empty
(define-rule (TopR ctx p)
  (unless (alpha-eqv? p top)
    (error 'TopR "rule not applicable"))
  ; do you really need this?
  (when (null? ctx)
    (error 'TopR "contex is empty"))
  '())

; ctx |- p and (not p)
; -------------------- BottomR
; ctx |- bottom
; contradiction
#;
(define-rule (BottomR))

; ctx p |- bottom
; --------------- NotR
; ctx |- (not p)
(define-rule (NotR ctx p) (=>R ctx p))

(module+ test
  ; proof by contradiction
  (check-not-exn
   (lambda ()
     (check-proof
      ; there does not exists something that is not equal to itself
      '() (neg (exists x (neg (= x x))))
      (Sequence
       =>R
       ; assume there does exist such a thing
       (ExistsL*
        ([(exists x (neg (= x x))) x])
        (Branch
         (=>L (neg (= x x)))
         =R
         BottomL))))))
  ; dual of proof by contradiction just for fun
  (check-not-exn
   (lambda ()
     (check-proof
      ; there does not exists something that is not equal to itself
      '() (forall x (= x x))
      (ForallR*
       (x)
       =R))))
  ; proof by contradiction with NotR
  ; Pretty much the same thing with two nots!
  (check-not-exn
   (lambda ()
     (check-proof
      ; there does not exists something that is not equal to itself
      '() (neg (exists x (neg (= x x))))
      (Sequence
       NotR
       (ExistsL*
        ([(exists x (neg (= x x))) x])
        (Sequence
         (NotL (= x x))
         =R))))))
  ; contradiction theorem
  (check-not-exn
   (lambda ()
     (check-proof
      '() (forall (p q) (=> (conj p (neg p))
                            q))
      (ForallR*
       (p q)
       (Sequence
        =>R
        AndL
        (Branch
         (=>L (neg p))
         I
         BottomL)))))))

; ctx, (not p) |- p
; ----------------- NotL
; ctx, (not p) |- q
; proof by contradiction
(define-rule ((NotL p) ctx q)
  (assert-in-context (neg p) ctx 'NotL)
  (list (/- ctx p)))

; checked rules

; For a "shortcut" rule like ModusPonens which isn't technically needed,
; it's safe to add a rule for it if you accompany the rule with an equivalent proof.
; Checked rules allow you to construct a rule like ModusPonens USING a proof.
; This way, rules are either intro/elim for new constructs and thus axiomatic,
; or verified shortcuts for proofs in terms of other rules.

; Fake rule used in checked rules to defer subproofs to the user of the checked rule.
; Don't use this in regular proofs
(define currently-deferring? (make-parameter #f))
(define-rule (Defer ctx p)
  (unless (currently-deferring?)
    (error 'Defer "do not use this during a normal proof"))
  '())

; Context Formula ProofTree -> (listof Judgement)
; like check-proof, but accumulates deferred subproofs
; Useful for defining checked rules.
; TODO what is the equivalent to this across the curry howard isomorphism?
(define (check-proof/defer ctx p tree)
  (define inference-tree (parameterize ([currently-deferring? #t])
                           (check-proof ctx p tree)))
  (get-deferred-judgements inference-tree))

; InferenceTree
(define (get-deferred-judgements tree)
  (match tree
    [(list j (== Defer eq?) '())
     (list j)]
    [(list _ _ subtrees)
     (apply append (map get-deferred-judgements subtrees))]))

; --------------- CheckedModusPonens
; ctx,p,p=>q |- q
(define-rule ((CheckedModusPonens p) ctx q)
  (assert-in-context `(=> ,p ,q) ctx 'CheckedModusPonens)
  (assert-in-context p ctx 'CheckedModusPonens)
  (check-proof/defer
   ctx q
   (Branch
    (=>L (=> p q))
    I
    I)))

(module+ test
  (fresh (p q)
         (check-equal? ((CheckedModusPonens p) (context p (=> p q)) q)
                       '())))

; TODO checked cut?

; ctx |- p    ctx, q |- r
; ----------------------- =>L
; ctx, p=>q |- r
(define-rule ((Checked=>L impl) ctx r)
  (match impl
    [`(=> ,p ,q)
     (assert-in-context impl ctx 'Checked=>L)
     (check-proof/defer
      ctx r
      (Sequence
       CR
       (Branch
        (=>L^ (=> p q))
        (Sequence OrR1 Defer)
        Defer)))]
    [_ (error 'Checked=>L "rule not applicable")]))

(module+ test
  ; TODO test other rules in this way
  (fresh (p q r)
         (define ctx (context (=> p q)))
         (check-equal? ((Checked=>L (=> p q))
                        ctx r)
                       (list (/- ctx p)
                             (/- (extend-context ctx q) r))))
  ; modus ponens using checked =>L
  (check-not-exn
   (lambda ()
     (fresh
      (p q)
      (check-proof
       (context p (=> p q)) q
       (Branch
        (Checked=>L (=> p q))
        I
        I))))))

; terms

;zfc

; set membership
(define (in e s) (list 'in e s))

; axioms

; equality on sets is determined by membership
(define extensionality
  (forall (x y) (=> (forall z (<=> (in z x) (in z y)))
                    (= x y))))
; ctx |- (forall z (in z x) <=> (in z y))
; --------------------------------------- Extensionality
; ctx |- (= x y)
(define-rule (Extensionality ctx p)
  (match p
    [`(= ,x ,y)
     (list (/- ctx (forall z (<=> (in z x) (in z y)))))]
    [_ (error 'Extensionality "rule is not applicable")]))

; this breaks if you do (forall x (null-set? x))
#;
(define (null-set? e) (forall x (neg (in x e))))

(define zfc-axioms (context extensionality))

; peano

(define zero (fresh (zero) zero))
(define (succ n) (list 'succ n))
(define (nat? x) (list 'nat? x))

; axioms

(define zero-is-nat (nat? zero))
; ------------------ ZeroIsNat
; ctx |- (nat? zero)
(define-rule (ZeroIsNat ctx p)
  (match p
    [(== (nat? zero) alpha-eqv?) '()]
    [`(nat? ,n) (list (/- ctx (= n zero)))]
    [_ (error 'ZeroIsNat "rule is not applicable")]))

; equality axioms follow from existing ones

(define succ-is-nat (forall n (=> (nat? n) (nat? (succ n)))))
; ctx |- (nat? n)
; ---------------
; ctx |- (nat? (succ n))
(define-rule (SuccIsNat ctx p)
  (match p
    [`(nat? (succ ,n))
     (list (/- ctx (nat? n)))]
    [`(nat? ,n)
     ; assuming free vars are fresh
     (list (/- ctx (exists pn (conj (= (succ pn) n) (nat? n)))))]
    [_ (error 'SuccIsNat "rule is not applicable")]))

(define nat= (forall (n m) (=> (= (succ n) (succ m))
                               (= n m))))
; ctx |- (= (succ n) (succ m))
; ---------------------------- Nat=
; ctx |- (= n m)
(define-rule (Nat= ctx p)
  (match p
    [`(= ,n ,m)
     (list (/- ctx (= (succ n) (succ m))))]
    [_ (error 'Nat= "rule is not applicable")]))

(define zero-not-succ (forall n (neg (= (succ n) zero))))

; ctx |- p[zero/x]   ctx |- (forall x p => p[(succ x)/x])
; ------------------------------------------------------- NatInduction
; ctx |- (forall x p)
(define-rule (NatInduction ctx p)
  (match p
    [`(forall ,x ,p)
     (list (/- ctx (subst p x zero))
           ; need to make sure we use the same x
           (/- ctx `(forall ,x ,(=> p (subst p x (succ x))))))]))

; TODO addition and multiplication as checked rules?

(define peano-axioms (context zero-is-nat succ-is-nat zero-not-succ))

; TODO transfinite ordinals??

; latex

; TODO check-proof/latex that checks it and returns a pict!

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
    ; TODO bottom, top, re-sugar neg?
    [(? symbol?)
     (match (regexp-match #px"^(.*):(\\d*)$" (symbol->string p))
       [(list _ name number)
        (format "~a_~a" name number)]
       [_ (symbol->string p)])]
    [`(not ,p) (format "(\\neg ~a)" (formula->latex p))]
    [`(and ,p ,q) (format "(~a \\wedge ~a)" (formula->latex p) (formula->latex q))]
    [`(or ,p ,q) (format "(~a \\vee ~a)" (formula->latex p) (formula->latex q))]
    [`(=> ,p ,q) (format "(~a \\rightarrow ~a)" (formula->latex p) (formula->latex q))]
    [`(forall ,x ,p) (format "(\\forall ~a . ~a)" (formula->latex x) (formula->latex p))]
    [`(exists ,x ,p) (format "(\\exists ~a . ~a)" (formula->latex x) (formula->latex p))]))
