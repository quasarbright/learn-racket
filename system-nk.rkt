#lang racket

(module+ test
  (require (except-in rackunit check)))

(require (for-syntax syntax/parse))

; a checker for proofs in system NK (see https://en.wikipedia.org/wiki/Sequent_calculus)
; this might actually be system LK or something, idk.

; TODO variadic rules for and/or and latex
; TODO extend-context function that flattens (and)
; TODO bottom
; TODO what programs do these proofs correspond to?
; TODO make a branch and reformulate everything in terms of forall and => lol
; TODO pattern expanders for formulae?
; TODO compound terms for theories
; TODO syntax-spec frontend!
; TODO proof shape validation or something for better errors
; TODO a way to define "shortcut" rules like ModusPonens USING a proof. Like define the rule using other rules.
; Like how NotR is literally =>R. Maybe combinators? Or an alternative to check-proof that just outputs the judgements?

; A Formula is one of
; symbol?                            variable
; (and Formula ...)                  conjunction
; (or Formula ...)                   disjunction
; (=> Formula Formula)               implication
; (forall symbol? Formula)           universal quantification
; (exists symbol? Formula)           existential quantification
; (= symbol? symbol?)                equality
;
; for later:
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

; A Rule is a (Context Formula -> (listof Judgement))
; The input judgement is the conclusion that is to be proven.
; It takes in the context and the formula as separate arguments for convenience.
; The output represents a list of sup-proofs that are necessary to prove the input judgement
; A rule is responsible for checking whether it can be applied
; For rules that need more information, curried functions are used.
;
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
     (list (list ctx p1)
           (list ctx p2))]
    [_ (error 'AndR "rule not applicable")]))
; This rule means to prove p1 and p2, you must supply a proof for p1 and a proof for p2

; p in ctx
; --------
; ctx |- p
(define-rule (I ctx p)
  (unless (member p ctx)
    (error 'I "formula not in context ~a ~a" p ctx))
  '())

; (forall x p-body) in ctx    ctx,p-body[t/x] |- p
; ------------------------------------------------
; ctx |- p
(define-rule ((ForallL p-forall t) ctx p)
  (match p-forall
    [`(forall ,x ,p-body)
     (unless (member p-forall ctx)
       (error "provided forall is not in the context"))
     (list (list (cons (subst p-body x t) ctx) p))]
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
     (list (list ctx p) rule
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
     (unless (member impl ctx)
       (error "implication not in context"))
     (list (list ctx `(or ,p ,q))
           (list (cons q ctx) s))]
    [(_ _) (error '=>L^ "rule not applicable. Did you forget an or?")]))

; ctx |- (or p r)    ctx, q |- r
; ------------------------------ =>L
; ctx, p=>q |- r
(define-rule ((=>L impl) ctx r)
  (match impl
    [`(=> ,p ,q)
     (unless (member impl ctx)
       (error '=>L "implication not in context"))
     (list (list ctx `(or ,p ,r))
           (list (cons q ctx) r))]))

; ctx |- q  ctx, q |- p
; --------------------- cut
; ctx |- p
(define-rule ((Cut q) ctx p)
  (list (list ctx q)
        (list (cons q ctx) p)))

; ctx |- p or p
; ------------- CR
; ctx |- p
(define-rule (CR ctx p)
  (list (list ctx `(or ,p ,p))))

; ctx |- p
; ------------- OrR1
; ctx |- p or q
(define-rule (OrR1 ctx p)
  (match p
    [`(or ,p ,_)
     (list (list ctx p))]
    [_ (error 'OrR1 "rule not applicable")]))

; ctx |- q
; ------------- OrR2
; ctx |- p or q
(define-rule (OrR2 ctx p)
  (match p
    [`(or ,_ ,q)
     (list (list ctx q))]
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
  (unless (member `(=> ,p ,q) ctx)
    (error 'ModusPonens "rule not applicable, implication not in ctx"))
  (unless (member p ctx)
    (error 'ModusPonens "rule not applicable, antecedent not in ctx"))
  '())

; ctx, p-body[y/x] |- p
; --------------------------- ExistsL
; ctx, (exists x p-body) |- p
(define-rule ((ExistsL p-exists y) ctx p)
  (match p-exists
    [`(exists ,x ,p-body)
     (when (or (occurs-free? y p) (occurs-free?/context y ctx))
       (error 'ExistsL "cannot instantiate existential with a variable that occurs free in lower sequents"))
     (list (list (cons (subst p-body x y) ctx) p))]
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
     (list (list ctx (subst p-body x y)))]
    [_ (error 'ForallR "rule not applicable")]))

; Formula symbol? Formula -> Formula
; p[replacement/x]
(define (subst p x replacement)
  (match p
    [(? symbol?)
     (if (eq? p x) replacement p)]
    [(cons (and op (or 'or 'and '=> '=)) ps)
     (cons op (for/list ([p ps]) (subst p x replacement)))]
    [(list (and quantifier (or 'forall 'exists)) a body)
     (if (eq? x a) p (list quantifier a (subst body x replacement)))]))

; symbol? Context -> boolean?
(define (occurs-free?/context x ctx)
  (for/or ([p ctx]) (occurs-free? x p)))

; symbol? Formula -> boolean?
(define (occurs-free? x p)
  (match p
    [(? symbol?)
     (eq? x p)]
    [(cons (or 'or 'and '=> '=) ps)
     (for/or ([p ps]) (occurs-free? x p))]
    [(list (or 'forall 'exists) a p)
     (and (not (eq? x a)) (occurs-free? x p))]))

; symbol? Formula -> boolean?
(define (occurs-bound? x p)
  (match p
    [(? symbol?) #f]
    [(cons (or 'or 'and '=> '=) ps)
     (for/or ([p ps]) (occurs-bound? x p))]
    [(list (or 'forall 'exists) a p)
     (or (eq? x a) (occurs-free? x p))]))

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

; A meta-rule for sequencing cuts
(define-syntax Cuts
  (syntax-rules ()
    [(_ () proof)
     proof]
    [(_ ([lemma lemma-proof] pairs ...) proof)
     (list
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

; sequences suproofs. Ex:
; ...
; ---------- Rule2
; ctx2 |- p2
; ---------- Rule1
; ctx1 |- p1
;
; where the last argument is the final subproof
; TODO make this a procedure lol
(define-syntax Sequence
  (syntax-rules ()
    [(_ proof) proof]
    [(_ rule0 rule ...) (list rule0 (Sequence rule ...))]))

(define Branch list)

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
(define-syntax-rule (fresh (x ...) body ...) (let ([x (gensym 'x)] ...) body ...))
(define-syntax-rule (disj p q) (list 'or p q))
(define-syntax-rule (conj p q) (list 'and p q))
(define-syntax-rule (=> p q) (list '=> p q))
; don't really need fresh for binder, right?
; I think you'd still need free var checks if you do this idk.
(define-syntax forall
  (syntax-rules ()
    [(_ () p) p]
    [(_ (x0 x ...) p)
     (let ([x0 'x0]) (list 'forall x0 (forall (x ...) p)))]
    [(_ x p) (forall (x) p)]))
(define-syntax exists
  (syntax-rules ()
    [(_ () p) p]
    [(_ (x0 x ...) p)
     (let ([x0 'x0]) (list 'exists x0 (exists (x ...) p)))]
    [(_ x p) (exists (x) p)]))

(module+ test
  ; modus ponens
  (check-not-exn
   (lambda ()
     (fresh
      (a b)
      (check-proof
       (list a (=> a b)) b
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
     (list (list (cons p ctx) q))]))

; ctx,a,b |- p
; ------------- AndL
; ctx, a^b |- p
; unfolds all ands automatically
(define-rule (AndL ctx p)
  (define ctx^ (foldr (lambda (p ctx)
                        (match p
                          [`(and . ,ps)
                           (append (flatten-and ps) ctx)]
                          [_ (cons p ctx)]))
                      '()
                      ctx))
  (list (list ctx^ p)))

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
       (list (forall x x)) a
       (Sequence
        ; this only works bc forall doesn't use fresh
        ; I thought something might need to get bound here, but
        ; you're always going to instantiate with something already bound
        (ForallL (forall x x) a)
        I))))))

; for binding, you just might need fresh sometimes
; but ForallR and ExistsL will always need a fresh var

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
     (list (list ctx (subst p x t)))]
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
      (list (exists (x y) (and x y))) (exists z z)
      (ExistsL*
       ([(exists (x y) (and x y)) w]
        ; notice how you have access to w here
        [(exists y (and w y)) w])
       (Sequence
        AndL
        (ExistsR w)
        I))))))

; equality

; shadows number =, but whatever
(define-syntax-rule (= t1 t2) (list '= t1 t2))

; ctx |- p[t2/t1]
; --------------- =L
; ctx,t1=t2 |- p
; handles symmetry automatically
(define-rule ((=L target replacement) ctx p)
  (unless (or (member (= target replacement) ctx)
              (member (= target replacement) ctx))
    (error '=L "couldn't find equality in context"))
  ; TODO subst a term with a term once you have (= Formula Formula)
  (list (list ctx (subst p target replacement))))

; ------------ =R
; ctx |- t = t
; Refl
(define-rule (=R ctx p)
  (match p
    [`(= ,p ,q)
     (unless (equal? p q)
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
(define-syntax-rule (<=> p q) (conj (=> p q) (=> q p)))
; unique existence
(define-syntax-rule (exists! x p y)
  (begin
    ; this is only necessary because we perform substitution on p
    (when (occurs-free? y p)
      (error 'exists! "universally quantified variable must not be free in formula"))
    (exists x (forall y (<=> (subst p x y) (= x y))))))
; can be used to prove anything, impossible to prove (without itself or equivalent)
(define bottom (forall a a))
; logical negation
(define-syntax-rule (neg p) (=> p bottom))
; useless as an assumption (except to prove itself), can always be proven
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
  (unless (member bottom ctx)
    (error 'BottomL "bottom not in context"))
  '())

; ---------- TopR
; ctx |- top
; ctx must not be empty
(define-rule (TopR ctx p)
  (unless (equal? p top)
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
         (Sequence
          OrR1
          =R)
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
         (Sequence
          OrR1
          I)
         BottomL)))))))

; ctx, (not p) |- p
; ----------------- NotL
; ctx, (not p) |- q
; proof by contradiction
(define-rule ((NotL p) ctx q)
  (unless (member (neg p) ctx)
    (error 'NotL "negation not found in context"))
  (list (list ctx p)))

; latex

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
    [(? symbol?) (symbol->string p)]
    [`(not ,p) (format "(\\neg ~a)" (formula->latex p))]
    [`(and ,p ,q) (format "(~a \\wedge ~a)" (formula->latex p) (formula->latex q))]
    [`(or ,p ,q) (format "(~a \\vee ~a)" (formula->latex p) (formula->latex q))]
    [`(=> ,p ,q) (format "(~a \\rightarrow ~a)" (formula->latex p) (formula->latex q))]
    [`(forall ,x ,p) (format "(\\forall ~a . ~a)" (formula->latex x) (formula->latex p))]
    [`(exists ,x ,p) (format "(\\exists ~a . ~a)" (formula->latex x) (formula->latex p))]))
