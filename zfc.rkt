#lang racket

; Goal is a proof checker for statements in ZFC. Will likely generalize to a general proof checker
; parameterized by a collection of axioms.
; Some concrete goals:
; * Can check the proof that the empty set exists.
; * Can check the proof that a singleton set can be constructed from a given set.
; * Can check some peano stuff or something, gotta think it out when I get there.

; A Proposition is one of
; #t                                 true
; #f                                 false
; symbol?                            variable
; (not Proposition)                  negation
; (and Proposition ...)              conjunction
; (or Proposition ...)               disjunction
; (=> Proposition Proposition)       implication
; (<=> Proposition Proposition)      bidirectional implication
; (forall symbol? Proposition)       universal quantification
; (exists symbol? Proposition)       existential quantification
; (exists! symbol? Proposition)      unique existential quantification
; (= symbol? symbol?)                equality
; (symbol? symbol? ...)              operator from a theory

; If you have a macro system or something, you can express some of these in terms of others.
; Namely, logical connectives have some inter-expressivity. And exists! can be defined in terms
; of forall and exists

#|
You have axioms, which are propositions assumed to be true.
You have rules like alpha renaming and equality substitution, which are kind of like axiom schemas
A proof uses axioms and rules to demonstrate that a proposition is true under the assumptions

Some desired properties of the system:
* Can use theorems in future proofs.
* Easy to know and configure what axioms are available.
* Proofs are top-down. Break up the big proposition into smaller propositions.
* Theories should not need rules, only axioms. Rules should be for the underlying logic and proofs.
* You can prove things in whatever order you want.
* You don't have to write down an axiom's whole proposition when you use it.
* Supports axiom schemas.
* Easy to add axioms and rules. Ideally, user-extensible.
* Not too much renaming, name collisions aren't an issue, etc.
* Macros. Maybe use syntax-spec and make this a hosted DSL. Careful with name sensitivity and hygiene.
* Proofs are flat. Don't want deep proof trees with many branches.
|#

#|
possible sketch of a proof:
Theorem: (forall a (forall b (=> (and a (= a b))
                                 b)))
Proof:
intro a
intro b
assume (and a (= a b))
a ; given
(= a b) ; given
b ; subst(a,b)
|#

#|
Idea: Judgements

You have rules like

ctx |- p    x not in ctx
------------------------ all
ctx |- (forall x p)

and ones with parameters like

ctx |- (= a b)    ctx |- (= b c)
-------------------------------- (eq-trans b)
ctx |- (= a c)

To prove something, you reduce it to simpler proofs, and you eventually
get to something like

-------------- refl
ctx |- (= a a)

p in ctx
-------- given
ctx |- p

with no sub-proofs.

Problems:
* Leads to tree structure?
* How to use an axiom?
* Need to specify the bottom proposition somehow
* Need to provide information like b for (eq-trans b) somehow

Flat:
You have givens and goals, and you apply rules to split goals.
But then proving implications leads to a tree structure.
If you only need to branch for local context manipulations, that's not a big deal.
Sketch:
ctx = (list (= a b) (= b c) (= c d))
goals = (list (= a d))
(eq-trans (= a d) b)

ctx = (list (= a b) (= b c) (= c d))
goals = (list (= a b) (= b d))
(given (= a b))

ctx = (list (= a b) (= b c) (= c d))
goals = (list (= b d))
(eq-trans (= b d) c)

ctx = (list (= a b) (= b c) (= c d))
goals = (list (= b c) (= c d))
(given (= b c))

ctx = (list (= a b) (= b c) (= c d))
goals = (list (= c d))
(given (= c d))

ctx = (list (= a b) (= b c) (= c d))
goals = (list)
done


Another sketch:
ctx = (list (= a b) (= x y))
goals = (list (= b a) (=> (= b c) (= c b)) (= y x))
(eq-sym (= b a))

ctx = (list (= a b) (= x y))
goals = (list (= a b) (=> (= b c) (= c b)) (= y x))
(given (= a b))

ctx = (list (= a b) (= x y))
goals = (list (=> (= b c) (= c b)) (= y x))
(implication (=> (= b c) (= c b))
  ctx = (list (= a b) (= x y) (= b c))
  goals = (list (= c b)) ; note just the single goal
  (eq-sym (= c b))
  (given (= b c))
  done)

ctx = (list (= a b) (= x y))
goals = (list (= y x))
(eq-sym (= y x))
(given)
done

Notes:
* Can add stuff like (givens) which eliminates goals in the context
* A rule is usually a function (propositions, ctx, goals -> goals), but ctx modifications are tricky
  * For those, (propositions, ctx, goals -> (listof (ctx, goals)), goals) where return is isolated sub-proofs and then final goals
  * Think more about how to represent that nicely
* May be able to infer bottom expr. But then rules will need to have matchers to know what they can be applied to.
  * supply auto instead of expr or something

Pros:
* Pretty flat. Only branches on context modifications.
* Seems like it'd be easy to have user rules. See notes.
* Lends itself nicely to interactivity since there is a state and it's pretty flat.

Cons:
* Have to specify bottom thing unless you can do structural inference nicely
* Very name sensitive




Tree:
Treat rules as tree-like functions
Some sketches:

ctx = ((= a b) (= b c) (= c d))
theorem = (= a d)
(eq-trans (= a d)
  (eq-trans (= a c)
    (given (= a b))
    (given (= b c)))
  (given (= c d)))

ctx = (list (= a b) (= x y))
theorem = [(= b a) (=> (= b c) (= c b)) (= y x)]
(and (eq-sym (= b a) (given (= a b)))
     (implies (= b c)
       (eq-sym (= c b) (given (= b c))))
     (eq-sym (= y x) (given (= x y))))

Notes:
* A rule is a function (context, expressions, proven-propositions -> proven-proposition)
* You can have inference if rules can communicate expected proven propositions to sub-proofs
  * That'd also help for interactivity.
  * Rules could take in a current goal proposition to inform inference
* Although it will usually be the case, rules don't have to take in the bottom prop as the first argument.
* Rules can run sub-proofs under modified contexts
* Should rules drive control? Or should rule application be bottom up?
  * If only a rule's implementer knows what's an expr and what's a subproof, rules must drive control
* Interactivity though (debug) rule which shows evaluation state, including context and goal if available

Pros:
* Rules are simple to write
* Uniform mechanism, always tree-like
* User rules should be easy
* Compositional
* May lend itself to inference, see note
* Rules can be very general and powerful
* Inference
* Rule model is more robust than flat

Cons:
* High breadth and depth
* No equivalent to (givens) since there usually one goal at a time. Not a big deal.
* Very name sensitive
* Pretty verbose, unless rules are smart ig.
* Worse interactivity ux than flat design? Overall depends on what user gains from better rules

General notes:
* Theorems
  * A theorem is a (context, proposition). You can use a theorem if its context is a subset of the current one in some sense.
  * Maybe just (axioms, proposition).
  * The rule can be (theorem name) and theorems will have to be in the context or some global environment
  * An axiom/locally true prop is a special case of a theorem with no assumptions needed.
* Axiom schemas
  * Treat axioms specially and can do (axiom replacement (lambda (x) ...)) or something.
  * Axiom is a (expr ... -> prop)? And simple axioms are 0-ary functions.
* If you treat axioms specially, you can have a global axiom store and infer which ones are needed in a proof.
  * User can configure whether to do this or just supply an axiom set and disallow inferred axioms.
  * Separate forms for (axiom ...), (assumed ...), (theorem ...), and stuff like (axiom) and (theorem) add to the needed axioms
  * Have a rule that searches axioms, assumeds, and theorems like givens?
* Automation
  * Automation will have to know what rules are available. Global rule store?
  * If you know what needs to be proven and what props a rule can apply to, you can get reasonable automation.
* Theorem schema?
* Use forall for axiom schemas, but quantify over functions? Then you'd need a type system.
* Construction stuff like (singleton x)
  * Usage: (forall x (in x (singleton x)))
           (forall x (forall sx (=> (is-singleton x sx)               (in x sx))))
           (forall x (forall sx (=> (forall y (=> (in y sz) (= x y))) (in x sx))))
  * macro (let ([a (constructor x y z ...)]) prop) ~> (forall a (=> (predicate a x y z ...) prop))
    * where each constructor has a corresponding predicate and constructors can only be used inside of let.
  * Reminds me of logic programming
  * Would be nice if it was easier to talk about constructed objects more directly. Need data types for something like that though.
  * Actually, if you use operators as constructors too, rules can take care of it!
  * Would have to relax equality beyond variables and make sure rules respect it.
  * Should also relax operator grammar? Think about implications, might be fine. Rules could become pretty complex though.
  * Define a singleton operator, and add
    (is-singleton x sx) ~> (forall y (<=> (in y sx) (= x y)))
    (forall x (is-singleton x (singleton x))) ; defining the meaning of the term
    Since this is a shorthand for a unique object with a property, prove unique existence:
    (forall x (and (exists! sx (is-singleton x sx))
                   (forall sx (=> (is-singleton x sx) (= sx (singleton x))))))
    => (forall x (is-singleton x (singleton x)))
    Rely on set equality axiom and defining property for equality to make sense
  * For something like peano from scratch, define (zero), (succ n), (nat? n), and then literally write the axioms
    * You can rely on refl and subst for structural equality
  * For something like peano addition, define (+ a b) and then
    * Define like (forall a (= (+ a (zero)) (zero))), (forall a (forall b (= (+ a (succ b)) (succ (+ a b)))))
* Do you need a type system? If you have sets, you can accidentally treat a set as a boolean. But good rules won't allow
  such statements to be provable, so it's fine. A little weird though.

Going with the tree style.
Sketch program for ZFC:



|#
#;{
   (theory
    zfc
    (axiom extensionality (forall x (forall y (=> (forall z (<=> (in z x) (in z y))) (= x y)))))
    (axiom regularity (forall x (exists a (=> (in a x)
                                              (exists y (and (in y x)
                                                             (not (exists z (and (in z y) (in z x))))))))))
    ; NOTE: tentative design for schemas. can take in macros. Messy
    ; could also just have them use free vars and treat them as a prop lol.
    (axiom-schema (specification pred) (forall z (exists y (forall x (<=> (in x y) (and (in x z) (pred x z)))))))
    ...
    (axiom union (forall F (exists A (forall Y (forall x (=> (and (in x Y) (in Y F)) (in x A)))))))
    (define-operator (self-union F))
    (define-macro (self-union? F uF) (forall x (<=> (in x uF) (exists Y (and (in x Y) (in Y F))))))
    ; can't use union? in axiom bc it's too strict, saying it's THE union instead of a superset.
    (axiom union-operator (forall F (self-union? F (union F))))
    ; TODO prove (forall F (exists! uF (self-union? F uF)))
    (define-operator (singleton x))
    ; ...
    (define-operator (pair x y))
    ; ...
    (define-operator (succ y))
    (define-macro (succ? y sy) (self-union? (pair y (singleton y)) sy))
    (axiom infinity (exists X (and (exists e (and (forall z (not (in z e))) (in e X)))
                                   (forall y (=> (in y X) (in (succ y) X))))))
    ...)

(define-macro (empty-set? x) (forall y (not (in y x))))

(theorem empty-exists (exists e (empty-set? x))
  (forall-inst ))
}
