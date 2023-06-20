#lang racket

; a checker for proofs in system NK (see https://en.wikipedia.org/wiki/Sequent_calculus)

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
