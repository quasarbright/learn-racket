#lang racket

; following along with https://www.cs.tufts.edu/~nr/cs257/archive/sam-tobin-hochstadt/typed-racket-popl-08.pdf

; Represents a program
(define (expr? v)
  (match v
    [(or (? symbol?)
         `(,(? expr?) ,(? expr?))
         `(if ,(? expr?) ,(? expr?) ,(? expr?))
         `(lambda ([,(? symbol?) : ,(? type-datum?)]) ,(? expr?))
         (? number?)
         (? boolean?))
     #t]
    [_ #f]))

; Represents the surface syntax of a type
(define (type-datum? v)
  (match v
    [(or 'Top 'Any
         'Bottom 'Never
         Number
         Boolean ; ~> (U #t #f)
         #t
         #f
         `(-> ,(? type-datum?) ,(? type-datum?))
         `(-> ,(? type-datum?) ,(? latent-predicate-datum?) ,(? type-datum?))
         `(U ,(? type-datum?) ...))
     #t]
    [_ #f]))

; Represents type information about the argument. Like "x is number" in typescript (the latent predicate is number).
(define (latent-predicate-datum? v)
  ; No surface syntax for "nothing", or the dot in the paper. Just do (-> a b) for that
  (type-datum? v))

; Represents the result of a program
(define (value? v)
  (or (boolean? v) (number? v) (procedure? v)))

; Universal supertype. any
(struct top [] #:transparent)
; Universal subtype. never
(struct bottom [] #:transparent)
(struct union-type [members] #:transparent)
; Function type. Predicate communicates type information about the argument
(struct function-type [arg-type predicate ret-type])
(struct number-type [] #:transparent)
; Represents the type of an expression
(define (type? v)
  (match v
    [(or (struct* top ())
         (struct* bottom ())
         (union-type (list (? type?) ...))
         (function-type (? type?) (? latent-predicate?) (? type?))
         #t
         #f
         (struct* number-type ()))
     #t]
    [_ #f]))

; Represents an empty predicate. Denoted as a dot in the paper.
(struct nothing [] #:transparent)
; If a type, then the function returning true means the argument is of the type, and false means it's not.
; Otherwise, no type information is communicated.
(define (latent-predicate? v)
  (or (type? v) (nothing? v)))

; The expression returns a boolean representing whether var is of type.
(struct annotation [var type] #:transparent)
; Represents type-relevant information that an expression's result tells us.
; Although visible is in the name, this is NOT in the surface syntax.
(define (visible-predicate? v)
  (match v
    [(or
      ; the expression evaluates to whether the variable is of that type
      (annotation (? symbol?) (? type?))
      ; the expression evaluates to the value of a variable
      (? symbol?)
      ; the expression evaluates to #t
      #t
      ; the expression evaluates to #f
      #f
      ; no extra type-relevant information
      (? nothing?))]))
