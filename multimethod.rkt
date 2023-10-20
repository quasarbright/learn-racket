#lang racket

; something like multi methods in clojure/common lisp

(module+ test (require rackunit))

; example:
(module+ test
  (define-generic (area [shape record-class]))
  (define-record square% [length])
  (define-record circle% [radius])
  (define-method (area [sq square%])
    (sqr (get-field sq length)))
  (define-method (area [c circle%])
    (* pi (sqr (get-field c radius))))
  (check-equal? (area (make-record square% [length 3]))
                9)
  (check-equal? (area (make-record circle% [radius 3]))
                (* pi 9))
  ; double dispatch
  ; dispatch values don't have to be classes
  (define-generic (encounter [a identity] [b identity]))
  (define-method (encounter [a 'bunny] [b 'bunny])
    'mate)
  (define-method (encounter [a 'bunny] [b 'lion])
    'die)
  (define-method (encounter [a 'lion] [b 'bunny])
    'eat)
  (define-method (encounter [a 'lion] [b 'lion])
    'fight)
  (check-equal?
   (list (encounter 'bunny 'bunny)
         (encounter 'bunny 'lion)
         (encounter 'lion 'bunny)
         (encounter 'lion 'lion))
   '(mate die eat fight)))

; the "type" for a generic argument is a dispatch function.
; a method's signature is its dispatch values.
; you decide which method to call by applying the dispatch function
; to each argument and finding a method with a matching signature.
; no hierarchy for now.

; A Generic is a
(struct generic [name dispatch-functions [methods #:mutable]]
  #:property prop:procedure
  (lambda (gen . args)
    (apply-generic gen args))
  #:property prop:object-name
  (lambda (gen) (generic-name gen)))
; where:
; name is a symbol
; dispatch-functions is a list of dispatch functions, one for each argument
; methods is a list of implementing Methods
; Represents a multi method/generic function

; A Method is a
(struct method [generic dispatch-values proc])
; where:
; generic is the generic this method is an implementation of
; dispatch-values is a list of values representing the signature of the method
; proc is a procedure representing the implementation
; proc must have arity equal to the length of dispatch-values
; represents an implementation of a multi method/generic function

; A Record is a
(struct record [class fields] #:transparent
  #:property prop:object-name
  (lambda (rcrd)
    (object-name (record-class rcrd))))
; where:
; class is the record's class
; fields is a hasheq from symbols to values representing the record's fields
; TODO reader and writer

; A Class is a
(struct class [name field-names] #:transparent
  #:property prop:object-name
  (lambda (cls)
    (class-name cls)))
; where:
; name is the class name
; field-names is a list of symbols

;; generics ;;

(define-syntax-rule
  (define-generic (name [argname dispatch-function] ...))
  (define name (generic 'name
                        (list dispatch-function ...)
                        (list))))
(define-syntax-rule
  (define-method (gen* [argname dispatch-value] ...)
    body ...)
  (let ()
    (define gen gen*)
    (define proc
      (lambda (argname ...) body ...))
    (define mthd
      (method gen (list dispatch-value ...) proc))
    (set-generic-methods! gen (cons mthd (generic-methods gen)))))

(define (apply-generic gen args)
  (match gen
    [(generic name dispatch-functions methods)
     (unless (= (length args) (generic-arity gen))
       (error name "arity error"))
     (define dispatch-values (map (lambda (f x) (f x))
                                  dispatch-functions
                                  args))
     (define mthd (find-applicable-method methods dispatch-values))
     (unless mthd
       (error (object-name gen) "could not find an applicable method"))
     (apply (method-proc mthd) args)]))

(define (generic-arity gen)
  (length (generic-dispatch-functions gen)))

(define (find-applicable-method methods dispatch-values)
  (findf (lambda (method) (method-applicable? method dispatch-values))
         methods))

(define (method-applicable? method dispatch-values)
  (equal? (method-dispatch-values method) dispatch-values))

;; records ;;

(define-syntax-rule
  (define-record name [field-name ...])
  (define name (class 'name (list 'field-name ...))))

(define-syntax-rule
  (make-record cls [field-name field-value] ...)
  (make-record* cls (list 'field-name ...) (list field-value ...)))
(define (make-record* cls field-names field-values)
  (define cls-field-names (class-field-names cls))
  (unless (equal? (apply seteq cls-field-names)
                  (apply seteq field-names))
    (error 'make-record "wrong fields"))
  (define fields (for/hasheq ([field-name field-names]
                              [field-value field-values])
                   (values field-name field-value)))
  (record cls fields))

(define-syntax-rule
  (get-field rcrd name)
  (hash-ref (record-fields rcrd)
            'name
            (lambda () (error 'get-field "field not found"))))
