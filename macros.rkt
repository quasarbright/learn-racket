#lang racket

(define-syntax-rule (swap x y)
  (let ([tmp x])
    (set! x y)
    (set! y tmp)))

(define first 1)
(define last 2)
(swap first last)

; getter and setter for val macro
(define-values (get-val put-val!)
  (let ([private-val 0])
    (values (lambda () private-val)
            (lambda (v) (set! private-val v)))))

; identifier macro for (get-val). doesn't need to be in parens
(define-syntax val
  (lambda (stx)
    (syntax-case stx ()
      [val (identifier? (syntax val)) (syntax (get-val))])))

; want to be able to say (set! val 2), not (put-val! 2)
(define-syntax-rule (define-get/put-id id get put!)
  (define-syntax id
    (make-set!-transformer
     (lambda (stx)
       (syntax-case stx (set!)
         [id (identifier? (syntax id)) (syntax (get))]
         [(set! id e) (syntax (put! e))])))))


(define-get/put-id val3 get-val put-val!)
; now you can run (set! val3 2), but not (set! val 2)
(set! val3 11)


;; call by reference (mutating args mutates actual values)
; normally, you'd have to pass in getter and setter. But macros can automate that

;; allows you to define call-by-reference functions. arguments to these functions must be variable references
(define-syntax-rule (define-cbr (id arg ...) body)
  (begin
    (define-syntax id
      (syntax-rules ()
        [(id actual (... ...))
         (do-f (lambda () actual) ; here, we translate a call (f a b) to (do-f get-a get-b set-a set-b) basically. define-for-cbr defines do-f
               (... ...)
               (lambda (v)
                 (set! actual v))
               (... ...))]))
    (define-for-cbr do-f (arg ...)
      ()
      body)))

;; takes in a function definition and converts it to one that takes in getters and setters for arguments and maps getters and setters to the argument names in the body
(define-syntax define-for-cbr
  (syntax-rules ()
    [(define-for-cbr do-f (id0 id ...) ; ids are arg names
       (gens ...) body) ; gens are a bunch of [a get_i set_i] name, getter name, setter name triplets
     ; the idea is to make gens for each arg name
     (define-for-cbr do-f (id ...)
       (gens ... (id0 get put)) body)] ; this will generate a [a get_i set_i] (get and put get unique-ified)
    [(define-for-cbr do-f ()
       ((id get put) ...) body) ; all the args are gen-ed
     (define (do-f get ... put ...) ; here, we define the function which takes in getters and setters and runs the body
       (define-get/put-id id get put) ... ; add setters under the args' names
       body)]))

(define-cbr (f a b)
  (swap a b))

#;(let ([x 1] [y 2])
    (f x y)
    (list x y))

;; simple list comprehension macro

; (list-comp body a xs) -> (map (lambda (a) body) xs)

(define-syntax-rule (list-comp body a xs)
  (map (lambda (a) body) xs))

#;(list-comp (* 2 x) x (list 1 2 3))

;; list comprehension with multiple sources

; ((+ x y) (x xs) (y ys))

(define (concat xss)
  (cond [(empty? xss) empty]
        [else (append (car xss) (concat (cdr xss)))]))

(define (list-bind xs k) (concat (map k xs)))
(define (list-return x) (cons x '()))

(define-syntax list-comp2
  (syntax-rules ()
    [(list-comp2 body (x0 xs0) (x xs) ...)
     (list-bind xs0 (lambda (x0) (list-comp2 body (x xs) ...)))]
    [(list-comp2 body) (list-return body)]))

(check-equal? '(1 2) (list-comp2 x (x (list 1 2))))
(check-equal? '(10 14 15 21) (list-comp2 (* x y) (x (list 2 3)) (y (list 5 7))))

; do-notation

#;(define-syntax do
    (syntax-rules (<- :=)
      [(do bind [(x <- e)]) (error "last statement of do block cannot be binding")] ; this will be a runtime error. idk how to throw macro-time errors without quasi-quote
      [(do bind [(x := e)]) (error "last statement of do block cannot be binding")]
      [(do bind [b]) b]
      [(do bind [(x <- e) b ...]) (bind e (lambda (x) (do bind [b ...])))]
      [(do bind [(x := e) b ...]) (let ((x e)) (do bind [b ...]))]
      [(do bind [e b ...]) (bind e (lambda (_) (do bind [b ...])))]))

#;(define-syntax (do stx)
    (syntax-case stx (<- :=)
      [(do bind [(x <- e)]) (raise-syntax-error #f "last statement of do cannot be a binding" stx #'(x <- e))]
      [(do bind [(x := e)]) (raise-syntax-error #f "last statement of do cannot be a binding" stx #'(x := e))]
      [(do bind [b]) #'b]
      [(do bind [(x <- e) b ...]) #'(bind e (lambda (x) (do bind [b ...])))]
      [(do bind [(x := e) b ...]) #'(let ((x e)) (do bind [b ...]))]
      [(do bind [e b ...]) #'(bind e (lambda (_) (do bind [b ...])))]))

(define-syntax (do stx)
  (syntax-case stx (<- :=)
    [(do bind [(x <- e)]) (raise-syntax-error #f "last statement of do cannot be a binding" stx #'(x <- e))]
    [(do bind [(x := e)]) (raise-syntax-error #f "last statement of do cannot be a binding" stx #'(x := e))]
    [(do bind [b]) #'b]
    #;[(do bind [statement b ...])
       (syntax-case statement (<- :=)
         [(x <- e) #'(bind e (lambda (x) (do bind [b ...])))]
         [[(x := e) b ...] #'(let ((x e)) (do bind [b ...]))]
         [(do bind [e b ...]) #'(bind e (lambda (_) (do bind [b ...])))]
         )]
    [(do bind [(x <- e) b ...]) #'(bind e (lambda (x) (do bind [b ...])))]
    [(do bind [(x := e) b ...]) #'(let ((x e)) (do bind [b ...]))]
    [(do bind [e b ...]) #'(bind e (lambda (_) (do bind [b ...])))]
    ))
;   ]))

(require rackunit)

(check-equal?
 '(10 14 15 21)
 (let ([bind list-bind] [return list-return])
   (do list-bind [(x <- (list 2 3))
                  (y <- (list 5 7))
                  (ans := (* x y))
                  (list-return ans)])))

; monad comprehension

(define (list-guard p) (if p (list-return void) '()))

(define-syntax monad-comp
  (syntax-rules (<-)
    [(monad-comp bind return guard [body]) (return body)] ; no more clauses, return body
    [(monad-comp bind return guard [body (x <- e) . rest]) (bind e (lambda (x) (monad-comp bind return guard [body . rest])))] ; use monadic bind
    [(monad-comp bind return guard [body p . rest]) (bind (guard p) (lambda (_) (monad-comp bind return guard [body . rest])))] ; filter using guard
    ))

(check-equal?
 '(10 14 15 21)
 (monad-comp list-bind list-return list-guard
             [(* x y)
              (x <- (list 1 2 3))
              (> x 1)
              (y <- (list 5 7))]))

