#lang racket

(module+ test (require rackunit))
(require (for-syntax syntax/parse))

; translation of lambda calculus to SKI calculus

; an Expr is one of
; x
; n
; (lambda (x) Expr)
; (Expr Expr)

(define S (lambda (y) (lambda (z) (lambda (x) ((y x) (z x))))))
(define K (lambda (x) (lambda (y) x)))
(define I (lambda (x) x))

; (lambda (x) x) ~> I
; (lamdba (x) y) ~> (K y)
; (lambda (x) (e1 e2)) ~> ((S (lambda (x) e1))
;                          (lambda (x) e2))

(begin-for-syntax
  (define compile/proc
    (syntax-parser
      #:literals (lambda)
      [x:id #'x]
      [n:number #'n]
      [(lambda (x:id) y:id)
       #:when (free-identifier=? #'x #'y)
       #'I]
      [(lambda (x:id) (~or y:id y:number))
       #'(K y)]
      [(lambda (x:id) (e1 e2))
       #`((S #,(compile/proc #'(lambda (x) e1)))
          #,(compile/proc #'(lambda (x) e2)))]
      [(lambda (x:id) (lambda (y:id) e))
       (compile/proc #`(lambda (x) #,(compile/proc #'(lambda (y) e))))]
      [(e1 e2) #`(#,(compile/proc #'e1) #,(compile/proc #'e2))])))

(define-syntax compile
  (syntax-parser
    [(_ e) (compile/proc #'e)]))
(define-syntax compile/datum
  (syntax-parser
    [(_ e) #`'#,(syntax->datum (compile/proc #'e))]))

(module+ test
  (check-equal? (compile/datum (lambda (x) x))
                'I)
  (check-equal? (compile/datum (lambda (x) 2))
                '(K 2))
  (check-equal? (compile/datum (lambda (x) y))
                '(K y))
  (check-equal? (compile/datum (lambda (x) (y z)))
                #;
                '((S (lambda (x) y))
                  (lambda (x) z))
                '((S (K y))
                  (K z)))
  (check-equal? (compile/datum (lambda (x) (x x)))
                #;
                '((S (lambda (x) x))
                  (lambda (x) x))
                '((S I)
                  I))
  (check-equal? (compile/datum ((lambda (x) (x x))
                                  (lambda (x) (x x))))
                #;
                '(((S (lambda (x) x))
                   (lambda (x) x))
                  ((S (lambda (x) x))
                   (lambda (x) x)))
                '(((S I)
                   I)
                  ((S I)
                   I)))
  (check-equal? (compile/datum (lambda (f) (lambda (x) (f x))))
                #;[
                   '(lambda (f) ((S (lambda (x) f)) (lambda (x) x)))
                   '(lambda (f) ((S (K f)) I))
                   '((S (lambda (f) (S (K f))))
                     (lambda (f) I))
                   '((S ((S (lambda (f) S))
                         (lambda (f) (K f))))
                     (K I))
                   '((S ((S (K S))
                         ((S (lambda (f) K))
                          (lambda (f) f))))
                     (K I))
                   '((S ((S (K S))
                         ((S (K K))
                          I)))
                     (K I))]
                '((S ((S (K S))
                      ((S (K K))
                       I)))
                  (K I)))
  (check-equal? (compile/datum (((lambda (f) (lambda (x) (f x)))
                                   (lambda (x) 3))
                                  2))
                #;['(((lambda (f) (lambda (x) (f x)))
                      (lambda (x) 3))
                     2)
                   '((((S ((S (K S))
                           ((S (K K))
                            I)))
                       (K I))
                      (lambda (x) 3))
                     2)
                   '((((S ((S (K S))
                           ((S (K K))
                            I)))
                       (K I))
                      (K 3))
                     2)]
                '((((S ((S (K S))
                        ((S (K K))
                         I)))
                    (K I))
                   (K 3))
                  2))
  (define-syntax-rule (check e) (check-equal? (compile e) e))
  (check ((lambda (x) 1) 2))
  (check (((lambda (f) (lambda (x) (f x)))
           (lambda (x) 3))
          2)))
