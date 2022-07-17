#lang racket

(require racket/generator)

(module+ test (require rackunit))

(struct node (val left right) #:transparent)
(struct leaf () #:transparent)
;; A BT is a
#; [U (node Number BT BT) (leaf)]

(define (same-fringe t1 t2)
  (define g1 (walk t1))
  (define g2 (walk t2))
  (define (loop)
    (and (equal? (generator-state g1) (generator-state g2))
         (or (equal? 'done (generator-state g1))
             (and (equal? (g1) (g2)) (loop)))))
  (loop))

(module+ test
  (check-true (same-fringe (node 2 (node 1 (leaf) (leaf)) (node 4 (node 3 (leaf) (leaf)) (node 5 (leaf) (node 6 (leaf) (leaf)))))
                           (foldr (λ (n t) (node n (leaf) t)) (leaf) '(1 2 3 4 5 6))))
  (check-false (same-fringe (node 2 (node 1 (leaf) (leaf)) (node 4 (node 3 (leaf) (leaf)) (node 5 (leaf) (node 6 (leaf) (leaf)))))
                           (foldr (λ (n t) (node n (leaf) t)) (leaf) '(1 2 7 4 5 6)))))

#; { BT -> [Generator Number]}
(define (walk t)
  (generator ()
             (let loop ([t t])
               (match t
                 [(node v l r) (loop l) (yield v) (loop r)]
                 [(leaf) (void)]))))

(module+ test
  (check-equal? (sequence->list (in-producer (walk (node 2 (node 1 (leaf) (leaf)) (node 4 (node 3 (leaf) (leaf)) (node 5 (leaf) (node 6 (leaf) (leaf))))))
                                             (void)))
                '(1 2 3 4 5 6)))
