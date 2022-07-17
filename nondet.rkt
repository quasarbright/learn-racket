#lang racket

;; Non-determinism via delimited continuations

(require racket/control
         racket/generator)

(define prompt-tag (make-continuation-prompt-tag))

#;(struct node (choice children))
(struct result (val))

(define (choice . xs)
  (shift-at prompt-tag k (map k xs)))

(define (choose-from xs)
  (shift-at prompt-tag k
            (for/list ([x xs])
              (k x))))

(define-syntax-rule (non-det body ...)
  (non-det/proc (thunk body ...)))

(define (non-det/proc thnk)
  (map result-val (flatten (reset-at prompt-tag (result (thnk))))))

(define (flatten lol)
  (cond
    [((listof (listof any/c)) lol) (apply append (map flatten lol))]
    [else lol]))

(define sat
  (non-det (let ([p (choice #t #f)]
                 [q (choice #t #f)]
                 [r (choice #t #f)])
             (when (and p (or q (not r)))
               (displayln (list p q r))))))

;; Doesn't work. They don't compose for some reason
#;(define pythagorean-triples
    (generator ()
               (non-det (let ([a (choose-from (in-naturals))]
                              [b (choose-from (in-naturals))]
                              [c (choose-from (in-naturals))])
                          (when (= (* c c) (+ (* a a) (* b b)))
                            (yield (list a b c)))))))

