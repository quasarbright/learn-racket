#lang racket

; idris bang notation
; similar to javascript await notation

(define (snoc xs x)
  (foldr cons (list x) xs))

(define (bang bind-stx stx)
  ; help :: stx -> ([binding], stx)
  ; help :: stx -> ([binding], var)
  ; help takes an expression and if it is a bang, generates a binding for it and replaces the body with a gensym-ed var
  ; returns a pair of bindings which need to precede the expression and the expression
  ; disregards quotation
  (define (help stx)
    (match stx
      [`(! ,e)
       (match-let* ([(list child-bindings child-expr) (help e)]
                    (x (gensym))
                    (bindings (snoc child-bindings (list x e)))
                    (expr x)
                    )
      (list bindings expr))]
      [(list es ...)
       (let* ((child-results (map help es))
              (child-bindings (apply append (map first child-results)))
              (child-expr (map second child-results)))
         (list child-bindings child-expr))]
      [e (list '() e)]))
  (define result (help stx))
  (define bindings (first result))
  (define expr (second result))
  (foldr (match-lambda* [`((,x ,e) ,b) `(,bind-stx ,e (lambda (,x) ,b))]) expr bindings))

(bang 'bind '(pure (+ (! x) (! z))))
