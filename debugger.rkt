#lang racket

;; A debugger using continuations.
;; I later found out that this exists: https://github.com/AlexKnauth/debug/blob/master/debug/repl.rkt
;; Limitations: You can't give the debugger repl access to macros, only variables bound to values.
;; TODO command to print context lines

(module+ test (require rackunit))
(provide breakpoint
         current-debug-input-port
         current-debug-output-port)
(require (for-syntax syntax/parse)
         (for-syntax racket/syntax-srcloc))

(define current-debug-input-port (make-parameter ((current-get-interaction-input-port))))
(define current-debug-output-port (make-parameter (current-output-port)))

;; Opens a repl at the current point of execution with the provided variables in scope.
;; Provides a function `resume` to continue code execution. Optionally takes in
;; Note: mutations of variables passed in have no effect, but mutations of values do.
(define-syntax breakpoint
  (syntax-parser
    [(_ x:id ... (~optional (~seq #:prompt-str prompt-str) #:defaults ([prompt-str #'"debug> "])))
     (define loc (syntax-srcloc this-syntax))
     (define/syntax-parse loc-str (datum->syntax this-syntax (srcloc->string loc)))
     #'(let/ec k
         (define (resume [v (void)])
           (k v))
         (define ns (make-base-namespace))
         (parameterize ([current-namespace ns]
                        [current-prompt-read (debug-prompt-read prompt-str)]
                        ;; without this, overriding current in would make debug prompt
                        [current-get-interaction-input-port (lambda () (current-debug-input-port))]
                        [current-output-port (current-debug-output-port)])
           (displayln loc-str)
           (namespace-set-variable-value! 'x x)
           ...
           (namespace-set-variable-value! 'resume resume)
           (read-eval-print-loop)))]))

(define (debug-prompt-read [prompt-str "debug> "])
  (lambda ()
    (display prompt-str)
    (let ([in ((current-get-interaction-input-port))])
      ((current-read-interaction) (object-name in) in))))

(module+ test
  (test-case "repl has access to provided variables and resume"
    (define out (open-output-string))
    (define result #f)
    (parameterize ([current-debug-input-port (open-input-string "(resume (add1 x))")]
                   [current-debug-output-port out])
      (define x 1)
      (set! result (breakpoint x)))
    (check-equal? result 2))
  (test-case "repl input and output independent of current ports"
    (define out (open-output-string))
    (define result #f)
    (parameterize ([current-debug-input-port (open-input-string "(resume x)\n")]
                   [current-debug-output-port out])
      (with-output-to-string
        (lambda ()
          (with-input-from-string "foo"
            (lambda ()
              (define x 1)
              (set! result (breakpoint x)))))))
    (check-equal? result 1)
    (check-regexp-match ".*debug>.*" (get-output-string out))))
