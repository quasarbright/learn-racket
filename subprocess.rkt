#lang racket

#;(begin
    (define-values (sp out in err)
      (subprocess #f #f #f "/bin/cat"))
    (display "hello\n" in)
    (close-output-port in)
    (printf "stdout:\n~a" (port->string out))
    (printf "stderr:\n~a" (port->string err))
    (close-input-port out)
    (close-input-port err)
    (subprocess-wait sp))

(require rackunit)

(define-check (check-cmd cmd args in-s out-s err-s)
  (begin
    (define-values (sp out-p in-p err-p)
      (apply subprocess #f #f #f cmd args))
    (display in-s in-p) ; feed in-s to subprocess stdin
    (close-output-port in-p) ; close input port (eof for subprocess)
    (check-equal? (port->string out-p) out-s "stdout differs from expected")
    (check-equal? (port->string err-p) err-s "stderr differs from expected")
    (close-input-port out-p) ; close outputs
    (close-input-port err-p)
    (subprocess-wait sp)))

(test-suite
  "subprocess"
  (test-case
    "args with no stdin"
    (check-cmd "/bin/echo" (list "hello") "" "hello\n" ""))
  (test-case
    "stdin with no args"
    (check-cmd "/bin/cat" '() "hello\n" "helloo\n" "")))
