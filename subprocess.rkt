#lang racket

(define-values (sp out in err)
  (subprocess #f #f #f "C:\\Windows\\System32\\whoami.exe" ))
(printf "stdout:\n~a" (port->string out))
(printf "stderr:\n~a" (port->string err))
(close-input-port out)
(close-output-port in)
(close-input-port err)
(subprocess-wait sp)
