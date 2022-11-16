#lang racket

; https://matt.might.net/articles/programming-with-continuations--exceptions-backtracking-search-threads-generators-coroutines/

(module+ test (require rackunit))

(require racket/control)

;; goto ;;

(define (label)
  (call/cc (λ (k) (k k))))

(define (goto label)
  (label label))

(module+ test
  (define (sum xs)
    (define acc 0)
    (define loop (label))
    (if (null? xs)
        acc
        (begin (set! acc (+ (car xs) acc))
               (set! xs (cdr xs))
               (goto loop))))
  (check-equal? (sum '(1 2 3 4)) 10))

;; backtracking search (non-composable) ;;

; queue of thunks that invoke continuations.
(define search-branches '())

; forks for each value.
; tries the next search branch in the queue.
; Not necessarily one of the branches introduced by this call
(define (amb . vals)
  (let/cc k
    (set! search-branches (append search-branches
                                  (for/list ([val vals])
                                    (λ () (k val)))))
    (when (null? search-branches)
      (error "search failed"))
    (define next (car search-branches))
    (set! search-branches (cdr search-branches))
    (next)))

(define (assert condition)
  ; (amb) kills this search branch
  (unless condition (amb)))

(module+ test
  (check-equal?
   (let ([a (amb 1 2 3 4 5)]
         [b (amb 1 2 3 4 5)]
         [c (amb 1 2 3 4 5)])
     (assert (= (+ (* a a) (* b b)) (* c c)))
     (assert (<= a b))
     (list a b c))
   '(3 4 5)))

;; exceptions ;;

#;(listof (cons/c procedure? continuation?))
(define exn-handlers (list (cons raise values)))
(define exn-conts '())

(define-syntax-rule
  (try handler body ...)
  (try/proc handler (λ () body ...)))

(define (try/proc handler thnk)
  (let/cc k
    (dynamic-wind (λ () (set! exn-handlers (cons (cons handler k) exn-handlers)))
                  thnk
                  (λ () (set! exn-handlers (cdr exn-handlers))))))

(define (throw exn)
  (match-define (cons handler k) (car exn-handlers))
  (k (handler exn)))

(module+ test
  (check-equal? (try (λ (exn) 2)
                     (throw 4)
                     3)
                2))

;; threading ;;

;; (spawn thunk) puts a thread for thunk into the thread queue.
;; (quit) kills the current thread and removes it from the thread queue.
;; (yield) hands control from the current thread to another thread.
;; (start-threads) starts executing threads in the thread queue.
;; (halt) exits all threads.

; list of thunks
; that resume their thread
(define threads '())
; call to escape to the scheduler. aborts the computation.
(define threac-escape-proc (thunk (error "tried to exit a thread when not in a thread")))

; kicks off the thread scheduler and blocks until threads are completed.
(define (start-threads)
  (let ()
    (let/cc k
     (set! threac-escape-proc (thunk (k (void)))))
    ; scheduler
    (match threads
      ['() (void)]
      [(cons thd thds)
       (set! threads thds)
       (thd)])))

(define (push-thread! thnk)
  (set! threads (append threads (list thnk))))

; puts a thread for body ... in the thread queue
(define-syntax-rule
  (spawn body ...)
  (push-thread! (thunk body ... (quit))))

; kills the current thread and removes it from the queue
(define (quit)
  (threac-escape-proc))

; hand control from the current thread to another thread
(define (yield)
  (let/cc k
    (push-thread! (thunk (k (void))))
    (quit)))

; kill all threads
(define (halt)
  (let ()
    (set! threads '())
    (quit)))

(module+ test
  (let ()
    (define vs '())
    (spawn (set! vs (append vs '(1))))
    (check-equal? vs '())
    (start-threads)
    (check-equal? vs '(1))
    (check-equal? threads '())

    (set! vs '())
    (spawn (set! vs (append vs '(1)))
           (yield)
           (set! vs (append vs '(2))))
    (spawn (set! vs (append vs '(3)))
           (yield)
           (set! vs (append vs '(4))))
    (start-threads)
    (check-equal? vs '(1 3 2 4))

    (set! vs '())
    (spawn (halt))
    (spawn (set! vs #f))
    (spawn (set! vs #f))
    (start-threads)
    (check-equal? vs '())
    (check-equal? threads '())))

(module+ test
  (displayln "got to the end"))
