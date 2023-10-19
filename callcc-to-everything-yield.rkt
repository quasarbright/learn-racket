#lang racket

; NOTE: this actually works!
; actually, call/cc and call-with-current-continuation have slight bugs.

; you can get delimited continuations, composable continuations, dynamic
; wind, and parameters from just call/cc

; starting with call/cc, you can implement dynamic-wind by keeping track of "winders" and
; making a wrapped call/cc that plays nice with it. This is a little complicated and brittle,
; and trying to add support for delimited continuations is really hard. I couldn't figure it out.
; however, if you start with reset + shift, you can easily get dynamic wind in terms of something like
; algebraic effects. Then, you can make wrapped reset + shift that plays nice with it,
; and then implementing call/cc in terms of the wrapped shift gives you call/cc that plays nice too.
; The only caveat is that everything has to be in a reset or things break.

; here is the outline:
; - start out with real racket call/cc
; - get reset1 + shift1 in terms of racket:call/cc
; - get yield in terms of reset1 and shift1 (algebraic effects)
; - make dynamic wind in terms of yield
; - make user-accessible reset and shift that play nice with dynamic wind,
; essentially a handler and an effect respectively
; - make user-accessible call/cc in terms of shift
; - define parameters in terms of dynamic wind

; this is mostly a bunch of things pieced together from oleg kiselyov's blog
; https://okmij.org/ftp/continuations/implementations.html

(require (prefix-in racket: racket))
(module+ test (require rackunit))


;; --- delimited continuations from call/cc ---


; the big ideas:
; to delimit continuations in reset, save the current continuation to a variable (push onto a stack of continuations)
; and throw the current context away by jumping to a "scheduler" near the beginning of the program (basically no context).
; then, continuations captured in the reset only capture the inside of the reset
; because the context surrounding the reset is gone!
; When the body is done, the scheduler will get the result of the body and use the
; saved continuation to restore the reset's context and fill in its hole.
; This happens because if we are in a reset, the current continuation ends up back at the scheduler.
;
; the abort behavior of shift is achieved by jumping to the scheduler without saving anything.
;
; composable continuations can be achieved by saving the context of applying k before jumping.
; When the program/reset body finishes, it'll pop that saved continuation instead of the reset's.
; This has the effect of filling in the hole left by the application of k with the result of executing
; the rest of the program/reset body with k's hole filled, which is exactly what composable continuations should do!

; takes in a thunk, ends up jumping to the "scheduler", discarding your context
(define go #f)

; pstack is a list of k: stack fragments
(define pstack '())

; the "scheduler"
(let ([thnk (racket:let/cc k
              (set! go k)
              (k #f))])
  ; calling go with a thunk jumps here with the thunk as thnk, which runs the 'when' body
  (when thnk
    (let ([v (thnk)]
          [next-k (first pstack)])
      (set! pstack (rest pstack))
      ; jump to the most recent continuation with the value returned from the thunk (if it returned)
      (next-k v)))); does not return

(define (reset* th)
  (racket:call/cc
   (lambda (k)
     ; add a delimiter
     (set! pstack (cons k pstack))
     ; if no continuation stuff happens in th, it just calls k with the result in go, which is what would've happened with no reset.
     ; but cont stuff can manipulate the stack or abort the inside of go.
     ; go discards the current context. calling it jumps to the scheduler, which has basically no context. that's why
     ; continuations inside reset can only capture up to the delimiter. everything outside of the delimiter is gone! except
     ; it's saved in pstack.
     (go th)))); does not return

(define (shift* f)
  (call-with-composable-continuation1
   (lambda (k); stack fragment
     (go
      (lambda ()
        ; go discards the current context (k). so if you just return a value from the shift body without any continuation stuff,
        ; it gets sent to the delimiter's continuation since it's next on the stack. that's the abort behavior of shift.
        (f k))))))

; I wrote this, inspired by oleg's shift* implementation.
(define (call-with-composable-continuation1 f)
  ; If you call this lambda in f, you'll do k, but when the body of the reset is done, instead of returning to
  ; the reset's continuation, it'll return HERE to k1 and fill in the hole in the shift with the value of finishing
  ; the reset! And then the next thing on the stack is the reset's continuation, so when the shift body finishes,
  ; it returns to the reset's continuation. wow.
  (racket:let/cc k
    (f (lambda (v)
         (racket:let/cc k1
           (set! pstack (cons k1 pstack))
           (k v))))))

(define-syntax reset1
  (syntax-rules ()
    ((_ ?e ?f ...) (reset* (lambda () ?e ?f ...)))))

(define-syntax shift1
  (syntax-rules ()
    ((_ ?k ?e ?f ...) (shift* (lambda (?k) ?e ?f ...)))))


;; --- yield and dynamic wind in terms of reset1 and shift1 ---


; big idea:
; express control operations in terms of algebraic effects.
;
; ex: shift performs a shift-record effect containing a function
; that takes in the continuation and runs the shift body with it.
; reset is an effect handler that just calls runs the shift body
; with the resume continuation.
;
; dynamic wind is little more than an effect handler that re-performs
; effects and does the setup and teardown each time.
;
; so much simpler than the call/cc winders list approach.

(struct yield-record [v k] #:transparent)
(define (yield v) (shift1 k (yield-record v k)))

(define (dynamic-wind before-thunk thunk after-thunk)
  ; all user-accessible control operators go through yield.
  ; we run the before thunk, then execute the main thunk
  ; under a delimiter. whether it yields or terminates naturally,
  ; it will return a pure value to us, not actually jump past us.
  ; after the body returns for the first time, we run after thunk.
  ; if it was a yield, that means the body is trying to jump out.
  ; in this case, we re-yield and expect a handler to resume for us.
  ; that handler thinks its resuming the body and not us, so we bind the resumed
  ; value to reenter and loop with a thunk that resumes the body with reenter.
  ; the first thing we do when we loop is the before thunk, which is good
  ; because we just jumped back in the body. this just keeps repeating until
  ; we finally return naturally.

  ; from this, it is pretty clear how the shift abort causes the after thunk
  ; to be invoked. and if you don't think about it too much, it makes sense
  ; that the before thunk gets invoked when we re-enter from a yield. but
  ; how does a continuation know to run the before and after thunk
  ; for its dynamic context, but not act like we're exiting the caller's
  ; dynamic extent? the answer is subtle.
  ;
  ; we're yielding from here when we re-yield.
  ; this gives the outer handler a continuation
  ; that will fill in the hole of the reenter yield.
  ; In other words, the continuation that the user sees captures this
  ; dynamic-wind! When the continuation is called by the user, it fills
  ; in the hole of the reenter yield, which ends up running the before and after thunks!
  ;
  ; we don't have to wrap the continuations like with other implementations.
  ; Instead of making a dynamic wind that doesn't know about continuations and then making
  ; a wrapped call/cc that plays nice with it, we make a dynamic wind that _uses_ continuations!
  ;
  ; As for why we don't leave the dynamic extent of the caller:
  ; at this point, the continuation is basically just a normal function.
  ; the only time we jump out of a dynamic extent is via shift (yield).
  ; so the continuation re-enters its dynamic extent because it contains
  ; the dynamic-wind. and the caller thinks its just a function, so it doesn't
  ; exit its dynamic extent.
  ; the call/cc in terms of shift gets its jumping behavior by wrapping
  ; the continuation with a function that does an extra shift.

  ; yield is perfect for dynamic wind because we can "catch the jump" and execute
  ; the after thunk. and we can do the opposite on the way back in. yield makes it easy
  ; for a middle-man, dynamic-wind, to do stuff every time
  ; control jumps out of and back in to the body, which is exactly what we need for dynamic-wind.
  ; very nice.
  ; in this sense, dynamic wind is essentially an effect handler that just defers
  ; handling.
  ; the actual handler in most cases is user-reset* which handles shift effects.
  (let loop ((th (lambda () (reset1 (thunk)))))
    (before-thunk)
    (let ((res (th)))
      (after-thunk)
      (match res
        [(yield-record v k)
         (let ((reenter (yield v)))
           (loop (lambda () (k reenter))))]
        [r r]))))

(define-syntax-rule (reset body ...) (user-reset* (lambda () body ...)))
(define (user-reset* thnk)
  ; this is pretty much an effect handler on shift effects
  (match (reset1 (thnk))
    [(yield-record v k)
     (match v
       [(shift-record f) (reset (f k))]
       [_ (error "unhandled yield from user reset")])]
    [r r]))

(define-syntax-rule (shift k body ...) (user-shift* (lambda (k) body ...)))
(struct shift-record [f] #:transparent)
(define (user-shift* f)
  ; perform a shift effect
  (yield (shift-record f)))

(define call/cc
  (lambda (p)
    (shift k (k (p (lambda (x)
                     ; I think this shift is why we leave
                     ; the dynamic extent of the caller and jump.
                     (shift k1 (k x))))))))

(define-syntax-rule (let/cc k body ...) (call/cc (lambda (k) body ...)))

; TODO test
(define (call-with-composable-continuation f)
  (shift k (k (f k))))


;; --- parameters from dynamic wind ---


(define (make-parameter v-default)
  (define v v-default)
  (case-lambda
    [() v]
    [(v-new) (set! v v-new)]))
(define-syntax parameterize
  (syntax-rules ()
    [(parameterize () body ...)
     (let () body ...)]
    [(parameterize ([p v-new] pair ...) body ...)
     (parameterize-rt p v-new (lambda () (parameterize (pair ...) body ...)))]))
(define (parameterize-rt p v-new thnk)
  (let ([v-old (p)] [v-current v-new])
    (dynamic-wind
      (lambda ()
        (p v-current))
      thnk
      (lambda ()
        (set! v-current (p))
        (p v-old)))))

(module+ test
  ; these tests are captured in the continuations lol.
  ; i'll fix that if it becomes a problem, idk if i can just
  ; install barriers bc of go. seems to be fine though.

  (define-namespace-anchor anc)
  (define ns (namespace-anchor->namespace anc))

  ; evaluates using my control forms
  (define (eval/cc expr) (eval expr ns))
  ; evaluates using the real racket control forms
  (define (eval/racket expr) (eval expr (parameterize ([current-namespace (module->namespace 'racket)])
                                          (namespace-require 'racket/control)
                                          (current-namespace))))
  ; test that my control forms have the same behavior as the real racket control forms for expr
  (define-check (teval expr)
    (check-equal? (eval/cc expr) (eval/racket expr)))

  (teval '(reset 1))
  (teval '(reset (add1 (shift k 1))))
  (teval '(- (reset (add1 (shift k 1)))))
  (teval '(reset (add1 (shift k (list (k 1))))))
  (teval '(reset (add1 (call-with-composable-continuation
                        (lambda (k) 1)))))
  (teval '(reset (add1 (call-with-composable-continuation
                        (lambda (k) (k 1))))))
  (teval '(reset (add1 (call-with-composable-continuation
                        (lambda (k) (k (k 1)))))))
  (teval '(let ([p (make-parameter 1)])
            (p)))
  (teval '(let ([p (make-parameter 1)])
            (parameterize ([p 2]) (p))))
  (teval '(let ([p (make-parameter 1)])
            (p 2)
            (p)))
  ; can parameterize around a composable continuation
  (teval '(let ([p (make-parameter 0)])
              (list (parameterize ([p 0])
                      ; (p) should be 1
                      (reset (list (shift k (parameterize ([p 1]) (k 2)))
                                   (p))))
                    (p))))
  ; same thing but a little weirder
  ; (displayln "skipped")
  (teval '(let ([p (make-parameter 0)])
              (list (parameterize ([p 1])
                      ; (p) should be 1
                      (reset (list (shift k (parameterize ([p (add1 (p))]) (k 3)))
                                   (p))))
                    (p))))
  ; save a composable continuation and parameterize around it
  ; (displayln "skipped")
  (teval '(reset (let ([saved-k #f]
                         [p (make-parameter 0)])
                     (reset (list (shift k (set! saved-k k)) (p)))
                     (list (saved-k 1)
                           (parameterize ([p 10]) (saved-k 2))
                           (p)))))
  ; using a non-composable continuation restores the old parameter value
  ; when you jump
  (teval '(reset (let ([saved-k #f]
                       [p (make-parameter 0)]
                       [v #f])
                   (parameterize ([p 1])
                     (if (call/cc (lambda (k) (set! saved-k k) #f))
                         (set! v (p))
                         (void)))
                   ; it should ignore this parameterize
                   (if v (void) (parameterize ([p 3]) (saved-k #t)))
                   v)))
  ; mutations to parameters are properly scoped (no continuation stuff)
  (teval '(let ([p (make-parameter 0)])
            (parameterize ([p 1])
              (p 2)
              (parameterize ([p 3])
                (p 4))
              (p))))
  ; testing order of thunk invocation from dynamic-wind directly
  (teval '(let ([out (open-output-string)])
            (dynamic-wind (lambda () (displayln "in" out))
                          (lambda () (void))
                          (lambda () (displayln "out" out)))
            (string-split (get-output-string out))))
  (test-case "dynamic wind around simple reset"
    (teval '(let ([out (open-output-string)])
              (dynamic-wind (lambda () (displayln "in" out))
                            (lambda () (reset (void)))
                            (lambda () (displayln "out" out)))
              (string-split (get-output-string out)))))
  (test-case "shift abort in reset runs out thunk"
    (teval '(let ([out (open-output-string)])
              (reset (dynamic-wind (lambda () (displayln "reset in" out))
                                   (lambda () (shift k (dynamic-wind (lambda () (displayln "shift in" out))
                                                                     (lambda () 1)
                                                                     (lambda () (displayln "shift out" out)))))
                                   (lambda () (displayln "reset out" out))))
              (string-split (get-output-string out) "\n"))))
  (test-case "reset shift with k simple usage in dynamic wind"
    (teval '(let ([out (open-output-string)])
              (reset (dynamic-wind (lambda () (displayln "in" out))
                                   (lambda () (shift k
                                                     (displayln "shift" out)
                                                     (k 1)))
                                   (lambda () (displayln "out" out))))
              (string-split (get-output-string out) "\n"))))
  (test-case "dynamic wind version of parameterize around composable continuation"
    (teval '(let ([out (open-output-string)])
              (dynamic-wind
                (lambda () (displayln "in" out))
                (lambda ()
                  (reset (dynamic-wind (lambda () (displayln "reset in" out))
                                       (lambda () (list (shift k (dynamic-wind
                                                                   (lambda () (displayln "shift in" out))
                                                                   (lambda () (k 2))
                                                                   (lambda () (displayln "shift out" out))))
                                                        (dynamic-wind
                                                          (lambda () (displayln "after in" out))
                                                          (lambda () 99)
                                                          (lambda () (displayln "after out" out)))))
                                       (lambda () (displayln "reset out" out)))))
                (lambda () (displayln "out" out)))
              (string-split (get-output-string out) "\n"))))
  (test-case "dynamic wind version of parameterize around composable continuation used outside of reset"
    #;; like
    (let ([saved-k #f])
      (reset (list (shift k (set! saved-k k)) 99))
      (parameterize (saved-k 2)))
    (teval '(let ([out (open-output-string)]
                  [saved-k #f])
              (dynamic-wind
                (lambda () (displayln "in" out))
                (lambda ()
                  (dynamic-wind (lambda () (displayln "reset in" out))
                                (lambda ()
                                  (reset (dynamic-wind (lambda () (displayln "reset body in" out))
                                                       (lambda () (list (shift k (dynamic-wind
                                                                                   (lambda () (displayln "shift in" out))
                                                                                   (lambda () (set! saved-k k))
                                                                                   (lambda () (displayln "shift out" out))))
                                                                        (dynamic-wind
                                                                          (lambda () (displayln "after in" out))
                                                                          (lambda () 99)
                                                                          (lambda () (displayln "after out" out)))))
                                                       (lambda () (displayln "reset body out" out)))))
                                (lambda () (displayln "reset out" out)))
                  (dynamic-wind
                    (lambda () (displayln "after reset in" out))
                    (lambda () (saved-k 2))
                    (lambda () (displayln "after reset out" out))))
                (lambda () (displayln "out" out)))
              (string-split (get-output-string out) "\n"))))
  (test-case "use saved k twice dynamic wind"
    (teval '(let ([out (open-output-string)])
              (let ([saved-k #f])
                (reset
                 (dynamic-wind
                   (lambda () (displayln "in reset" out))
                   (lambda () (add1 (shift k (set! saved-k k) 99)))
                   (lambda () (displayln "out reset" out))))
                (dynamic-wind
                  (lambda () (displayln "in user" out))
                  (lambda () (list (saved-k 0) (saved-k 1)))
                  (lambda () (displayln "out user" out))))
              (string-split (get-output-string out) "\n"))))
  ; produces 0s and 1s. the parameterize around the saved-k does nothing
  ; the one in the reset overrides it.
  (teval '(let ([p (make-parameter 0)]
                [saved-k #f])
            (list (reset (parameterize ([p 1])
                           (shift k (set! saved-k k) (list (p)))
                           (p)))
                  (p)
                  (parameterize ([p 2]) (saved-k (void)))
                  (parameterize ([p 3]) (saved-k (void)))
                  (saved-k (void)))))
  ; the parameterize around the saved-k works.
  (teval '(let ([p (make-parameter 0)]
                [saved-k #f])
            (list (reset (shift k (set! saved-k k) (list (p)))
                         (p))
                  (p)
                  (parameterize ([p 2]) (saved-k (void)))
                  (parameterize ([p 3]) (saved-k (void)))
                  (saved-k (void)))))
  ; the parameterize around the saved-k works.
  ; we only get the 9 from the (list (p)) in the shift interestingly.
  ; i never thought about this behavior but the implementation passes!
  (teval '(let ([p (make-parameter 0)]
                [saved-k #f])
            (list (parameterize ([p 9])
                    (reset (shift k (set! saved-k k) (list (p)))
                           (p)))
                  (p)
                  (parameterize ([p 2]) (saved-k (void)))
                  (parameterize ([p 3]) (saved-k (void)))
                  (saved-k (void)))))
  (test-case "call/cc doesn't leave the dynamic extent"
    (teval '(let ([out (open-output-string)])
              (let ([saved-k #f])
                (reset
                 (dynamic-wind
                   (lambda () (displayln "in" out))
                   (lambda () (add1 (call/cc (lambda (k) 1))))
                   (lambda () (displayln "out" out)))))
              (string-split (get-output-string out) "\n"))))
  (test-case "call-with-comosable-continuation doesn't leave the dynamic extent"
    (teval '(let ([out (open-output-string)])
              (let ([saved-k #f])
                (reset
                 (dynamic-wind
                   (lambda () (displayln "in" out))
                   (lambda () (add1 (call-with-composable-continuation
                                     (lambda (k) 1))))
                   (lambda () (displayln "out" out)))))
              (string-split (get-output-string out) "\n")))))
; TODO test parameterize, mutate, jump out, jump back in, and make sure you get mutated value
