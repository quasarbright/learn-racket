#lang racket


; NOTE: never got this working, see the yield version.

(module+ test (require rackunit))
(require (prefix-in racket: racket))


; implementing delimited continuations, dynamic wind, and parameters in terms of call/cc

; dynamic wind implementation taken from https://www.scheme.com/tspl4/control.html#./control:h6
; TODO understand
; stack of (cons before after) thunk pairs
; first pair is from innermost dynamic-wind
(define winders '())

; find the common tail between both lists (using eq?)
(define common-tail
  (lambda (x y)
    (let ([lx (length x)] [ly (length y)])
      (do ([x (if (> lx ly) (list-tail x (- lx ly)) x) (cdr x)]
           [y (if (> ly lx) (list-tail y (- ly lx)) y) (cdr y)])
          ((eq? x y) x)))))

; > (let ([tail '(3 4)]) (without-tail (cons 1 (cons 2 tail))))
; '(1 2)
; replaces tail in items with '() if it is found as a tail. uses eq?.
(define (without-tail items tail)
  (let loop ([items items])
    (if (or (null? items) (eq? items tail))
        '()
        (cons (first items) (loop (rest items))))))

; call befores and afters according to the current dynamic environment and the
; one we're jumping into.
; this function is used when calling a continuation.
(define do-wind
  (lambda (new)
    ; someone just called a continuation.
    ; winders is from the call-site of the continuation.
    ; new is saved from the call/cc that created the continuation.

    ; we ignore common-tail thunks because they come from a dynamic-wind that encloses both the continuation
    ; we're calling and the call/cc that created it. we don't need to call those befores because we never left the
    ; dynamic extent, so we're not re-entering.
    ; we don't need to call the afters ourselves because the continuation includes the enclosing dynamic-wind that will call
    ; the afters when execution reaches that point.
    (define tail (common-tail new winders))

    ; we need to run afters from winders because we're about to jump out of this dynamic extent.
    ; thunks are stored with the innermost dynamic-wind's thunk pair first, which means we execute afters
    ; in that order (innermost dynamic wind ends first).
    (define afters (map cdr (without-tail winders tail)))
    (for ([after afters]) (after))

    ; we need to run befores from new because we're about to jump back into the continuation's dynamic extent.
    ; thunks are stored with the innermost dynamic-wind's thunk pair first, which means we execute befores
    ; in the reverse of that order (innermost dynamic wind began last).
    (define befores (reverse (map car (without-tail new tail))))
    (for ([before befores]) (before))))
; notes from figuring out how this works:
; new is the winders at the time of the call/cc itself.
; do-wind gets called when k gets called.
; by comparing winders (from when k gets called) to new (from
; when call/cc was called), we can figure out which thunks
; need to be invoked.
; ex: (dynamic-wind before (call/cc (lambda (k) (save k) ...)) after)
; if we invoke saved-k from outside of this dynamid-wind, we need to
; run the before thunk manually. we don't need to run the after thunk since k captures
; the dynamic-wind and will therefore end up running the after thunk.
; let's think about this case:
; (dynamic-wind before2 (saved-k "hello") after2)
; assuming no other dynamid-winds, at the point of the saved-k, winders will be (list (cons before2 after2)).
; saved-k will invoke do-wind with new as (list (cons before after)).
; common-tail will just be '().
; we are jumping out of the second dynamic-wind, so we need to call after2.
; we are jumping into the first one, so we need to call before.
;
; In general, ignoring common-tail thunks, when calling a continuation, we need to call afters from the
; current winders list (winders) since we're jumping out of the current dynamic extent,
; and call befores from the continuation's saved winders list (new)
; since we're jumping back into the continuation's dynamic extent.
; common-tail is the list of thunks from dynamic-winds surrounding both the k's call/cc and the invocation of k,
; so they can be ignored. the befores don't need to run because we never left the dynamic extent, we just jumped around
; within it. the afters will run on their own since the dynamic-wind is captured by k, which will run the afters.
;
; for order of thunk calling, the first element of winder lists is from the innermost dynamic-wind.
; Since the outermost dynamic-wind began first and will end last, its before should run first and its after should run last.
; so we run the befores in the reverse order of how they appear in the list and the afters in the same order as how they appear in the list.

; a wrapper around the primitive call/cc that supports dynamic-wind
(define call/cc
  (lambda (f)
    (racket:call/cc
     (lambda (k)
       ; save the dynamic environment at the time of the call/cc
       (define saved-winders winders)
       (f (lambda (v)
            (unless (eq? saved-winders winders)
              (do-wind saved-winders))
            (k v)))))))

(define-syntax-rule (let/cc k body ...) (call/cc (lambda (k) body ...)))

; takes in 3 thunks.
; returns the result of (body).
; calls 'in' when we enter the dynamic extent of 'body' and
; 'out' when we leave it. Continuations respect this, so
; jumping in and out using continuations will call in and out as
; appropriate.
(define dynamic-wind
  ; I call in before and out after elsewhere
  (lambda (in body out)
    (in)
    (set! winders (cons (cons in out) winders))
    (call-with-values
     body
     (lambda ans*
       (set! winders (cdr winders))
       (out)
       (apply values ans*)))))

; delimited continuations originally taken from https://okmij.org/ftp/continuations/implementations.html

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

; Execute a thunk in the empty environment -- at the bottom of the stack --
; and pass the result, too encapsulated as a thunk, to the
; continuation at the top of pstack. The top-most pstack frame is
; removed.
;
; We rely on the insight that the capture of a delimited continuation
; can be reduced to the capture of the undelimited one. We invoke
; (go th) to execute the thunk th in the delimited context.
; The call to 'go' is evaluated almost in the empty context
; (near the `bottom of the stack'). Therefore,
; any call/cc operation encountered during the evaluation of th
; will capture at most the context established by the 'go' call, NOT
; including the context of go's caller. Informally, invoking (go th)
; creates a new stack segment; continuations captured by call/cc
; cannot span the segment boundaries, and are hence delimited.
;
; This emulation of delimited control is efficient providing that
; call/cc is implemented efficiently, with the hybrid heap/stack or
; stack segment strategies.

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

;; let push_prompt_aux (p : 'a prompt) (body : unit -> 'a) : 'a =
;;   let ek = get_ek () in
;;   let pframe = {pfr_mark = p.mark; pfr_ek = ek} in
;;   let () = ptop := pframe :: (!ptop) in
;;   let res = body () in
;;   let () = p.mbox := fun () -> res in
;;   raise DelimCCE

(define (reset* th)
  (call/cc
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
  (call-with-composable-continuation
   (lambda (k); stack fragment
     (go
      (lambda ()
        ; go discards the current context (k). so if you just return a value from the shift body without any continuation stuff,
        ; it gets sent to the delimiter's continuation since it's next on the stack. that's the abort behavior of shift.
        (f k))))))

; I wrote this, inspired by oleg's shift* implementation.
(define (call-with-composable-continuation f)
  ; If you call this lambda in f, you'll do k, but when the body of the reset is done, instead of returning to
  ; the reset's continuation, it'll return HERE to k1 and fill in the hole in the shift with the value of finishing
  ; the reset! And then the next thing on the stack is the reset's continuation, so when the shift body finishes,
  ; it returns to the reset's continuation. wow.
  ; TODO what happens when you use this without a delimiter? you won't end up back at the scheduler, so you'll never
  ; invoke k1. Is there a way to effectively surround the program in a reset from the scheduler?
  ; or can you wrap this in a go and preserve its semantics somehow?
  ; TODO make it work with parameters. maybe push some of the current winders?
  ; we want to prevent our thunks from running because we aren't leaving the dynamic extent!
  ; maybe we need to use the racket continuation operators in some places. but we do need to
  ; do some winding stuff here.
  ; I think we need to use racket call/cc internally and manage winding stuff in all continuation operators.
  ; Might be easiest to just define shift, reset, etc. using racket call/cc and ignoring winding and creating wrappers around each
  ; of them that handle winding. like what we did for call/cc, but for everything.

  ; making this the racket one treats k as non-jumping
  (racket:let/cc k
    (f (lambda (v)
         (let/cc k1
           (set! pstack (cons k1 pstack))
           (k v))))))

; ------------------------------- Syntactic sugar

(define-syntax reset
  (syntax-rules ()
    ((_ ?e ?f ...) (reset* (lambda () ?e ?f ...)))))

(define-syntax shift
  (syntax-rules ()
    ((_ ?k ?e ?f ...) (shift* (lambda (?k) ?e ?f ...)))))


; parameters by me

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
  ; install barriers. seems to be fine though.

  (define-namespace-anchor anc)
  (define ns (namespace-anchor->namespace anc))

  (define (eval/cc expr) (eval expr ns))
  (define (eval/racket expr) (eval expr (parameterize ([current-namespace (module->namespace 'racket)])
                                          (namespace-require 'racket/control)
                                          (current-namespace))))
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
              (reset (dynamic-wind (lambda () (displayln "in" out))
                                   (lambda () (shift k 1))
                                   (lambda () (displayln "out" out))))
              (string-split (get-output-string out)))))
  (test-case "reset shift with k simple usage in dynamic wind"
    (teval '(let ([out (open-output-string)])
              (reset (dynamic-wind (lambda () (displayln "in" out))
                                   (lambda () (shift k (k 1)))
                                   (lambda () (displayln "out" out))))
              (string-split (get-output-string out)))))
  (test-case "dynamic wind version of parameterize around composable continuation"
    (teval '(let ([out (open-output-string)])
              (dynamic-wind
                (lambda () (displayln "reset in" out))
                (lambda ()
                  (reset (list (shift k (dynamic-wind
                                          (lambda () (displayln "k in" out))
                                          (lambda () (k 2))
                                          (lambda () (displayln "k out" out))))
                               (dynamic-wind
                                 (lambda () (displayln "after in" out))
                                 (lambda () 99)
                                 (lambda () (displayln "after out" out))))))
                (lambda () (displayln "reset out" out)))
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
              (string-split (get-output-string out) "\n")))))

; these have weird behavior compared to real racket.
; outs execute too many times.
#;
(let ([saved-k #f])
  (reset
   (dynamic-wind
     (lambda () (displayln "in reset"))
     (lambda () (add1 (shift k (set! saved-k k) 99)))
     (lambda () (displayln "out reset"))))
  (dynamic-wind
    (lambda () (displayln "in user"))
    (lambda () (saved-k 0))
    (lambda () (displayln "out user"))))
; this one errors!
#;
(let ([saved-k #f])
    (reset
     (dynamic-wind
       (lambda () (displayln "in reset"))
       (lambda () (add1 (let/cc k (set! saved-k k) 99)))
       (lambda () (displayln "out reset"))))
    (dynamic-wind
      (lambda () (displayln "in user"))
      (lambda () (saved-k 0))
      (lambda () (displayln "out user"))))
; maybe internals should use the real call/cc? most of them shouldn't though.
; i was thinking that maybe shift should use the real call/cc and do its own
; winding stuff, but even let/cc is broken! maybe reset is broken?

#;; parameterize around a composable continuation call
(let ([p (make-parameter 0)])
  (list (parameterize ([p 0])
          ; (p) should be 1
          (reset (list (shift k (parameterize ([p 1]) (k 2)))
                       (p))))
        (p)))
; dynamic-wind version of that ^
#;; in real racket, we get in in in out out out.
; here, we get k out before after in.
; that's why it doesn't work
(dynamic-wind
  (lambda () (displayln "reset in"))
  (lambda ()
    ; (p) should be 1
    (reset (list (shift k (dynamic-wind
                            (lambda () (displayln "k in"))
                            (lambda () (k 2))
                            (lambda () (displayln "k out"))))
                 (dynamic-wind
                   (lambda () (displayln "after in"))
                   (lambda () 99)
                   (lambda () (displayln "after out"))))))
  (lambda () (displayln "reset out")))
