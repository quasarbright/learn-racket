#lang racket

; a failed attempt to adapt a call/cc dynamic wind implementation
; to delimited continuations.
; see the yield version instead

(module+ test (require rackunit))
(require (prefix-in racket: racket)
         (prefix-in racket: (except-in racket/control set)))

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

; call befores and afters according to the current dynamic environment and the
; one we're jumping into, and incrementally updates winders to new,
; preserving the INVARIANT that
; a winder is in the list iff in has been called and out hasn't.
; this function is used when calling a continuation.
(define do-wind
  (lambda (new)
    ; someone just called a continuation.
    ; winders is from the call-site of the continuation.
    ; new is saved from the call/cc that created the continuation.
    ;
    ; we ignore common-tail thunks because they come from a dynamic-wind that encloses both the continuation
    ; we're calling and the call/cc that created it. we don't need to call those befores because we never left the
    ; dynamic extent, so we're not re-entering.
    ; we don't need to call the afters ourselves because the continuation includes the enclosing dynamic-wind that will call
    ; the afters when execution reaches that point.
    (let ([tail (common-tail new winders)])
      ; we need to run afters from winders because we're about to jump out of this dynamic extent.
      ; thunks are stored with the innermost dynamic-wind's thunk pair first, which means we execute afters
      ; in that order (innermost dynamic wind ends first).
      ; we pop winders as we go because a winder should be popped before its out thunk is called.
      (let f ([ls winders])
        (when (not (eq? ls tail))
          (begin
            (set! winders (cdr ls))
            ((cdar ls))
            (f (cdr ls)))))
      ; we need to run befores from new because we're about to jump back into the continuation's dynamic extent.
      ; thunks are stored with the innermost dynamic-wind's thunk pair first, which means we execute befores
      ; in the reverse of that order (innermost dynamic wind began last).
      ; we push winders as we go because a winder should be pushed after its in thunk is called.
      (let f ([ls new])
        (when (not (eq? ls tail))
          (begin
            (f (cdr ls))
            ((caar ls))
            (set! winders ls)))))
    ; the code below doesn't update winders, I missed that when I was trying to understand it
    #;#;#;#;#;
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

; wrapped control operators to play nice with dynamic-wind

; a wrapper around the primitive call/cc that supports dynamic-wind
(define call/cc
  (lambda (f)
    (racket:call/cc
     (lambda (k)
       ; save the dynamic environment at the time of the call/cc
       (define saved-winders winders)
       (f (wrap-continuation k saved-winders))))))

(define (wrap-continuation k saved-winders)
  (lambda (v)
    (unless (eq? saved-winders winders)
      (do-wind saved-winders))
    (k v)))

(define-syntax-rule (let/cc k body ...) (call/cc (lambda (k) body ...)))

(struct shift-record [thnk] #:transparent)
(define (reset* thnk)
  (define saved-winders winders)
  (let ([result (racket:reset (thnk))])
    (match result
      [(shift-record thnk)
       (do-wind saved-winders)
       ; do you need the reset*? does it break anything?
       ; we definitely need it bc otherwise, if there is another shift,
       ; it will abort too far.
       (reset* thnk)]
      [_ result])))
(define (shift* f)
  (racket:shift k
                (shift-record (lambda ()
                                (define saved-winders winders)
                                (f (wrap-composable-continuation k saved-winders))))))

(define (wrap-composable-continuation k saved-winders)
  (lambda (v)
    ; TODO need to make it think it never left the call-site of k but still
    ; do some winding stuff.
    ; what if you took the winders from winders that aren't in
    ; saved-winders, consed those onto saved-winders, and did do-wind to that?
    ; keep k's context, add the new stuff from the caller, ignore the common bits.
    ; might've gotten details wrong, but something like that.

    ; thinking:
    ; facts:
    ; - the body of a shift does not run in the dynamic extent of the inside of the reset,
    ; but the continuation does (see parameterize dyn wind and friends).
    ; - when you use a delimited, composable continuation from outside its reset,
    ; you run winders from the reset's body, but not those surrounding the reset itself.
    ; does reset delimit the dynamic extent that gets captured by continuations too? it'd make sense.
    ;
    ; when you run a continuation, act like you're not leaving the current dyn extent (k-saved-winders?), but
    ; act like you're entering the continuation's dyn extent (saved-winders).
    ; when you return from a continuation, act like you leave it, but don't execute befores from here.

    ; what if you set winders to its common tail with saved-winders and restore it after the call?
    ; that'd run saved-winders' befores, but not our afters!
    ; didn't quite work. we get the reset-in instead of reset-body in when we
    ; call a saved continuation from outside.
    ; would be interesting to inspect saved-winders and winders.
    ; reset might need to do something special
    (define k-saved-winders winders)
    (set! winders (common-tail winders saved-winders))
    (unless (eq? saved-winders winders)
      (do-wind saved-winders))
    (define result (k v))
    ; should this be do-wind?
    ; that would run our befores
    (set! winders k-saved-winders)
    result))

(define-syntax-rule (reset body ...) (reset* (lambda () body ...)))
(define-syntax-rule (shift k body ...) (shift* (lambda (k) body ...)))

(define (call-with-composable-continuation f)
  (racket:call-with-composable-continuation
   (lambda (k)
     (define saved-winders winders)
     (f (wrap-composable-continuation k saved-winders)))))

(module+ test
  (define-namespace-anchor anc)
  (define ns (namespace-anchor->namespace anc))

  (define (eval/cc expr) (eval expr ns))
  (define (eval/racket expr) (eval expr (parameterize ([current-namespace (module->namespace 'racket)])
                                          (namespace-require 'racket/control)
                                          (current-namespace))))
  (define-check (teval expr)
    (check-equal? (eval/cc expr) (eval/racket expr)))

  ; can parameterize around a composable continuation
  (teval '(let ([p (make-parameter 0)])
            (list (parameterize ([p 0])
                    ; (p) should be 1
                    (reset (list (shift k (parameterize ([p 1]) (k 2)))
                                 (p))))
                  (p))))
  ; same thing but a little weirder
  (teval '(let ([p (make-parameter 0)])
            (list (parameterize ([p 1])
                    ; (p) should be 1
                    (reset (list (shift k (parameterize ([p (add1 (p))]) (k 3)))
                                 (p))))
                  (p))))
  ; save a composable continuation and parameterize around it
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
              (string-split (get-output-string out) "\n")))))
