#lang racket

(module+ test (require rackunit))
(provide actor
         setup
         on-receive
         this-address
         define-actor
         new-actor
         send-message
         address?)

(require racket/stxparam racket/async-channel (for-syntax syntax/parse racket/stxparam racket/pretty))

#|
An actor can receive and send messages. It can also create new actors. It has a state.
Message passing can be implemented by channels. Might want a global table of address -> channel.
You'll want something like listeners. If it's just listening for messages, loop on channel read will work.
Handle actor failure?
Actor needs state. You'll probably want initializaton fields like classes. You could just expand to a class for a simple implementation.
Actors are similar to classes, except instead of synchronous method calls, there is asynchronous message passing.
Literature suggests that addresses are a good idea. I guess when an actor is created, you only get back their address? or an actor from which you can
extract an address. That's only necessary if actors should be inspectable.
|#

#;
(begin
  (define-actor counter%
    (init-field [count 0])
    (on-receive msg
                (match msg
                  ['increment (set! count (add1 count))]
                  ['decrement (set! count (sub1 count))]
                  [`(view ,dest) (send-message dest `(count ,count))])))
  (define-actor ui%
    (init-field [counter-address (new-actor counter% [count 0])])
    (on-receive msg
                (match msg
                  ['button-clicked (send-message counter 'increment)]
                  ; like a continuation
                  ['save (send-message counter `(view ,this-address))]
                  ; it's kind of necessary to tag the output from counter
                  ; so you know who it's coming from. should messages include a sender? I'd like to avoid that.
                  [`(count ,count) (write-to-file count ...)]))))

#|
An actor has
high level:
- local state
- an address
- initialization behavior (initial field values, initialization effects, etc.)
- a message listener
low level:
- an initialization function
- a channel for messages
- a channel-reading loop
- a (preferably class-like) constructor
|#

(define address? channel?)
; for debugging/testing
(define make-address make-async-channel)
; for debugging/testing
(define address-get async-channel-get)
(define send-message async-channel-put)

(define actor<%>
  (interface ()
    #;(-> address?)
    get-address
    #;(-> any/c void?)
    ; receive a message and act on it
    on-receive
    #;(-> void?)
    ; start the message loop
    start
    ; kills the actor's thread
    kill))

(define actor%
  (class* object% (actor<%>)
    (super-new)

    (field [thd #f])
    (init-field [address (make-address)])

    (define/public (get-address) address)

    (define/public (kill) (kill-thread thd))

    (abstract on-receive)

    (define/private (receive-message) (address-get (send this get-address)))
    (define/public (start)
      (set! thd
            (thread
             (thunk
              (let loop ()
                (send this on-receive (receive-message))
                (loop))))))))

(define-syntax setup (syntax-parser [_ (raise-syntax-error this-syntax "cannot use as an expression")]))
(define-syntax on-receive (syntax-parser [_ (raise-syntax-error this-syntax "cannot use as an expression")]))

(define-syntax-parameter this-address
  (syntax-parser
    [_ (raise-syntax-error this-syntax "use of an actor keyword is not in an actor")]))

(define-syntax actor
  (syntax-parser
    [(_ (~alt (~optional ((~literal init-field) init-field-decl ...) #:defaults ([(init-field-decl 1) null]))
              (~optional ((~literal field) field-decl ...) #:defaults ([(field-decl 1) null]))
              (~optional ((~literal setup) setup-body ...) #:defaults ([(setup-body 1) null]))
              (~optional ((~literal on-receive) on-receive-expr) #:defaults ([on-receive-expr #'void])))
        ...)
     #'
     (syntax-parameterize ([this-address (syntax-parser [(~literal this-address) #'(send this get-address)])])
       (class* actor% (actor<%>)
         (super-new)
         (init-field init-field-decl ...)
         (field field-decl ...)
         setup-body
         ...
         (define/override on-receive on-receive-expr)))]))

(define-syntax-rule (define-actor name actor-body ...) (define name (actor actor-body ...)))

; for internal use. returns the actor, not the address.
(define-syntax-rule
  (#%new-actor name% field-stuff ...)
  (let* ([actor (new name% field-stuff ...)])
    ; kick off message loop
    (send actor start)
    actor))

; returns the actor's address
(define-syntax-rule
  (new-actor name% field-stuff ...)
  (let ([actor (#%new-actor name% field-stuff ...)])
    (send actor get-address)))

; creates an actor with the message behavior given by `proc`. returns the actor's address.
; TODO test that it has access to this-address
(define-syntax-rule
  (new-stateless-actor proc)
  (let ()
    (define-actor stateless-actor%
      (on-receive proc))
    (new-actor stateless-actor%)))

(module+ test
  (test-case "basic counter"
    (define-actor counter%
      (init-field [count 0])
      (on-receive
       (match-lambda
         ['increment (set! count (add1 count))]
         ['decrement (set! count (sub1 count))]
         [`(view ,dest) (send-message dest `(count ,count))])))
    (define counter-addr (new-actor counter%))
    (send-message counter-addr 'increment)
    (send-message counter-addr 'increment)
    (send-message counter-addr 'increment)
    (send-message counter-addr 'decrement)
    (define addr (make-address))
    (send-message counter-addr `(view ,addr))
    (check-equal? (address-get addr) '(count 2)))
  (test-case "repeater"
    (define-actor repeater%
      (init-field dest)
      (on-receive
       (λ (msg) (send-message dest msg) (send-message this-address msg))))
    (define chan (make-address))
    (define repeater-actor (#%new-actor repeater% [dest chan]))
    (define repeater-addr (send repeater-actor get-address))
    (send-message repeater-addr 'foo)
    (send-message repeater-addr 'bar)
    (define gets (build-list 6 (thunk* (address-get chan))))
    (check-equal? gets '(foo bar foo bar foo bar))
    (send repeater-actor kill)))
