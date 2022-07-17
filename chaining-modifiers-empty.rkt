;; The first three lines of this file were inserted by DrRacket. They record metadata
;; about the language level of this file in a form that our tools can easily process.
#reader(lib "htdp-intermediate-lambda-reader.ss" "lang")((modname chaining-modifiers-empty) (read-case-sensitive #t) (teachpacks ()) (htdp-settings #(#t constructor repeating-decimal #f #t none #f () #f)))
(define-struct pet [name kind num-belly-rubs])
;; A Pet is a (make-pet String String Natural)
;; Represents a pet with a name, what kind of animal they are,
;; and how many belly rubs they've gotten
(define butterscotch (make-pet "butterscotch" "cat" 7))
(define jasper (make-pet "jasper" "dog" 5))
(define dexter (make-pet "dexter" "dog" 3))
(define stanley (make-pet "stanely" "cat" 10))
(define king-paimon (make-pet "King Paimon" "rock" 100))

;; modify-num-belly-rubs : [Natural -> Natural] Pet -> Pet
;; updates p's number of belly rubs using f
(define (modify-num-belly-rubs f p)
  (make-pet (pet-name p) (pet-kind p) (f (pet-num-belly-rubs p))))

(define-struct pet-owner [name pets])
;; A PetOwner is a (make-pet-owner String [List-of Pet])
;; Represents a person with a name who owns pets
(define mike (make-pet-owner "mike" (list butterscotch)))
(define bobby (make-pet-owner "bobby" (list jasper dexter stanley)))
(define jack (make-pet-owner "jack" (list king-paimon)))

;; modify-pets : [[List-of Pet] -> [List-of Pet]] PetOwner -> PetOwner
;; updates po's pets using f
(define (modify-pets f po)
  (make-pet-owner (pet-owner-name po) (f (pet-owner-pets po))))


;; rub-all-bellies : PetOwner -> PetOwner
;; rub the belly of each pet owned by po
(define (rub-all-bellies po)
  (modify-pets (lambda (pets)
                 (map (lambda (pet)
                        (modify-num-belly-rubs add1 pet))
                      pets))
               po))
(check-expect (rub-all-bellies mike)
              (make-pet-owner "mike" (list (make-pet "butterscotch" "cat" 8))))


;; now let's make it a bit cleaner

;; modify-each-pet : [Pet -> Pet] PetOwner -> PetOwner
;; updates po's pets using f on each pet
(define (modify-each-pet f po)
  (modify-pets (lambda (pets) (map f pets)) po))

;; rub-all-bellies.v2 : PetOwner -> PetOwner
;; rub the belly of each pet owned by po
(define (rub-all-bellies.v2 po)
  (modify-each-pet (lambda (pet)
                        (modify-num-belly-rubs add1 pet))
                   po))
(check-expect (rub-all-bellies.v2 mike)
              (make-pet-owner "mike" (list (make-pet "butterscotch" "cat" 8))))

;; nicer, but we can do even better!

;; you could write modify-each-pet-num-belly-rubs, but that's a little silly and would be annoying
;; to do every time you want deep modification
;; Instead, we can write a function that chains modifiers for us

;; WARNING: This is where things get really complicated and abstract, so you may want to look at the
;; examples first. If you want to undesrtand the signature, Think about what each type variable means.
;; This WILL hurt your brain. It certainly hurt mine for a while when I first learned about this and
;; tried to make sense of the types.

;; This isn't going to change your life or anything, but I think it's pretty cool.
;; Consider it a little brain teaser and something
;; that can make deep modification nicer in functional languages :)


;; A [Modifier S T] is a [[T -> T] S -> S]
;; and represents a function which modifies an S by applying a function to
;; a T inside of it (or multiple Ts)
;; One way to think about it is that an S is the structure, and a T is the target/field within it

;; Examples:
;; modify-num-belly-rubs is a [Modifier Pet Natural]

;; modify-pets is a [Modifier PetOwner [List-of Pet]]

;; modify-each-pet is a [Modifier PetOwner Pet]. This is a modifier which modifies multiple values
;; That's interesting because there is no field of type Pet in a PetOwner. This means modifiers don't
;; necessarily have to modify fields directly

;; This signature is very complicated. Look at the example before trying to understand it

;; chain-modifiers : {S T1 T2} [Modifier S T1] [Modifier T1 T2] [T2 -> T2] S -> S
;; chains two modifiers to make a deep modifier
;; Useful if you want to modify a T2 deep inside of an S
(define (chain-modifiers modify-s-t1 modify-t1-t2 ft2 s)
  ; this abstraction captures the pattern of a modify in a lambda in a modify,
  ; which is what you do for a deep modification
  (modify-s-t1 (lambda (t1) (modify-t1-t2 ft2 t1)) s))

;; That's really hard to think about, and very abstract
;; Here's an example that might make things clearer

;; rub-all-bellies.v3 : PetOwner -> PetOwner
;; rub the belly of each pet owned by po
(define (rub-all-bellies.v3 po)
  (chain-modifiers modify-each-pet ; [Modifier PetOwner Pet]. S is PetOwner, T1 is Pet.
                   modify-num-belly-rubs ; [Modifier Pet Natural]. T1 is Pet, T2 is Natural.
                   add1 ; [Natural -> Natural]. This is our [T2 -> T2]
                   po)) ; PetOwner. This is our S
(check-expect (rub-all-bellies.v3 mike)
              (make-pet-owner "mike" (list (make-pet "butterscotch" "cat" 8))))

;; Ok, that was a lot. Don't let the signature confuse you though.
;; This is exactly what we wanted! Now we can chain modifiers. But there's a problem

;; This can't be used to chain more than 1 modifier. Why? Because the output of chain-modifiers
;; is not a modifier. But if you squint, you can kind of see a [Modifier S T2] in the last bit of
;; the signature of chain-modifiers. That's the [T2 -> T2] S -> S. But we're not returning a
;; [T2 -> T2] S -> S, which is a [Modifier S T2]. How can we make that happen? Currying

;; Remember currying is when you have a function return another function which is waiting for
;; the rest of the arguments. Currying generally helps make things chain or compose more nicely

;; Here is our old signature:
;; chain-modifiers : {S T1 T2} [Modifier S T1] [Modifier T1 T2]        [T2 -> T2] S -> S
;; Here is what we want:
;; chain-modifiers.v2 : {S T1 T2} [Modifier S T1] [Modifier T1 T2] -> [[T2 -> T2] S -> S]
;; chain-modifiers.v2 : {S T1 T2} [Modifier S T1] [Modifier T1 T2] -> [Modifier S T2]
;; Ok, so we just have to make a lambda that takes in the last two arguments, namely ft2 and s
(define (chain-modifiers.v2 modify-s-t1 modify-t1-t2)
  ; this abstraction captures the pattern of a modify in a lambda in a modify,
  ; which is what you do for a deep modification
  (lambda (ft2 s)
    (modify-s-t1 (lambda (t1) (modify-t1-t2 ft2 t1)) s)))
;; All we changed was moving the last two arguments into that lambda and returning the lambda instead
;; This lambda is itself a [Modifier S T2]. Remember a modifier is just a function which takes in an
;; updater function for a target and applies it in the structure

;; modify-each-pet-num-belly-rubs : [Modifier PetOwner Natural]
;; This modifier updates each the number of belly rubs for each pet owned by a pet owner
(define modify-each-pet-num-belly-rubs
  (chain-modifiers.v2 modify-each-pet modify-num-belly-rubs))

;; This is just like function composition using compose
(define string-length-even? (compose even? string-length))
(check-expect (string-length-even? "hello") #f)

;; rub-all-bellies.v4 : PetOwner -> PetOwner
;; rub the belly of each pet owned by po
(define (rub-all-bellies.v4 po)
  (modify-each-pet-num-belly-rubs add1 po))
(check-expect (rub-all-bellies.v4 mike)
              (make-pet-owner "mike" (list (make-pet "butterscotch" "cat" 8))))

;; Now if we want to chain three modifiers, we could do something like this.
;; Pretend a pet has a posn and we had a modify-x and a modify-pet-position
#;(define modify-each-pet-x-position
    (chain-modifiers modify-each-pet (chain-modifiers modify-pet-position modify-position-x)))
;; this would modify the x-position of each pet owned by a pet owner

;; I'll leave you with a real brain-melter
;; Would it be the same if I wrote modify-each-pet-x-position like this?
#;(define modify-each-pet-x-position
    (chain-modifiers (chain-modifiers modify-each-pet modify-pet-position) modify-position-x))
;; It's like the difference between (+ 1 (+ 2 3)) and (+ (+ 1 2) 3)
;; In other words, is modifier-chaining associative?

;; How would you write a function that takes in a list of modifiers and chains all of them?
;; You don't have the tools to write functions that take in arbitrary numbers of arguments like +,
;; So a list is the best you can do

;; What I've described here is a taste of something called lenses. A lens is essentially a getter
;; and a setter packed into one value. Lenses can modify fields, set fields, and access fields. They
;; can also be chained. And in actual racket, there is a library that will auto-generate lenses
;; for all of your struct fields just like ISL auto-generates accessors like pet-name. Very cool!

;; Hope this was interesting! Let me know if you have any more questions, and feel free to come to
;; my offices hours if you want to talk about it there :)


;; ----------------------------------------------------------------------------


;; A [NE-Modifiers S T] is a
;; (cons [Modifier S T] empty)
;; {T1} (cons [Modifier S T1] [NE-Modifiers T1 T])
;; Represents a non-empty list of modifiers whose types "line up" to allow
;; chaining

;; This little trick is called a type-aligned sequence. It's like [List-of X],
;; but elements don't need to have the same type. But for adjacent elements,
;; their types need to be related to each other in a particular way. In this
;; case, we restrict that the target of one element has to be the structure
;; of the next one

;; That {T1} is interesting because it is necessary to make sure the "middle"
;; types line up, but it doesn't occur in the [NE-Modifiers S T] type.
;; This is called an existential type. It's sort of like the "forall" {X} in the
;; signature of a function like map, but there are some subtle differences.
;; They are only necessary when you need to do crazy type stuff like this.
;; You certainly won't need them in fundies, so don't use them in a homework


;; chain-modifiers/list : [NE-Modifiers S T] -> [Modifier S T]
;; .... same as before

;; Now, if we want to allow an empty list

;; A [Modifiers S T] is a
;; empty
;; {T1} (cons [Modifier S T1] [Modifiers T1 T])
;; Represents a list of modifiers whose types "line up" to allow chaining

;; chain-modifiers/list : [Modifiers S T] -> [Modifier S T]
;; ...
#;(define (chain-modifiers/list modifiers)
  (cond
    [(empty? modifiers) ???] ;; This needs to be a modifier
    [(cons? modifiers)
     (chain-modifiers (first modifiers)
                      (chain-modifiers/list (rest modifiers)))]))

;; to fill in that ???, here are a few hints
;; chaining modifiers is a lot like function composition with compose.
;; calling (compose) with no functions actually does work. What is the result?
;; The identity function (lambda (x) x). The signature of this is {X} [X -> X]
;; Similarly, we need an "identity modifier".
;; What is its type? Well if I chain it with a [Modifier A B], I better get back a [Modifier A B]
;; So it'll be like
;; [Modifier A B]  [Modifier ? ?] -> [Modifier A B]
;; If we look at chain-modifiers' signature,
;; [Modifier S T1] [Modifier T1 T2] -> [Modifier S T2]
;; We see that S is A, T1 is B, and T2 must also be B
;; So the identity modifier [Modifier ? ?] must be [Modifier B B]
;; And it must work for any type B. Then, similar to the identity function,
;; identity-modifier : {X} [Modifier X X]

;; How would we make this?

;; identity-modifier : {X} [Modifier X X]
(define (identity-modifier f s) ...)

;; chain-modifiers/list : [Modifiers S T] -> [Modifier S T]
;; ...
(define (chain-modifiers/list modifiers)
  (cond
    [(empty? modifiers) identity-modifier]
    [(cons? modifiers)
     (chain-modifiers (first modifiers)
                      (chain-modifiers/list (rest modifiers)))]))

;; you can also just use foldr
(define (chain-modifiers/list.v2 modifiers)
  (foldr chain-modifiers identity-modifier modifiers))

;; It's a little silly, but it is necessary to allow empty chains and it leads
;; to an interesting observation

;; Addition is an associative binary operation. The identity of addition is 0
;; Multiplication is an associative binary operation. The identity of multiplication is 1

;; Function composition and modifier chaining are binary operators

;; Is function composition associative? The identity is (lambda (x) x), which
;; is a built-in function named identity
;; If you think about making a signature for compose/list, you'd need to pull
;; the same type-aligned sequence trick. And the base case yould

;; Is modifier chaining associative? The identity is identity-modifier

;; Since identity-modifier is the identity of modifier chaining, we should
;; be able to "drop it in" anywhere in a chaining and it shuoldn't change anything.
;; Similar to how we can put a zero anywhere in a sum and it won't change anything.

;; This pattern of "an associative binary operator with an identity value"
;; pops up all over the place. It's called a monoid, and there are many monoids.

;; Lists are a monoid under append with identity '()
;; Strings are a monoid under string-append with identity ""

;; And when the values are like functions and modifiers in the sense that they have two type
;; parameters with a notion of composition that goes like AB BC -> AC and an
;; identity like AA, it forms what is called a category. This is a less common pattern,
;; but it is very powerful too.


;; There's a little problem with our data definition now. If the empty list
;; of modifiers is the same as the identity modifier, it's not any [Modifier S T].
;; It's only a [Modifier S S] or something. In other words, S and T must be
;; the same in the empty case. Our data definition notation can't express this.
;; Instead, we need something like

;; A [Modifiers S T] is a
;; {X} empty : [Modifiers X X]
;; {S T1 T} (cons [Modifier S T1] [Modifiers T1 T]) : [Modifier S T]
;; Represents a list of modifiers whose types "line up" to allow chaining

;; Don't think about that too hard though, and certainly don't use it in hw!

;; This is something known as a generalized algebraic data type, or GADT
;; That's a huge rabbit hole with a lot of prerequesites, but I can teach you
;; about it if you're curious. This GADT and type-aligned sequence stuff are
;; some of the cool things you can do in Haskell. Except in Haskell, the types
;; are actually enforced!



