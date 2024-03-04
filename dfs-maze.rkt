#lang racket

(require 2htdp/image
         2htdp/universe)

(define px-width 400)
(define px-height 400)
(define width 20)
(define height 20)

(define MODE 'dfs)
;(define MODE 'bfs)

; a Position is a
(struct position [x y] #:transparent)
; where x and y are naturals

; a Tree is a
(struct tree [edges width height] #:transparent)
; where
; edges is a (hash-of Position Position). they're directed edges, key is child parent is value
; width is a natural representing the maximum position x value
; height is a natural representing the maximum position y value

; a Search is a
(struct search [tree seen-positions stack] #:transparent)
; where
; tree is a Tree
; seen-positions is a (set/c Position)
; stack is a (listof (list Position Position)) where the first is the child and the second is the parent.
; INVARIANT: seen-positions is the same as the set of all positions appearing in tree
; INVARIANT: the parents of stack should be in seen-positions

(define (search-step srch)
  (match (search-filter-seen-in-stack srch)
    [(search tre seen-positions (cons (list child parent) stack))
     (define tre^ (tree-add-edge tre child parent))
     (define seen-positions^ (set-add seen-positions child))
     (search tre^
             seen-positions^
             (match MODE
               ['dfs
                (append (for/list ([child^ (shuffle (tree-get-children tre seen-positions^ child))])
                          (list child^ child))
                        stack)]
               ['bfs
                (append stack
                        (reverse
                         (for/list ([child^ (shuffle (tree-get-children tre seen-positions^ child))])
                           (list child^ child))))]))]
    [_ srch]))

(define (search-filter-seen-in-stack srch)
  (match srch
    [(search tre seen-positions stack)
     (search tre seen-positions (stack-filter-seen stack seen-positions))]))

(define (stack-filter-seen stack seen-positions)
  (for/list ([pair stack]
             #:unless (set-member? seen-positions (first pair)))
    pair))

(define (tree-add-edge tre child parent)
  (match tre
    [(tree edges width height)
     (tree (hash-set edges child parent)
           width
           height)]))

(define (tree-get-children tre seen-positions parent)
  ; assumes parent is in the tree and seen-positions
  (define width (tree-width tre))
  (define height (tree-height tre))
  (define x (position-x parent))
  (define y (position-y parent))
  (define naive-adjacents
    (for*/list ([dx (list -1 0 1)]
                [dy (list -1 0 1)]
                #:unless (= 0 dx dy)
                #:when (member 0 (list dx dy)))
      (position (+ x dx)
                (+ y dy))))
  (for/list ([position naive-adjacents]
             #:when (position-in-bounds? position width height)
             #:unless (set-member? seen-positions position))
    position))

(define (position-in-bounds? pos width height)
  (match pos
    [(position x y)
     (and (<= 0 x (sub1 width))
          (<= 0 y (sub1 height)))]))

(define initial-search
  (search (tree (hash) width height)
          (set)
          (list (list (position 0 0) (position 0 0)))))

; drawing

(define (draw-search srch)
  (draw-tree (search-tree srch)))

(define (draw-tree tre)
  (match tre
    [(tree edges width height)
     (for/fold ([scene (rectangle px-width px-height "solid" "black")])
               ([(child parent) (in-hash edges)])
       (draw-edge child parent scene (/ px-width width) (/ px-height height)))]))


(define (draw-edge child parent scene cell-width cell-height)
  (define pen (make-pen "white" (/ (min cell-width cell-height) 2) "solid" "round" "round"))
  (add-line scene
            (+ (* (position-x child) cell-width) (/ cell-width 2))
            (+ (* (position-y child) cell-height) (/ cell-height 2))
            (+ (* (position-x parent) cell-width) (/ cell-width 2))
            (+ (* (position-y parent) cell-height) (/ cell-height 2))
            pen))

(void
 (big-bang initial-search
           [to-draw draw-search]
           [on-tick search-step]))
