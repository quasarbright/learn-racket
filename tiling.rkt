#lang racket

(module+ test (require rackunit))
(require racket/hash
         math/array
         math/matrix
         "vec2.rkt")

; penrose-like tiling

; you can create a tiling from a bunch of intersecting lines.
; the tiling is dual to the lines.
; at each intersection, create a rhombus tile. with sides perpendicular to
; the lines.
; for multiple tiles along a line, slide them together.
; for a penrose-like tiling, draw a "grid" containing a bunch of sets of parallel
; lines, not necessarily perpendicular to each other. For penrose tiling, each
; set should be rotated a fifth of a circle from the previous set (pentagrid).

; algorithm:
; 1. draw a bunch of lines
; 2. compute intersections
; 3. create a rhombus tile for each intersection
; 4. slide all the tiles together

; for step 3:
; start at the intersection,
; go in the direction of the line for a bit (k), create a perpendicular line at that point.
; repeat for the other direction and the other line. The intersections of these lines form
; the rhombus. Measure the side length (s). Redo with k^ = k S / s, where S is desired side length.
; TODO figure out geometry to get k correct from the beginning based on line angles or something.

; for step 4:
; you can compute pairs of adjacent tiles,
; find a pair of vertices that should become matched,
; find the difference between the two vertex positions,
; and translate the entire tile by that vector.

; data representations:
; a line will be 2 vectors, position and direction.
; an intersection will be one vector, its position.
; we'll need to associate intersections with the lines that formed them.
; a tile 4 vectors representing vertex positions.
; we'll need to associate tiles with the intersections/lines that formed them.

; A Line is a
(struct line [pos dir]
  #:transparent
  #:property prop:procedure (lambda (lin t) (vec2+ (line-pos lin) (vec2-scale (line-dir lin) t))))
; pos and dir are Vec2s
; pos is a point on the line, dir is the direction of the line (magnitude is irrelevant)
; as a procedure, the line is (lambda (t) (pos + t * dir))

; An Intersection is a
(struct intersection [pos line1 line2] #:transparent)
; pos is a Vec2
; line1 and line2 are Lines
; pos is the point of intersection

; A Tile is a
(struct tile [vertices] #:transparent)
; vertices is a list of positions (length of 4)
; adjacent elements are adjacent vertices in the tile

; (listof Line) -> (listof Tile)
; generate the tiling that is dual to the lines
(define (generate-tiling lines)
  (define intersections (filter identity (all-intersections lines)))
  (define tiles (map intersection->tile intersections))
  (define intersection-to-tile
    (for/hasheq ([int intersections]
                 [til tiles])
      (values int til)))
  (define intersection-adjacency (get-intersection-adjacency lines intersections))
  (define tile-adjacency
    (for/hasheq ([(a bs) (in-hash intersection-adjacency)])
      (values (hash-ref intersection-to-tile a)
              (for/list ([b bs]) (hash-ref intersection-to-tile b)))))
  (connect-tiles tiles tile-adjacency))

; (listof Line) -> (listof Intersection)
(define (all-intersections lines)
  (cond
    [(null? lines) '()]
    [else
     (define lin (first lines))
     (append
      (filter identity
              (for/list ([other (rest lines)])
                (intersect lin other)))
      (all-intersections (rest lines)))]))

(module+ test
  ; a square
  (let* ([lines (list (line (vec2 0 0) (vec2 1 0))
                      (line (vec2 0 1) (vec2 1 0))
                      (line (vec2 0 0) (vec2 0 1))
                      (line (vec2 1 0) (vec2 0 1)))]
         [intersections (all-intersections lines)])
    (check-equal? (length intersections)
                  4)
    (check-equal? (map intersection-pos intersections)
                 (list (vec2 0 0)
                       (vec2 1 0)
                       (vec2 0 1)
                       (vec2 1 1)))))

; p1 + t1 d1 = p2 + t2 d2
; p1x + t1 d1x = p2x + t2 d2x
; t1 d1x - t2 d2x = p2x - p1x
; t1 d1y - t2 d2y = p2y - p1y

; t1 = (p2x - p1x - t2 d2x) / d1x

; d1y (p2x - p1x - t2 d2x) / d1x - t2 d2y = p2y - p1y
; d1y (p2x - p1x) / d1x - t2 d1y d2x / d1x - t2 d2y = p2y - p1y
; d1y (p2x - p1x) / d1x - t2 (d1y d2x / d1x - d2y) = p2y - p1y
; t2 = - (p2y - p1y - d1y (p2x - p1x) / d1x) / (d1y d2x / d1x - d2y)

; Line Line -> (or/c #f Intersection)
(define (intersect line1 line2)
  (match-define (line (vec2 p1x p1y) (vec2 d1x d1y)) line1)
  (match-define (line (vec2 p2x p2y) (vec2 d2x d2y)) line2)
  ; t1 d1x - t2 d2x = p2x - p1x
  ; t1 d1y - t2 d2y = p2y - p1y
  (define M (matrix [[d1x (- d2x)]
                     [d1y (- d2y)]]))
  (define B (col-matrix [(- p2x p1x)
                         (- p2y p1y)]))
  (define solution (matrix-solve M B (lambda () #f)))
  (and solution
       (let ()
         (define t1 (array-ref solution #(0 0)))
         (define pos (line1 t1))
         (intersection pos line1 line2))))

(module+ test
  (let ([line1 (line (vec2 1 0) (vec2 2 0))]
        [line2 (line (vec2 1 0) (vec2 0 1))])
    (check-equal? (intersect line1 line2)
                  (intersection (vec2 1 0) line1 line2)))
  (check-equal? (intersect (line (vec2 0 0) (vec2 1 0))
                           (line (vec2 0 0) (vec2 1 0)))
                #f))

; Line Line -> (or/c #f Intersection)
(define (intersect! line1 line2)
  (or (intersect line1 line2) (error 'intersect! "no intersection found")))

(define DESIRED_SIDE_LENGTH 1)

; Intersection -> Tile
(define (intersection->tile int)
  (match-define
    (intersection center
                  (line _ dir1)
                  (line _ dir2))
    int)
  (define perp1 (vec2-rotate-90 dir1))
  (define perp2 (vec2-rotate-90 dir2))
  (define sides
    (list
     (line (vec2+ center dir1) perp1)
     (line (vec2+ center dir2) perp2)
     (line (vec2+ center (vec2-scale dir1 -1)) perp1)
     (line (vec2+ center (vec2-scale dir2 -1)) perp2)))
  (define (intersections sides)
    (for/list ([line1 sides]
               [line2 (append (rest sides) (list (first sides)))])
      (intersect! line1 line2)))
  (define initial-intersections (intersections sides))
  (define side-length (vec2-dist (intersection-pos (first initial-intersections))
                                 (intersection-pos (second initial-intersections))))
  (define scaled-sides
    (for/list ([side sides])
      (match side
        [(line pos dir)
         (line (vec2-lerp center pos (/ DESIRED_SIDE_LENGTH side-length))
               dir)])))
  (tile (for/list ([int (intersections scaled-sides)])
          (intersection-pos int))))

(module+ test
  (let* ([line1 (line (vec2 0 0) (vec2 1 0))]
         [line2 (line (vec2 0 0) (vec2 0 1))]
         [int (intersect line1 line2)]
         [til (intersection->tile int)])
    (match til
      [(tile (list p1
                   p2
                   p3
                   p4))
       (check-equal? p1 (vec2 1/2 1/2))
       (check-equal? p2 (vec2 -1/2 1/2))
       (check-equal? p3 (vec2 -1/2 -1/2))
       (check-equal? p4 (vec2 1/2 -1/2))])))

; (listof Line) (listof Intersection) -> (hash/c Intersection (listof Intersection))
(define (get-intersection-adjacency lines intersections)
  (for/fold ([adj (hasheq)])
            ([line lines])
    (hash-union adj
                (get-intersection-adjacency/line line intersections)
                #:combine append)))

(module+ test
  ; two right triangles, one inside the other
  ; origin is right angle, diagonal goes down-right in first quadrant
  (let* ([lines (list (line (vec2 0 0) (vec2 1 0))
                      (line (vec2 0 0) (vec2 0 1))
                      (line (vec2 0 1) (vec2 1 -1))
                      (line (vec2 0 2) (vec2 1 -1)))]
         [intersections (all-intersections lines)]
         [adj (get-intersection-adjacency lines intersections)])
    (check-equal? (length intersections) 5)
    (define corner-int (first intersections))
    (check-equal? (intersection-pos corner-int)
                  (vec2 0 0))
    (define right-int (second intersections))
    (check-equal? (intersection-pos right-int)
                  (vec2 1 0))
    (define right-int^ (third intersections))
    (check-equal? (intersection-pos right-int^)
                  (vec2 2 0))
    (define top-int (fourth intersections))
    (check-equal? (intersection-pos top-int)
                  (vec2 0 1))
    (define top-int^ (fifth intersections))
    (check-equal? (intersection-pos top-int^)
                  (vec2 0 2))
    (check-equal? (hash-ref adj corner-int)
                  (list right-int top-int))
    (check-equal? (hash-ref adj right-int)
                  (list right-int^))
    (check-equal? (hash-ref adj top-int)
                  (list top-int^ right-int))
    (check-equal? (hash-ref adj top-int^)
                  (list right-int^))))

; Line (listof Intersection) -> (hash/c Intersection (listof Intersection))
(define (get-intersection-adjacency/line lin intersections)
  (define relevant-intersections
    (filter (lambda (int) (intersection-has-line? int lin))
            intersections))
  (define sorted-intersections
    (sort relevant-intersections
          <
          #:key (lambda (int)
                  (line-project lin (intersection-pos int)))))
  (if (null? sorted-intersections)
      (hasheq)
      (for/hasheq ([a sorted-intersections]
                   [b (rest sorted-intersections)])
        (values a (list b)))))

; Intersection Line -> Boolean
(define (intersection-has-line? int lin)
  (match int
    [(intersection _ line1 line2)
     (or (eq? lin line1)
         (eq? lin line2))]))

; Line Vec2 -> Number
; How "far along" the line is the point when projected onto it.
; Ex: if the line is (line (vec2 0 0) (vec2 1 0)), the result is the x-value
(define (line-project lin v)
  (match lin
    [(line pos dir)
     (vec2-dot dir (vec2- v pos))]))

(module+ test
  (check-equal? (line-project (line (vec2 0 0) (vec2 1 0))
                              (vec2 2 3))
                2))

; 1. divide tiles into locked and unlocked. all are initially unlocked.
; 2. for each tile t:
; 3.   lock t if unlocked.
; 4.   for each unlocked tile t' connected to t (need to check both directions):
; 5.     translate t' to be connected to t and lock t'

; before translations, for each tile connection, we'll need to store a pair of vertices that need
; to end up in the same position.


; (listof Tile) (hash/c Tile (listof Tile)) -> (listof Tile)
; translate tiles next to each other
(define (connect-tiles tiles tile-adjacency)
  (define tile-connections (adj->connections tile-adjacency))
  ; maps tiles to their translated selves
  (define tile-to-translated
    (for/hasheq ([til tiles])
      (values tile tile)))

  ; invariants:
  ; unlocked tiles have not been translated
  ; locked tiles have been translated and never will be translated again
  (define locked (mutable-seteq))
  (define (lock! til)
    (set-add! locked til))
  (define (locked? til)
    (set-member? locked til))

  (define (need-to-be-connected? til til^)
    (or (member (cons til til^) tile-connections)
        (member (cons til^ til) tile-connections)))
  (define (connect! tile-to-move target-tile)
    (define-values (idx-to-move target-idx)
      (connected-tile-find-matching-vertices tile-to-move target-tile))
    ; tile-to-move has not been translated, so no need to access
    (define target-tile^ (hash-ref tile-to-translated target-tile))
    (define displacement (vec2- (tile-get-vertex target-tile^ target-idx)
                                (tile-get-vertex tile-to-move idx-to-move)))
    (define tile-to-move^ (tile-translate tile-to-move displacement))
    (hash-set! tile-to-translated tile-to-move tile-to-move^))

  (for ([til tiles])
    (lock! til)
    (for ([til^ tiles]
          #:when (need-to-be-connected? til til^)
          #:unless (locked? til^))
      (connect! til^ til)))
  (for/list ([til tiles])
    (hash-ref tile-to-translated til)))

; (hash/c T (listof T)) -> (listof (cons T T))
(define (adj->connections adj)
  (apply append
         (for/list ([(k vs) (in-hash adj)])
           (for/list ([v vs])
             (cons k v)))))

; Tile Tile -> (values Natural Natural)
; find the indices of vertices that need to be matched,
; assuming these tiles need to be connected.
(define (connected-tile-find-matching-vertices til1 til2)
  ; left off here
  ; idea: find the two inner pairs of vertices, try a pairing,
  ; if the other vertices don't match, it's the other pairing.
  'todo)

; Tile Natural -> Vec2
(define (tile-get-vertex til idx)
  (match til
    [(tile vertices)
     (list-ref vertices idx)]))

; Tile Vec2 -> Tile
(define (tile-translate til displacement)
  (match til
    [(tile vertices)
     (tile (for/list ([v vertices])
             (vec2+ v displacement)))]))
