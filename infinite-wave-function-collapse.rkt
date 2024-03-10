#lang racket

(require racket/random)

; 2D tile-based wave-function collapse
; neighbors are up, down, left, and right, no diagonal

; a Wave is a (listof Tile)
; list of possibilities. implicit uniform probability distribution.

; A Chunk is a (vector-of (vector-of Wave))
; mutable 2D vector of waves

; A CollapsedChunk is a (vector-of (vector-of Tile))
; 2D vector of tiles, result of fully collapsing a Chunk.
; The tiles are properly connected

; An Index is a
(struct index [row col] #:transparent)
; row and col are zero indexed, (0,0) is top-left
; specifies a location within a chunk

; a Direction is one of
(define LEFT 'LEFT)
(define RIGHT 'RIGHT)
(define UP 'UP)
(define DOWN 'DOWN)

; a Tile is a (set/c Direction)
; representing a tile on a tilemap that is one of |,-,+,T,|-,-|, etc.
; like pipes. if a direction is present, its segment is present
; examples
(define plus-tile (set LEFT RIGHT UP DOWN))
(define l-tile (set UP RIGHT))
(define j-tile (set LEFT UP))
(define seven-tile (set LEFT DOWN))
(define r-tile (set RIGHT DOWN))
(define t-tile (set LEFT RIGHT DOWN))
(define bottom-tile (set LEFT RIGHT UP))
(define dashv-tile (set LEFT UP DOWN))
(define vdash-tile (set RIGHT UP DOWN))
(define vertical-tile (set UP DOWN))
(define horizontal-tile (set LEFT RIGHT))
(define empty-tile (set))

(define straight-tiles (list horizontal-tile vertical-tile))
(define corner-tiles (list l-tile j-tile r-tile seven-tile))
(define t-tiles (list t-tile bottom-tile vdash-tile dashv-tile))

(define tiles
  (append
   (list empty-tile
         #;plus-tile)
   ;t-tiles
   straight-tiles
   corner-tiles))

(define CHUNK_WIDTH 80)
(define CHUNK_HEIGHT 15)

; -> CollapsedChunk
; randomly generate a grid of tiles that are properly connected
(define (make-collapsed-chunk)
  (define chunk (make-initial-chunk))
  (let loop ()
    (define idx-to-collapse (chunk-find-idx-to-collapse chunk))
    (when idx-to-collapse
      (chunk-collapse! chunk idx-to-collapse)
      (loop)))
  (chunk-get-collapsed chunk))

; -> Chunk
; Initial uncollapsed chunk
(define (make-initial-chunk)
  (for/vector ([row (in-range CHUNK_HEIGHT)])
    (for/vector ([col (in-range CHUNK_WIDTH)])
      ; tiles itself is a wave
      tiles)))

; Chunk Index -> Void
; do a round of collapsing, starting at idx-to-collapse.
; fully collapses wave at idx-to-collapse and propagates constraints.
(define (chunk-collapse! chunk idx-to-collapse)
  (chunk-collapse-wave! chunk idx-to-collapse)
  (define stack (list idx-to-collapse))
  (define (push! idx) (set! stack (cons idx stack)))
  (define (pop!) (begin0 (first stack) (set! stack (rest stack))))
  (let loop ()
    (define idx (pop!))
    (define wave (chunk-get chunk idx))
    (define neighbors (get-idx-neighbors idx))
    (for ([(direction-to-neighbor neighbor-idx) (in-hash neighbors)])
      (define neighbor-wave (chunk-get chunk neighbor-idx))
      (define neighbor-wave^ (constrain-wave wave neighbor-wave direction-to-neighbor))
      (chunk-set! chunk neighbor-idx neighbor-wave^)
      (when (and (< (length neighbor-wave^) (length neighbor-wave))
                 (not (member neighbor-idx stack)))
        ; neighbor became further constrained and isn't in the stack, we need to
        ; propagate its new constraints
        (push! neighbor-idx)))
    (unless (null? stack)
      (loop))))

; Chunk Index -> Void
; Collapses the specified wave to just one item, chosen uniformly randomly
(define (chunk-collapse-wave! chunk idx)
  (chunk-set! chunk idx (list (random-ref (chunk-get chunk idx)))))

; Chunk Index -> Wave
(define (chunk-get chunk idx)
  (vector-ref (vector-ref chunk (index-row idx))
              (index-col idx)))

; Chunk Index Wave -> Void
(define (chunk-set! chunk idx wave)
  (vector-set! (vector-ref chunk (index-row idx))
               (index-col idx)
               wave))

; Index -> (hash/c Direction Index)
; get the neighboring indices in each direction,
; only returns those which are in bounds.
(define (get-idx-neighbors idx)
  (match idx
    [(index row col)
     (define all-neighbors (hash LEFT (index row (sub1 col))
                                 RIGHT (index row (add1 col))
                                 UP (index (sub1 row) col)
                                 DOWN (index (add1 row) col)))
     (for/hash ([(dir idx) (in-hash all-neighbors)]
                #:when (idx-in-bounds? idx))
       (values dir idx))]))

; Index -> Boolean
; is the index in bounds?
(define (idx-in-bounds? idx)
  (match idx
    [(index row col)
     (and (< -1 row CHUNK_HEIGHT)
          (< -1 col CHUNK_WIDTH))]))

; Wave Wave Direction -> Wave
; constrains neighbor wave to be compatible with tiles in wave.
(define (constrain-wave wave neighbor-wave direction-to-neighbor)
  (for/list ([neighbor-tile neighbor-wave]
             #:when (for/or ([tile wave])
                      (valid-tile-connection? tile neighbor-tile direction-to-neighbor)))
    neighbor-tile))

; Tile Tile Direction -> Boolean
; can neighbor-tile be placed to the direction-to-neighbor side of tile?
(define (valid-tile-connection? tile neighbor-tile direction-to-neighbor)
  (equal? (set-member? tile direction-to-neighbor)
          (set-member? neighbor-tile (direction-opposite direction-to-neighbor))))

; Direction -> Direction
(define (direction-opposite direction)
  (match direction
    [(== LEFT) RIGHT]
    [(== RIGHT) LEFT]
    [(== UP) DOWN]
    [(== DOWN) UP]))

; Chunk -> (or/c #f Index)
; find the index of a non-collapsed wave.
; return #f if there are none.
(define (chunk-find-idx-to-collapse chunk)
  (for*/or ([row (in-range CHUNK_HEIGHT)]
               [col (in-range CHUNK_WIDTH)])
    (define idx (index row col))
    (define wave (chunk-get chunk idx))
    (and (not (wave-collapsed? wave)) idx)))

; Wave -> Boolean
; is the wave collapsed?
(define (wave-collapsed? wave)
  (= 1 (length wave)))

; Chunk -> CollapsedChunk
; convert a chunk to a CollapsedChunk.
; Errors if the chunk isn't fully collapsed.
(define (chunk-get-collapsed chunk)
  (for/vector ([row chunk])
    (for/vector ([wave row])
      (match wave
        [(list tile) tile]
        [_ (error 'chunk-get-collapsed "chunk was not collapsed")]))))

(define (display-collapsed-chunk chunk)
  (for ([row chunk])
    (for ([tile row])
      (display-tile tile))
    (newline)))

(define (display-tile tile)
  (display
   (match tile
     [(== empty-tile) " "]
     [(== vertical-tile) "│"]
     [(== horizontal-tile) "─"]
     [(== l-tile) "└"]
     [(== r-tile) "┌"]
     [(== j-tile) "┘"]
     [(== seven-tile) "┐"]
     [(== plus-tile) "┼"]
     [(== t-tile) "┬"]
     [(== bottom-tile) "┴"]
     [(== dashv-tile) "┤"]
     [(== vdash-tile) "├"])))

(module+ main
  (display-collapsed-chunk (make-collapsed-chunk)))

#|
starting to think about chunking

features:
1 can walk forever in any direction
2 if you walk far away and then come back, it's the same
3 doesn't need to store everything that's been generated. space usage independent of traversed chunks
4 no seams

- each chunk has a position in chunk space, which is an integer lattice
- each chunk has a seed so if you regenerate it, it's the same every time. the seed can be from position
- neighboring chunks
  - need seamless borders
  - a trick:
    - get the 8 surrounding chunks
    - instead of starting with a fully wavy chunk, add a "border" of collapsed waves from the surrounding chunks
    - doesn't quite work because how are those chunks generated?

seems like 2 and 3 are incompatible
if you drop 2, you don't even need chunking. when you walk to the right, you can just destroy the left column and
create a new column on the right, and add some padding so it's not obvious.

screw chunking and things being the same when you come back, just do infinite scroll
|#
