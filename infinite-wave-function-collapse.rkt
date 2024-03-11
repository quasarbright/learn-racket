#lang racket

(require racket/random
         2htdp/universe
         2htdp/image)

; 2D tile-based wave-function collapse
; neighbors are up, down, left, and right, no diagonal

; single chunk generation

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
(define right-tile (set RIGHT))
(define left-tile (set LEFT))
(define up-tile (set UP))
(define down-tile (set DOWN))
(define empty-tile (set))

(define straight-tiles (list horizontal-tile vertical-tile))
(define corner-tiles (list l-tile j-tile r-tile seven-tile))
(define t-tiles (list t-tile bottom-tile vdash-tile dashv-tile))
(define single-tiles (list left-tile right-tile up-tile down-tile))

(define tiles
  (append
   (list empty-tile
         plus-tile)
   t-tiles
   straight-tiles
   corner-tiles
   single-tiles))

(define CHUNK_WIDTH  30)
(define CHUNK_HEIGHT 30)

; -> CollapsedChunk
; randomly generate a grid of tiles that are properly connected
(define (make-collapsed-chunk)
  (define chunk (make-initial-chunk))
  (chunk-fully-collapse! chunk)
  (chunk-get-collapsed chunk))

; Chunk -> Void
; collapse all waves in the chunk
(define (chunk-fully-collapse! chunk)
  (let loop ()
    (define idx-to-collapse (chunk-find-idx-to-collapse chunk))
    (when idx-to-collapse
      (chunk-collapse! chunk idx-to-collapse)
      (loop))))

; -> Chunk
; Initial uncollapsed chunk
(define (make-initial-chunk [width CHUNK_WIDTH] [height CHUNK_HEIGHT])
  (for/vector ([_ (in-range height)])
    (for/vector ([_ (in-range width)])
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
    (define neighbors (get-idx-neighbors chunk idx))
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
; Collapses the specified wave to just one item, chosen uniformly randomly from valid tiles.
(define (chunk-collapse-wave! chunk idx)
  ; before collapsing, filter the wave based on neighbors.
  ; this is only necessary in the presence of walking where fresh waves are naively added.
  (define neighbors (get-idx-neighbors chunk idx))
  (define wave
    (for/fold ([wave (chunk-get chunk idx)])
              ([(direction-to-neighbor neighbor-idx) (in-hash neighbors)])
      (define neighbor-wave (chunk-get chunk neighbor-idx))
      ; TODO this is awkward because constrain-wave is neighbor-focused
      (constrain-wave neighbor-wave wave (direction-opposite direction-to-neighbor))))
  (when (null? wave)
    (debug-display-chunk chunk)
    (error (format "empty wave found at ~a" idx)))
  (chunk-set! chunk idx (list (random-ref wave))))

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
(define (get-idx-neighbors chunk idx)
  (match idx
    [(index row col)
     (define all-neighbors (hash LEFT (index row (sub1 col))
                                 RIGHT (index row (add1 col))
                                 UP (index (sub1 row) col)
                                 DOWN (index (add1 row) col)))
     (for/hash ([(dir idx) (in-hash all-neighbors)]
                #:when (idx-in-bounds? chunk idx))
       (values dir idx))]))

; Index -> Boolean
; is the index in bounds?
(define (idx-in-bounds? chunk idx)
  (match idx
    [(index row col)
     (and (< -1 row (chunk-height chunk))
          (< -1 col (chunk-width chunk)))]))

; Chunk -> Natural
(define (chunk-width chunk)
  (vector-length (vector-ref chunk 0)))

; Chunk -> Natural
(define (chunk-height chunk)
  (vector-length chunk))

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
  (for*/or ([row (in-range (chunk-height chunk))]
               [col (in-range (chunk-width chunk))])
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
     [(== vdash-tile) "├"]
     [(== right-tile) "╶"]
     [(== left-tile) "╴"]
     [(== up-tile) "╵"]
     [(== down-tile) "╷"])))


#;(module+ main
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

; infinite treadmill, no chunking

; CollapsedChunk Direction -> CollapsedChunk
; "walk" in the direction, deleting the tiles behind and generating new tiles in front
(define (collapsed-chunk-walk collapsed-chunk direction)
  (define chunk (uncollapse-chunk collapsed-chunk))
  (chunk-walk! chunk direction)
  (chunk-fully-collapse! chunk)
  (chunk-get-collapsed chunk))

; CollapsedChunk -> Chunk
; creates a chunk that just has collapsed wave for each tile
(define (uncollapse-chunk collapsed-chunk)
  (for/vector ([row collapsed-chunk])
    (for/vector ([tile row])
      (list tile))))

; Chunk Direction -> Void
; "walk" in the direction, deleting the tiles behind and generating new tiles in front
(define (chunk-walk! chunk direction)
  (match direction
    [(== DOWN) (chunk-walk-down! chunk)]))

; Chunk -> Void
(define (chunk-walk-down! chunk)
  (for ([row-num (in-range (sub1 (chunk-height chunk)))])
    (vector-set! chunk row-num (vector-ref chunk (add1 row-num))))
  (vector-set! chunk (sub1 (chunk-height chunk)) (for/vector ([_ (chunk-width chunk)]) tiles)))

(define (display-collapsed-chunk-last-row chunk)
  (for ([tile (vector-ref chunk (sub1 CHUNK_HEIGHT))])
    (display-tile tile))
  (newline))

#;(module+ main
  (define collapsed-chunk (make-collapsed-chunk))
  (display-collapsed-chunk collapsed-chunk)
  (let loop ([collapsed-chunk collapsed-chunk])
    (define collapsed-chunk^ (collapsed-chunk-walk collapsed-chunk DOWN))
    (display-collapsed-chunk-last-row collapsed-chunk^)
    (sleep 0.1)
    (loop collapsed-chunk^)))

#|
an idea for chunking that satisfies everything:
- in seams, randomly generate a boolean in each position for whether the chunks should be connected at that point
in a repeatable way. use absolute wave position or something based on index and chunk position as the seed
- when generating a chunk, add those connectivity constraints around it as a border of straight tiles
- after chunk generation, get rid of the connectivity border
- initially, you can just do all trues to get the buffering and stuff working
|#

; proper constant-space repeatable chunking

; high level:
; we have a grid of chunks infinitely expanding in all (2D) directions.
; each chunk is procedurally generated, using its position as a random seed.
; before generation, each chunk is surrounded by a "connectivity border" of straight and empty tiles (seeded by position),
; which ensures that chunks properly connect to each other. After generation, this border is removed.
; To seed the connectivity borders, we use half-positions like (position 0.5 0) for the vertial border between
; (position 0 0) and (position 1 0). The former's chunk will use that seed for its right border and the latter for its left.

; A Position is a
(struct position [x y] #:transparent)
; where x and y are integers.
; increasing y is visually down.

; Position -> CollapsedChunk
; generate a chunk at the given position
(define (generate-collapsed-chunk pos)
  (define chunk (make-bordered-chunk pos))
  ; ensure that if we walk away and come back, we get the same chunk.
  (random-seed (->seed pos))
  (chunk-fully-collapse! chunk)
  (chunk-get-collapsed (chunk-remove-border chunk)))

; Position -> Chunk
; create an uncollapsed chunk with a connectivity border added.
; takes in pos for seeding of connectivity border.
(define (make-bordered-chunk pos)
  (define chunk (make-initial-chunk (+ 2 CHUNK_WIDTH) (+ 2 CHUNK_HEIGHT)))
  ; left border
  (random-seed (->seed (list (- (position-x pos) 0.5) (position-y pos))))
  (for ([row (in-range 1 (add1 CHUNK_HEIGHT))])
    (chunk-set! chunk
                (index row 0)
                (list (random-ref (list empty-tile horizontal-tile)))))
  ; right border
  (random-seed (->seed (list (+ (position-x pos) 0.5) (position-y pos))))
  (for ([row (in-range 1 (add1 CHUNK_HEIGHT))])
    (chunk-set! chunk
                (index row (add1 CHUNK_WIDTH))
                (list (random-ref (list empty-tile horizontal-tile)))))
  ; top border
  (random-seed (->seed (list (position-x pos) (- (position-y pos) 0.5))))
  (for ([col (in-range 1 (add1 CHUNK_WIDTH))])
    (chunk-set! chunk
                (index 0 col)
                (list (random-ref (list empty-tile vertical-tile)))))
  ; bottom border
  (random-seed (->seed (list (position-x pos) (+ (position-y pos) 0.5))))
  (for ([col (in-range 1 (add1 CHUNK_WIDTH))])
    (chunk-set! chunk
                (index (add1 CHUNK_HEIGHT) col)
                (list (random-ref (list empty-tile vertical-tile)))))
  (for ([idx (list (index 0 0)
                   (index 0 (add1 CHUNK_WIDTH))
                   (index (add1 CHUNK_HEIGHT) 0)
                   (index (add1 CHUNK_HEIGHT) (add1 CHUNK_WIDTH)))])
    (chunk-set! chunk idx (list empty-tile)))
  chunk)

; Chunk -> Chunk
; make a new chunk without the border of the given chunk
(define (chunk-remove-border chunk)
  (for/vector ([row (in-range 1 (sub1 (chunk-height chunk)))])
    (for/vector ([col (in-range 1 (sub1 (chunk-width chunk)))])
      (chunk-get chunk (index row col)))))

(define world-seed (random 4294967087))
; Any -> Integer
; generate a random seed suitable for random-seed from the given value.
; within the same run, the same value will produce the same seed. but between runs,
; it is different due to world-seed being randomly generated each run.
(define (->seed v)
  (modulo (+ world-seed (equal-hash-code v)) (sub1 (expt 2 31))))

; drawing

(define TILE_SIZE 24)

; CollapsedChunk -> Image
(define (draw-collapsed-chunk collapsed-chunk)
  (apply above
         (for/list ([row collapsed-chunk])
           (apply beside
                  (for/list ([tile row])
                    (draw-tile tile))))))

; Tile -> Image
(define (draw-tile tile)
  (define r (/ TILE_SIZE 2))
  (for/fold ([img (rectangle TILE_SIZE TILE_SIZE "solid" "white")])
            ([direction tile])
    (match direction
      [(== UP) (add-line img
                         r r
                         r 0
                         "black")]
      [(== DOWN) (add-line img
                           r r
                           r (* 2 r)
                           "black")]
      [(== LEFT) (add-line img
                           r r
                           0 r
                           "black")]
      [(== RIGHT) (add-line img
                            r r
                            (* 2 r) r
                            "black")])))

(define (handle-key pos key)
  (match pos
    [(position x y)
     (match key
       [(or "left" "a") (position (sub1 x) y)]
       [(or "right" "d") (position (add1 x) y)]
       [(or "up" "w") (position x (sub1 y))]
       [(or "down" "s") (position x (add1 y))]
       [_ pos])]))

#;(module+ main
  (void (big-bang (position 0 0)
                  [to-draw (lambda (pos) (draw-collapsed-chunk (generate-collapsed-chunk pos)))]
                  [on-key handle-key])))

; debugging

(define (display-and-return v) (displayln v) v)
(define (chunk-naive-collapse chunk)
  (for/vector ([row chunk])
    (for/vector ([wave row])
      (first wave))))
(define (debug-display-chunk chunk)
  (for ([row chunk])
    (for ([wave row])
      (match wave
        [(list) (display "?")]
        [(list tile) (display-tile tile)]
        [_ (display "*")]))
    (newline)))

; walk 1 tile at a time in a chunked world

; high level:
; building upon previous step, the "player" is in some chunk and they can walk around inside of it.
; they can also walk into another chunk.
; when the player walks near the edge of a chunk, it will show some tiles from this chunk and the next chunk.
; the screen should shift one at a time.
; we only need keep a 3x3 grid of chunks generated.
; the player is always in the center chunk. when the player walks into a new chunk, we treadmill the chunk grid.

; a ChunkGrid is a 3x3 2D vector of CollapsedChunks

; a State is a
(struct state [grid pos idx])
; where
; grid is a ChunkGrid
; pos is the position of the center chunk
; idx is the index of the player within the center chunk
; we only store grid to save time re-computing it.

; Position -> Grid
(define (generate-grid pos)
  (match pos
    [(position x y)
     (for/vector ([y (list (sub1 y) y (add1 y))])
       (for/vector ([x (list (sub1 x) x (add1 x))])
         (generate-collapsed-chunk (position x y))))]))

; State KeyPress -> State
(define (handle-key/grid st key)
  (match (key->direction key)
    [#f st]
    [dir (state-walk st dir)]))

; State Direction -> State
; take a single (tile) step in the direction of dir
(define (state-walk st dir)
  (match st
    [(state grid (and pos (position x y)) (index row col))
     (match dir
       [(== RIGHT)
        (if (= (add1 col) CHUNK_WIDTH)
            (state (grid-walk grid pos dir) (pos (add1 x) y) (index row 0))
            (state grid pos (index row (add1 col))))]
       [(== LEFT)
        (if (< (sub1 col) 0)
            (state (grid-walk grid pos dir) (pos (sub1 x) y) (index row (sub1 CHUNK_WIDTH)))
            (state grid pos (index row (sub1 col))))]
       [(== UP)
        (if (< (sub1 row) 0)
            (state (grid-walk grid pos dir) (pos x (sub1 y)) (index (sub1 CHUNK_HEIGHT) col))
            (state grid pos (index (sub1 row) col)))]
       [(== DOWN)
        (if (= (add1 row) CHUNK_HEIGHT)
            (state (grid-walk grid pos dir) (pos x (add1 y)) (index 0 col))
            (state grid pos (index (add1 row) col)))])]))

; Grid Position Direction -> Grid
; shift the grid as if walking in the given direction one whole chunk.
; for example, walking to the right will move the right chunk to the center and generate a new chunk to the right.
; pos is the pos of the old center chunk
(define (grid-walk grid pos dir)
  (match-define (position x y) pos)
  (match dir
    [(== RIGHT)
     (vector (vector (grid-get grid (index 0 1)) (grid-get grid (index 0 2)) (generate-collapsed-chunk (position (+ x 2) (+ y -1))))
             (vector (grid-get grid (index 1 1)) (grid-get grid (index 1 2)) (generate-collapsed-chunk (position (+ x 2) (+ y 0))))
             (vector (grid-get grid (index 2 1)) (grid-get grid (index 2 2)) (generate-collapsed-chunk (position (+ x 2) (+ y 1)))))]
    [(== LEFT)
     (vector (vector (generate-collapsed-chunk (position (+ x -2) (+ y -1))) (grid-get grid (index 0 0)) (grid-get grid (index 0 1)))
             (vector (generate-collapsed-chunk (position (+ x -2) (+ y 0))) (grid-get grid (index 1 0)) (grid-get grid (index 1 1)))
             (vector (generate-collapsed-chunk (position (+ x -2) (+ y 1))) (grid-get grid (index 2 0)) (grid-get grid (index 2 1))))]
    [(== UP)
     (vector (vector (generate-collapsed-chunk (position (+ x -1) (+ y -2))) (generate-collapsed-chunk (position (+ x 0) (+ y -2))) (generate-collapsed-chunk (position (+ x 1) (+ y -2))))
             (vector (grid-get grid (index 0 0)) (grid-get grid (index 0 1)) (grid-get grid (index 0 2)))
             (vector (grid-get grid (index 1 0)) (grid-get grid (index 1 1)) (grid-get grid (index 1 2))))]
    [(== DOWN)
     (vector (vector (grid-get grid (index 1 0)) (grid-get grid (index 1 1)) (grid-get grid (index 1 2)))
             (vector (grid-get grid (index 2 0)) (grid-get grid (index 2 1)) (grid-get grid (index 2 2)))
             (vector (generate-collapsed-chunk (position (+ x -1) (+ y 2))) (generate-collapsed-chunk (position (+ x 0) (+ y 2))) (generate-collapsed-chunk (position (+ x 1) (+ y 2)))))]))

;;; left off here, just finished grid-walk, need to do drawing, which is just tile sampling.

; Grid Index -> CollapsedChunk
(define grid-get chunk-get)

; KeyPress -> (or/c #f Direction)
(define (key->direction key)
  (match key
       [(or "left" "a") LEFT]
       [(or "right" "d") RIGHT]
       [(or "up" "w") UP]
       [(or "down" "s") DOWN]
       [_ #f]))
