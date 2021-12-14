#lang racket

(require graph
         lang/posn
         2htdp/universe
         2htdp/image
         noise)

(module+ test (require rackunit))

(define PX-WIDTH 600)
(define PX-HEIGHT 600)
;; Like how many walls (not quite that)
(define WIDTH 40)
(define HEIGHT 40)
;; in pixels
(define WALL-THICKNESS 5)
;; how wide the path should be, since that's what's drawn
;; Assume width = height
(define PATH-THICKNESS (floor (- (/ PX-WIDTH WIDTH) (/ WALL-THICKNESS 2))))

;; A Maze is a
#; [Listof [List Posn Posn]]
;; Represents list of edges corresponding to connected posns
;; Walls are between posns which aren't connected. These positions are not
;; The corners of walls, but rather the maze paths themselves.

;; A World is a Natural. Represents time passed

#; { World -> Image }
;; Draw the maze at the current time
(define (draw-world t) (draw-maze (generate-maze t)))

#; { Natural {Natural} {Natural} -> Maze }
;; Randomly generate a maze
(define (generate-maze t [width WIDTH] [height HEIGHT])
  (define edges (apply append (for*/list ([x (in-range width)]
                                          [y (in-range height)])
                                (list (list (my-noise x y t) (make-posn x y) (make-posn (add1 x) y))
                                      (list (my-noise x y (- t)) (make-posn x y) (make-posn x (add1 y)))))))
  (define g (weighted-graph/undirected edges))
  (define mst (min-st-kruskal g))
  mst)

(define (my-noise x y t)
  (perlin (* x 51 (/ WIDTH)) (* y 51 (/ HEIGHT)) (/ t 300)))

#; { Maze -> Image }
;; Draw the maze
(define (draw-maze maze)
  (foldl draw-edge (rectangle PX-WIDTH PX-HEIGHT "solid" "gray") maze))

#; { [List Posn Posn] Image -> Image }
;; Draw a connection between two posns (the absence of a wall)
(define (draw-edge edge bg)
  (define pos1 (maze-posn->px-posn (first edge)))
  (define pos2 (maze-posn->px-posn (second edge)))
  (add-line bg
            (posn-x pos1)
            (posn-y pos1)
            (posn-x pos2)
            (posn-y pos2)
            (make-pen "white" PATH-THICKNESS "solid" "round" "round")))

#; { Posn -> Posn }
;; Convert a posn in maze-space to pixel space
(define (maze-posn->px-posn pos)
  (make-posn (* (posn-x pos) (/ PX-WIDTH WIDTH))
             (* (posn-y pos) (/ PX-HEIGHT HEIGHT))))

(module+ test
  (check-equal? (maze-posn->px-posn (make-posn 0 0)) (make-posn 0 0))
  (check-equal? (maze-posn->px-posn (make-posn WIDTH HEIGHT)) (make-posn PX-WIDTH PX-HEIGHT)))

(big-bang 0
  [on-tick add1]
  [to-draw draw-world])

