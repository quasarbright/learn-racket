;; how many times do you have to watch a movie to have really seen all of it?
;; if you blink, you miss stuff!
#lang racket

(struct interval (start end) #:transparent)


; https://www.ncbi.nlm.nih.gov/pmc/articles/PMC4043155/pdf/rsif20130227.pdf
(define blink-duration .058)
; https://www.healthline.com/health/how-many-times-do-you-blink-a-day#blinking-frequency
(define blink-period-min 3)
(define blink-period-max 6)
(define movie-length (* 60 120))

; returns intervals of time with eyes closed
(define (movie-intervals)
  (reverse (let loop ([time 0] [intervals '()])
             (cond
               [(>= time movie-length) intervals]
               [else
                (define open-time (+ blink-period-min (* blink-period-max (random))))
                (cond
                  [(> (+ time open-time blink-duration) movie-length) intervals]
                  [else
                   ; eyes open then blink
                   (define blink (interval (+ time open-time) (+ time open-time blink-duration)))
                   (loop (+ time open-time blink-duration) (cons blink intervals))])]))))

;; [[interval]] -> interval | #f
;; is there any interval of time across all viewings where the viewer has their eyes closed?
;; If there is, return an interval where the viewer's eyes were closed throughout all viewings
(define (has-dark-time? viewings)
  (define all-blinks (apply append viewings))
  (define key-times (map interval-start all-blinks))
  (for/or ([time key-times]) ; any time where eyes always closed?
    (for/and ([blinks viewings]) ; all blinks have a blink containing the time?
      (for/or ([blink blinks]) ; any blink contains the time?
        (and (interval-contains-time? blink time)
             (intersect-intervals (filter (λ (i) (interval-contains-time? i time)) all-blinks)))))))

(define (interval-contains-time? i time)
  (<= (interval-start i) time (interval-end i)))

;; [interval] -> interval | #f
;; find the intersection of all intervals if one exists
(define (intersect-intervals intervals)
  (define max-start (apply max (map interval-start intervals)))
  (define min-end (apply min (map interval-end intervals)))
  (and (< max-start min-end) (interval max-start min-end)))

(define (how-many-viewings-to-see-all)
  (let loop ([viewings (list (movie-intervals))])
    (if (has-dark-time? viewings)
        (loop (cons (movie-intervals) viewings))
        (length viewings))))

(define (how-many-viewings-to-see-all-avg [n 50])
  (mean (build-list n (thunk* (how-many-viewings-to-see-all)))))

(define (mean numbers) (/ (foldl + 0 numbers) (length numbers)))