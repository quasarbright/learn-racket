#lang racket

; A DSL for working with timesheets.

(module+ test (require rackunit))
(provide
 ; timesheet interface

 ; files

 ; path -> void
 ; load a timesheet from a file
 load-timesheet!
 ; path -> void
 ; save the current timesheet to a file
 save-timesheet!
 ; string -> path
 ; like (home-path "foo.txt") for "~/foo.txt"
 home-path

 ; timesheet operations

 ; -> void
 ; create an empty timesheet
 create-timesheet!
 ; date? [string?] -> void
 ; clock in at that time, with optional description
 clock-in!
 ; date? [string?] -> void
 ; clock out at that time, with optional description
 clock-out!
 ; date? natural? [string?] -> void
 ; add a duration of work with no start or end, with optional description.
 ; recommended to use date utilities like (today) which clear the date's time.
 ; time is in seconds. recmmended to use time utilities like (hours 2)
 add-period!
 ; date? date? -> number?
 ; how many hours in between the two dates
 hours-between
 ; -> number?
 ; total hours in the whole timesheet
 total-hours
 ; -> void
 print-timesheet

 ; date/time utilities

 ; -> date?
 now
 ; natural? -> natural?
 ; (seconds n) gives the number of seconds in n seconds (identity function)
 seconds
 ; natural? -> natural?
 ; (minutes n) gives the number of seconds in n minutes
 minutes
 ; natural? -> natural?
 ; (minutes n) gives the number of seconds in n hours
 hours
 ; natural? -> date?
 ; cleared time
 days-ago
 ; natural? -> date?
 ; (time-ago n) is n seconds ago
 time-ago
 ; date?
 ; cleared time
 today
 ; date?
 ; cleared time
 yesterday
 ; date?
 ; cleared time
 tomorrow
 ; date? natural? -> date?
 ; subtracts seconds from date
 -/date
 ; date? natural? -> date?
 ; adds seconds to date
 +/date)
(require racket/date
         racket/serialize
         racket/pretty)

; helper functions for maintaining a timesheet in a repl user interface

; user actions:
; P0
; - clock in (at a time, default to now)
;   - with description
; - clock out (at a time, default to now)
;   - with description
; - log some amount of time for a given date, like 3 hours on september 1st 2024, default to today
;   - with description
; - how many hours logged total
; - are you clocked in?
; P1
; - some way of specifying you've been paid for your time?
;   - you work in hours but get paid in dollars. the conversion rate is not necessarily constant. how should this be managed?
;   - each interval/period has an hourly rate associated with it
;   - the timesheet has a current hourly rate that used as the default when logging work
;   - no need to mark a particular interval/period as paid for. just total money vs sum(hours * rate)
;   - track when you got paid how much? yeah, log payments by day like periods. no need to track total paid directly.
;   - UI:
;     - (unpaid-hours) how many hours of work you haven't been paid for
;     - (money-owed) returns how much money you are owed
;     - (hourly-rate) returns current hourly rate
;     - (set-hourly-rate! rate) obvious
;     - (add-payment! amount [description])
;     - new optional kwarg on clock-in, clock-out, and add-period: rate. defaults to current rate. Ex: (clock-in! (now) #:rate 40)
;    - what if no hourly rate is set?
;      - default to zero?
;      - add an operation to retroactively put rate?
;      - print a warning?
;      - don't worry about it until you run into that use-case. for now, default to zero without warning.
;    - if start and end have different rates, use the end's rate.

; can only have one clock-in at a time

(module+ main
  (create-timesheet!)
  (add-period! (yesterday) (hours 1) "dilly dallying")
  (clock-in! (time-ago (hours 2)) "started working")
  (clock-out! (now) "done working")
  (hours-between (yesterday) (now))
  (save-timesheet! "research.hours")
  (load-timesheet! "research.hours")
  (print-timesheet))

; data definitions

; a Timesheet is a
(struct timesheet [intervals periods payments rate clock-in] #:prefab)
; intervals is a (listof Interval)
; periods is a (listof Period)
; payments is a (listof Payment)
; rate is a Real representing $/hr for work.
; clockin is a (or/c #f Event)

; an Interval is a
(struct interval [start end] #:prefab)
; start and end are Events

; an Event is a
(struct event [date description rate] #:prefab)
; date is a date?
; description is a (or/c #f string?)
; rate is a Real in $/hr

; a Period is a
(struct period [date duration description rate] #:prefab)
; date is a date?. the time is not necessarily accurate
; duration is an integer representing seconds
; description is a (or/c #f string?)
; rate is a Real in $/hr

; A Payment is a
(struct payment [date description amount] #:prefab)
; date is a date? the time is not necessarily accurate
; description is a (or/c #f string?)
; amount is a Real in $

; timesheet operations

(define empty-timesheet (timesheet (list) (list) (list) 0 #f))

; Timesheet date? (or/c #f string?) -> Timesheet
(define (timesheet-do-clock-in sheet dat [description #f] #:rate [rate #f])
  (when (timesheet-clock-in sheet)
    (raise-user-error "already clocked in"))
  (struct-copy timesheet sheet [clock-in (event dat description (or rate (timesheet-rate sheet)))]))

(module+ test
  (test-case "clock-in"
    (define dat (current-date))
    (check-equal? (timesheet-do-clock-in empty-timesheet dat "working")
                  (timesheet (list) (list) (list) 0 (event dat "working" 0)))
    (check-exn
     #rx"already clocked in"
     (lambda ()
       (timesheet-do-clock-in (timesheet (list) (list) (list) 0 (event dat #f 0)) dat)))))

; Timesheet date? (or/c #f string?) -> Timesheet
(define (timesheet-do-clock-out sheet dat [description #f] #:rate [rate #f])
  (unless (timesheet-clock-in sheet)
    (raise-user-error "not clocked in"))
  (struct-copy timesheet sheet
               [clock-in #f]
               [intervals (cons (interval (timesheet-clock-in sheet) (event dat description (or rate (timesheet-rate sheet))))
                                (timesheet-intervals sheet))]))

(module+ test
  (test-case "clock-out"
    (define dat1 (current-date))
    (define dat2 (current-date))
    (define clocked-in (timesheet-do-clock-in empty-timesheet dat1 "working"))
    (define clocked-out (timesheet-do-clock-out clocked-in dat2))
    (check-equal? (timesheet-intervals clocked-out) (list (interval (event dat1 "working" 0) (event dat2 #f 0))))
    (check-equal? (timesheet-clock-in clocked-out) #f)))

; Timesheet date? natural? (or/c #f string/) -> Timesheet
; duration in seconds
(define (timesheet-add-period sheet dat duration [description #f] #:rate [rate #f])
  (struct-copy timesheet sheet
               [periods (cons (period dat duration description (or rate (timesheet-rate sheet)))
                              (timesheet-periods sheet))]))

(define SECONDS_PER_HOUR (* 60 60))

; Timesheet date? date? -> number?
(define (timesheet-hours-between sheet start end)
  (timesheet-total-hours (timesheet-select-between sheet start end)))

; Timesheet -> natural?
; excludes time related to clockin
(define (timesheet-total-hours sheet)
  (/ (+ (for/sum ([int (timesheet-intervals sheet)])
          (match int
            [(interval (event start _ _) (event end _ _))
             (- (date->seconds end)
                (date->seconds start))]))
        (for/sum ([prd (timesheet-periods sheet)])
          (period-duration prd)))
     SECONDS_PER_HOUR))

; Timesheet date? date? -> Timesheet
; selects intervals and periods that are fully contained between start and end.
; range is inclusive.
; erases clockin.
(define (timesheet-select-between sheet start end)
  (match sheet
    [(timesheet ints prds payments rate _)
     (define ints^
       (filter (lambda (int)
                 (and (date<=? start (event-date (interval-start int)))
                      (date<=? (event-date (interval-end int)) end)))
               ints))
     (define prds^
       (filter (lambda (prd)
                 (and (date<=? start (period-date prd))
                      (date<=? (period-date prd) end)))
               prds))
     (define payments^
       (filter (lambda (pmt)
                 (and (date<=? start (payment-date pmt))
                      (date<=? (payment-date pmt) end)))
               payments))
     (timesheet ints^ prds^ payments^ rate #f)]))

; date? date? -> boolean?
(define (date<=? d1 d2)
  (<= (date->seconds d1)
      (date->seconds d2)))

; date utilities

(define (now) (current-date))
(define (seconds n) n)
(define (minutes n) (* n 60))
(define (hours n) (* n 60 60))
(define SECONDS_PER_DAY (* SECONDS_PER_HOUR 24))
; with time cleared
(define (days-ago n) (-/date (today) (* n SECONDS_PER_DAY)))
(define (time-ago seconds) (-/date (now) seconds))
; with time cleared
(define (today) (clear-time (now)))
; with time cleared
(define (yesterday) (days-ago 1))
(define (tomorrow) (days-ago -1))
; sets seconds, minutes, hours to zero
(define (clear-time d) (struct-copy date (now) [second 0] [minute 0] [hour 0]))
(define (-/date dat change-in-seconds) (+/date dat (- change-in-seconds)))
(define (+/date dat change-in-seconds)
  (seconds->date (+ (date->seconds dat) change-in-seconds)))
(define (mdy month day year) (seconds->date (find-seconds 0 0 0 day month year)))

; user timesheet operations

(define current-timesheet (make-parameter #f))
(define (assert-current-timesheet!)
  (unless (current-timesheet)
    (raise-user-error "no timesheet active!")))
(define (create-timesheet!)
  (current-timesheet empty-timesheet))

; files

(define (load-timesheet! path)
  (define prt (open-input-file path))
  (read-timesheet! prt)
  (close-input-port prt))
(define (read-timesheet! prt)
  (current-timesheet (deserialize (read prt))))
(define (save-timesheet! path)
  (define prt (open-output-file path #:exists 'replace))
  (write-timesheet! prt)
  (close-output-port prt))
(define (write-timesheet! prt)
  (assert-current-timesheet!)
  (writeln (serialize (current-timesheet)) prt))
; like (home-path "Documents/file.txt")
(define (home-path str)
  (build-path (find-system-path 'home-dir) str))

; parameterized operations

(define (clock-in! dat [description #f] #:rate [rate #f])
  (assert-current-timesheet!)
  (current-timesheet (timesheet-do-clock-in (current-timesheet) dat description #:rate rate)))

(define (clock-out! dat [description #f] #:rate [rate #f])
  (assert-current-timesheet!)
  (current-timesheet (timesheet-do-clock-out (current-timesheet) dat description #:rate rate)))

(define (add-period! dat duration [description #f] #:rate [rate #f])
  (assert-current-timesheet!)
  (current-timesheet (timesheet-add-period (current-timesheet) dat duration description #:rate rate)))

(define (hours-between start end)
  (assert-current-timesheet!)
  (round-to-tenth (timesheet-hours-between (current-timesheet) start end)))

(define (total-hours)
  (timesheet-total-hours (current-timesheet)))

(define (print-timesheet)
  (pretty-print (timesheet->datum (current-timesheet))))

(define (timesheet->datum sheet)
  `(timesheet
    (clock-in ,@(if (timesheet-clock-in (current-timesheet))
                    (match (timesheet-clock-in (current-timesheet))
                      [(event dat desc rate)
                       `(,(date->string dat #t) ,desc ,(rate->datum rate))])
                    '(#f)))
    (intervals
     ,@(for/list ([int (timesheet-intervals sheet)])
         (match int
           [(interval (event start desc-start rate-start) (event end desc-end rate-end))
            `(interval [start ,(date->string start #t) ,desc-start ,(rate->datum rate-start)] [end ,(date->string end #t) ,desc-end ,(rate->datum rate-end)])])))
    (periods
     ,@(for/list ([prd (timesheet-periods sheet)])
         (match prd
           [(period dat duration desc rate)
            `(period ,(date->string dat) ,(round-to-tenth (/ duration SECONDS_PER_HOUR)) ,desc ,(rate->datum rate))])))))

(define (rate->datum rate)
  (format "$~a/hr" rate))

(define (round-to-tenth x) (/ (round (* 10 (exact->inexact x))) 10))
