;;; threads/runtime.scm

(let ((time-stamp "Time-stamp: <2003-10-25 10:22:55 wand>"))
  (eopl:printf
    "threads/runtime.scm ~a~%"
    (substring time-stamp 13 29)))

;;; runtime system for machine with output and threads.
;;; Currently depends on store1.scm, but just for setting up initial
;;; store. 

;;;;;;;;;;;;;;;; global tables in the store ;;;;;;;;;;;;;;;;

(define timer-location       0)
(define rq-location          1)
(define current-tid-location 2)
(define next-tid-location    3)
(define output-location      4)
(define final-answer-location 5)

(define *the-quantum* 20)

;; this uses store1.scm !!

(define initial-store
  (lambda () (list
               *the-quantum*            ; initial timer
               '()                      ; initial ready queue
               0                        ; initial process is tid 0
               1                        ; initial free tid counter
               '()                      ; initial std output
               #f                       ; reserved for final answer
)))


                  

(define store-get-timer
  (lambda (store)
    (deref store timer-location)))

(define store-decrement-timer
  (lambda (store)
    (setref store timer-location
      (- (deref store timer-location) 1))))

(define store-reset-timer
  (lambda (store) (setref store timer-location *the-quantum*)))

(define store-get-queue
  (lambda (store) (deref store rq-location)))

(define store-set-queue
  (lambda (q1 store) (setref store rq-location q1)))

(define store-enqueue-thread
  (lambda (store thrd)
    (let ((rq (deref store rq-location)))
      (setref store rq-location
        (queue-enqueue rq thrd)))))

(define store-get-tid
  (lambda (store) (deref store current-tid-location)))

(define store-set-tid
  (lambda (tid store) (setref store current-tid-location tid)))

(define store-allocate-tid
  (lambda (store callback)
    (let ((next-tid (deref store next-tid-location)))
      (callback next-tid
        (setref store next-tid-location (+ next-tid 1))))))

(define store-get-final-answer
  (lambda (store)
    (deref store final-answer-location)))

(define store-set-final-answer
  (lambda (store val)
    (setref store final-answer-location val)))

(define store-initialize-stdout
  (lambda (store)
    (setref store output-location '())))

(define store-append-to-stdout
  (lambda (vals store)
    (setref store output-location
      (append (deref store output-location) vals))))


;;;;;;;;;;;;;;;; queues ;;;;;;;;;;;;;;;;

;; We maintain the queue by adding to the end and dequeuing from the
;; front. 

(define queue-empty? null?)

(define queue-enqueue
  (lambda (q val)
    (append q (list val))))

(define queue-dequeue
  (lambda (q callback)
    (callback (car q) (cdr q))))
