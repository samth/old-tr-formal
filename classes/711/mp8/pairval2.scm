;;; mutable-pairs/pairval2.scm

(let ((time-stamp "Time-stamp: <2003-10-05 12:55:57 wand>"))
  (eopl:printf
    "mutable-pairs/pairval2.scm ~a~%"
    (substring time-stamp 13 29)))

(define pairval? location?)

;; produce (start start+1 ... start+number)
(define iota2
  (lambda (start number)
    (if (zero? number)
      '()
      (cons start (iota2 (+ start 1) (- number 1))))))

(define new-pair
  (lambda (val1 val2 store rcvr)
    (let* ((new-locs (iota2 (next-location store) 2))
           (new-store
             (adjoin-many-to-store store (list val1 val2))))
      (rcvr (car new-locs) new-store))))

(define left
  (lambda (p store)
    (deref store p)))

(define setleft
  (lambda (p val store)
    (setref store p val)))

(define right
  (lambda (p store)
    (deref store (+ p 1))))

(define setright
  (lambda (p val store)
    (setref store (+ p 1) val)))


