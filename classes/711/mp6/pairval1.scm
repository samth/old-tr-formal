;;; mutable-pairs/pairval1.scm

(let ((time-stamp "Time-stamp: <2003-10-05 12:04:54 wand>"))
  (eopl:printf
    "mutable-pairs/pairval1.scm ~a~%"
    (substring time-stamp 13 29)))

(define-datatype pairval pairval?
  (a-pair
    (left  location?)
    (right location?)))

(define new-pair
  (lambda (val1 val2 store rcvr)
    (let* ((new-locs (iota2 (next-location store) 2))
           (new-store
             (adjoin-many-to-store store (list val1 val2))))
      (rcvr
        (a-pair (car new-locs) (cadr new-locs))
        new-store))))

(define left
  (lambda (p store)
    (cases pairval p
      (a-pair (left right)
        (deref store left)))))

(define setleft
  (lambda (p val store)
    (cases pairval p
      (a-pair (left right)
        (setref store left val)))))

(define right
  (lambda (p store)
    (cases pairval p
      (a-pair (left right)
        (deref store right)))))

(define setright
  (lambda (p val store)
    (cases pairval p
      (a-pair (left right)
        (setref store right val)))))


