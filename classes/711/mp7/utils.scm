(let ((time-stamp "Time-stamp: <2003-10-25 10:19:21 wand>"))
  (eopl:printf "threads/utils.scm ~a~%"
    (substring time-stamp 13 29)))

;;;;;;;;;;;;;;;; utils for environments;;;;;;;;;;;;;;;;

(define list-find-position
  (lambda (sym los)
    (list-index (lambda (sym1) (eqv? sym1 sym)) los)))

(define list-index
  (lambda (pred ls)
    (cond
      ((null? ls) #f)
      ((pred (car ls)) 0)
      (else (let ((list-index-r (list-index pred (cdr ls))))
              (if (number? list-index-r)
                (+ list-index-r 1)
                #f))))))

;; produce (start start+1 ... start+number)
(define iota2
  (lambda (start number)
    (if (zero? number)
      '()
      (cons start (iota2 (+ start 1) (- number 1))))))