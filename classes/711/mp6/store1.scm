;;; explicit-store/store1.scm

(let ((time-stamp "Time-stamp: <2003-10-05 12:04:33 wand>"))
  (eopl:printf
    "explicit-store/store1.scm: really stupid store model ~a~%"
    (substring time-stamp 13 29)))

;;;;;;;;;;;;;;;; references and the store ;;;;;;;;;;;;;;;;

;;; world's stupidest model of the store

;; the store will be a list of expvals.
;; locations will be integers (offsets in the list)
;; the contents of location N will (list-ref store N)
;; the (length store) serves as a free-location counter (!)


(define location? number?)

(define empty-store
  (lambda () '()))

(define next-location
  (lambda (store)
    (length store)))

(define adjoin-to-store                 ; YUCK!
  (lambda (store val)
    (append store (list val))))

(define deref 
  (lambda (store loc)
    (if (location? loc)
        (list-ref store loc)
        (error-val))))

(define setref                          ; YUCK!
  (lambda (store0 loc0 val)
    (let recur ((store store0) (loc loc0))
      (cond
        ((null? store)
         (error:eopl 'setref
           "illegal reference ~s in store ~s"
           loc0 store0))
        ((zero? loc)
         (cons val (cdr store)))
        (else
          (cons
            (car store)
            (recur (cdr store) (- loc 1))))))))

(define adjoin-many-to-store
  (lambda (store vals)
    (append store vals)))