;;; explicit-store/store1.scm

(let ((time-stamp "Time-stamp: <2003-10-27 08:12:35 wand>"))
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

(define adjoin-many-to-store append)

(define deref 
  (lambda (store loc)
    (list-ref store loc)))

;; store x loc x val -> store
(define setref                          ; YUCK!
  (lambda (store0 loc0 val)
    (let recur ((store store0) (loc loc0))
      (cond
        ((null? store)
         (eopl:error 'setref
           "illegal reference ~s in store ~s"
           loc0 store0))
        ((zero? loc)
         (cons val (cdr store)))
        (else
          (cons
            (car store)
            (recur (cdr store) (- loc 1))))))))
