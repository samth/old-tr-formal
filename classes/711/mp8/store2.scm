;;; explicit-store/store2.scm

(let ((time-stamp "Time-stamp: <2003-10-04 19:16:42 wand>"))
  (eopl:printf
    "explicit-store/store2.scm: store as a Scheme vector ~a~%"
    (substring time-stamp 13 29)))

;;;;;;;;;;;;;;;; references and the store ;;;;;;;;;;;;;;;;

;; modelling the store using Scheme's mutable vectors
;; the store is "ephemeral": it uses destructive update

;; the store will be a Scheme vector
;; locations will be integers (indices into the vector)
;; the contents of location N will (vector-ref store N)
;; index 0 serves as a free-location counter

(define location? number?)

(define empty-store
  (lambda ()
    (let ((store (make-vector 100)))    ; this should be a parameter
      (vector-set! store 0 1)           ; first free location is 1
      store)))

; returns the next free location without allocating it
(define next-location                   
  (lambda (store) 
    (vector-ref store 0)))

;; allocates the next free location and initializes it
(define adjoin-to-store                 
  (lambda (store val)
    (let ((fp (vector-ref store 0)))
      (vector-set! store fp val)
      (vector-set! store 0 (+ fp 1))
      store)))

(define deref 
  (lambda (store loc)
    (if (location? loc)
        (vector-ref store loc)
        (error-val))))

(define setref                          
  (lambda (store0 loc0 val)
    (vector-set! store0 loc0 val)
    store0))

;; adjoin the vals to the store in left-to-right order
(define adjoin-many-to-store
  (lambda (store vals)
    (if (null? vals)
      store
      (adjoin-many-to-store
        (adjoin-to-store store (car vals))
        (cdr vals)))))
