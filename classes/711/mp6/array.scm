(define arrayval? location?)

(define (new-array l store rcvr)
  (let* ((new-loc (next-location store))
         (new-store
          (adjoin-to-store store (make-vector l (num-val 0)))))
    (rcvr new-loc new-store)))

(define (arrayref arr l store)
  (vector-ref (deref store arr) l))

(define (arrayset arr l v store)
  (begin (vector-set! (deref store arr) l v)
         store))