(module lazy mzscheme
  (require (lib "contract.ss"))
  (require "struct.ss")

  (with-public-inspector
   (define-struct thing (value parent children))
   (define-struct unique ()))

  (define-values (struct:lazy make-lazy lazy? lazy-thunk)
    (let-values ([(s:l m-l l? accessor mutator)
                  (make-struct-type 'lazy
                                    #f
                                    1
                                    0
                                    #f
                                    '()
                                    (current-inspector)
                                    0
                                    null)])
      (values s:l m-l l? (lambda (lz) (accessor lz 0)))))

  (define-syntax lazy
    (syntax-rules ()
      [(_ expr)
       (let* ([unit (make-unique)]
              [tmp unit])
         (make-lazy
          (lambda ()
            (when (eq? tmp unit)
              (set! tmp expr))
            tmp)))]))

  (define x
    (letrec ([a-thing (make-thing 0 #f (list (make-thing 1 (lazy a-thing) null)
                                             (make-thing 2 (lazy a-thing) null)
                                             (make-thing 3 (lazy a-thing) null)))])
      a-thing))

  (define (lazy-value lzv)
    (unless (lazy? lzv)
      (raise-type-error 'lazy-value "lazy value" lzv))
    (lzv))

  (provide lazy lazy? lazy-value x))
