;; =============================================================================
;;
;; macro-object.ss - by Dave Herman
;; version 1, 2004-05-08
;;
;; A library for attaching elaboration-time values to syntax transformers. A
;; macro-object is a structure with a field containing an elaboration-time value
;; but that can also be used as a syntax transformer.
;;
;; =============================================================================

(module macro-object mzscheme

  ;; A macro-object is a structure with two fields:
  ;;   - macro-object-value : an arbitrary piece of data
  ;;   - macro-object-transformer : a syntax transformer
  (define-values (struct:macro-object
                  make-macro-object
                  macro-object?
                  macro-object-ref
                  macro-object-set!)
    (make-struct-type 'macro-object #f 2 0 #f null (current-inspector) 1))

  ;; macro-object-value : (union macro-object syntax) -> any
  ;; selects the data associated with a macro-object
  (define macro-object-value
    (let ([ref (make-struct-field-accessor macro-object-ref 0 'value)])
      (lambda (x)
        (cond
          [(macro-object? x) (ref x)]
          [(syntax? x) (ref (syntax-local-value x))]
          [else (raise-type-error 'macro-object-value
                                  "macro-object or syntax object"
                                  x)]))))

  ;; macro-object-transformer : macro-object -> (syntax -> syntax)
  ;; selects the syntax transformer from a macro-object
  (define macro-object-transformer
    (make-struct-field-accessor macro-object-ref 1 'transformer))

  (provide make-macro-object macro-object?
           macro-object-value macro-object-transformer))