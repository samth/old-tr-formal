(module m mzscheme
  (require (lib "contract.ss"))
  (define-struct parent (foo))
  (define-struct (child parent) (bar))
  (define-struct (grand child) (baz))

;  (define-syntax provide-struct-hierarchy/child
;    (syntax-rules ()
;      [(provide-struct-hierarchy/child (name ((field contract) ...) sub ...))
;       (begin
;         (provide/contract (struct name ((field contract) ...)))
;         (provide-struct-hierarchy/child sub) ...)]))

  (define-syntax (provide-struct-hierarchy/child stx)

    (define sym syntax-object->datum)
    (define (make-name name)
      (datum->syntax-object stx (string->symbol name)))
    (define (make-predicate-name type)
      (make-name (format "~a?" (sym type))))
    (define (make-constructor-name type)
      (make-name (format "make-~a" (sym type))))
    (define (make-selector-name type field)
      (make-name (format "~a-~a" (sym type) (sym field))))
    (define (make-mutator-name type field)
      (make-name (format "set-~a-~a!" (sym type) (sym field))))

    (syntax-case stx ()
      [(_ (type (parent-contract ...) ((field contract) ...) sub ...))
       (with-syntax ([predicate (make-predicate-name #'type)])
         (with-syntax ([constructor
                        (make-constructor-name #'type)]
                       [((selector selector-contract) ...)
                        (map (lambda (field contract)
                               #`(#,(make-selector-name #'type field) (predicate . -> . #,contract)))
                             (syntax->list #'(field ...))
                             (syntax->list #'(contract ...)))]
                       [((mutator mutator-contract) ...)
                        (map (lambda (field contract)
                               #`(#,(make-mutator-name #'type field) (predicate #,contract . -> . any/c)))
                             (syntax->list #'(field ...))
                             (syntax->list #'(contract ...)))]
                       [(sub* ...)
                        (map (lambda (sub)
                               (syntax-case sub ()
                                 [(sub-type etc ...)
                                  #'(sub-type (parent-contract ... contract ...) etc ...)]))
                             (syntax->list #'(sub ...)))])
           #'(begin
               (provide/contract (predicate (any/c . -> . boolean?)))
               (provide/contract (selector selector-contract)) ...
               (provide/contract (mutator mutator-contract)) ...
               (provide/contract (constructor (parent-contract ... contract ... . -> . predicate)))
               (provide-struct-hierarchy/child sub*) ...)))]))

  (define-syntax (provide-struct-hierarchy stx)
    (syntax-case stx ()
      [(_ (name ((field contract) ...)
            (subname ((subfield subcontract) ...) subsub ...)
            ...))
       (with-syntax ([parent-contracts #'(contract ...)])
         #`(begin
             (provide-struct-hierarchy/child (subname parent-contracts ((subfield subcontract) ...) subsub ...))
             ...))]))

  (provide/contract (struct parent ((foo integer?))))
  (provide-struct-hierarchy (parent ((foo integer?))
                              (child ((bar string?))
                                (grand ((baz boolean?))))))

  )
