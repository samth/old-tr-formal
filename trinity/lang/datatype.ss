;; =============================================================================
;;
;; datatype.ss - by Dave Herman
;; version 2, 2004-05-14
;;
;; An implementation of algebraic datatypes that work with the contract system,
;; somewhat similar to the define-datatype construct from EoPL. Currently these
;; can only be attached to contracts at module boundaries, due to the setup of
;; the contract system.
;;
;; I'm not entirely satisfied with this. Eventually I'd like to be able to
;; define a datatype with its contracts in one place, while still allowing for
;; datatypes with mutually recursive contracts.
;;
;; =============================================================================

;; TODO: eliminate unnecessary parens from (provide-datatype/contract)

(module datatype mzscheme
  (require (lib "contract.ss"))
  (require "struct.ss")
  (require-for-syntax "macro-object.ss")

  (define-syntax (define-datatype stx)
    (syntax-case stx ()
      [(_ type [variant (field ...)] ...)
       (with-syntax ([variants #'([variant (field ...)] ...)])
         (let* ([type-name (syntax-object->datum #'type)]
                [datatype:type-name (string->symbol (format "datatype:~a" type-name))]
                [field-names (map (lambda (x)
                                    (syntax-case x ()
                                      [(v (f ...))
                                       #'(v f ...)]))
                                  (syntax->list #'variants))])
           #`(begin
               (define-syntax #,(datum->syntax-object stx datatype:type-name)
                 (make-macro-object
                  '#,field-names
                  (lambda (x)
                    (syntax-case x ()
                      [id
                       (identifier? #'id)
                       'no-datatype-information-implemented-yet]))))
               (with-public-inspector
                (define-struct type ())
                (define-struct (variant type) (field ...))
                ...))))]))

  (define-syntax (provide-datatype/contract stx)
    (syntax-case stx ()
      [(_ type [variant (contract ...)] ...)
       (let* ([type-name (syntax-object->datum #'type)]
              [datatype:type-name (string->symbol (format "datatype:~a" type-name))]
              [variants (macro-object-value
                         (datum->syntax-object stx datatype:type-name))]
              [formals (map car variants)]
              [actuals (map syntax-object->datum (syntax->list #'(variant ...)))]
              [field-names (map (lambda (v)
                                  (map (lambda (contract)
                                         (datum->syntax-object stx contract))
                                       (cdr v)))
                                variants)])
         (unless (and (= (length formals) (length actuals))
                      (andmap (lambda (x) (memq x formals))
                              actuals))
           (raise-syntax-error
            'provide-datatype/contract
            (format "variants do not match definition of ~a; expected ~v"
                    type-name
                    formals)
            stx))
         (let ([clauses (map (lambda (clause names)
                               (syntax-case clause ()
                                 [(v (c ...))
                                  (let ([pairs (map (lambda (name contract)
                                                      #`(#,name #,contract))
                                                    names
                                                    (syntax->list #'(c ...)))])
                                    #`(provide-struct/contract v #,pairs))]))
                             (syntax->list #'([variant (contract ...)] ...))
                             field-names)])
           #`(begin
               (provide (struct type ()))
               #,@clauses)))]))

  (define-syntax (provide-datatype stx)
    (syntax-case stx ()
      [(_ type)
       (let* ([type-name (syntax-object->datum #'type)]
              [datatype:type-name (string->symbol (format "datatype:~a" type-name))]
              [variants (macro-object-value
                         (datum->syntax-object stx datatype:type-name))]
              [clauses (map (lambda (variant)
                              (let ([variant-name (car variant)]
                                    [field-names (cdr variant)])
                                #`(struct #,variant-name #,field-names)))
                            variants)])
         #`(provide (struct type ())
                    #,@clauses))]))

  (define-syntax (provide-struct/contract stx)
    (syntax-case stx ()
      [(_ struct-name ([field fc] ...))
       (datum->syntax-object
        #'struct-name
        (syntax-e #'(provide/contract (struct struct-name ([field fc] ...)))))]))
  
;  (define-syntax (provide-datatype stx)
;    (syntax-case stx ()
;      [(_ type
;         [variant ([field field-contract] ...)]
;         ...)
;       #`(begin
;           (define-struct type ())
;           (define-struct (variant type) (field ...))
;           ...
;           (provide (struct type ()))
;           #,(datum->syntax-object
;              #'type
;              (syntax-e
;               #'(provide/contract
;                  (struct variant ([field field-contract] ...))
;                  ...))))]))

;  (define-syntax (provide-datatypes stx)
;    (syntax-case stx ()
;      [(_ [type [variant ([field field-contract] ...)]
;                ...]
;          ...)
;       #`(begin
;           (begin
;             (define-struct type ())
;             (define-struct (variant type) (field ...))
;             ...)
;           ...
;           (begin
;             (provide (struct type ()) ...)
;             (provide-struct/contract variant ([field field-contract] ...))
;             ... ...))]))

  (provide define-datatype provide-datatype provide-datatype/contract))
