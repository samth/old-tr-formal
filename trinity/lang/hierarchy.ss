;; Macro/module ickiness:
;;
;;     All occurrences of provide/contract have to be wrapped in the context
;;     of the struct name being provided, since this module is generating the
;;     provide/struct expression.

(module hierarchy mzscheme
  (require (lib "contract.ss"))

  ;; TODO: comment with the things I told Ryan about
  ;; TODO: add identifier? checks where needed

  (define-syntax define-struct-hierarchy
    (syntax-rules ()
      [(_ ((name parent) ((field contract) ...) sub ...))
       (begin
         ;; Define the root struct type.
         (define-struct name (field ...))
         ;; Define all descendant struct types.
         (define-struct-hierarchy/child name sub) ...
         ;; Provide everything.
         (provide-struct-hierarchy (name ((field contract) ...) sub ...)))]
      [(_ (name ((field contract) ...) sub ...))
       (begin
         ;; Define the root struct type.
         (define-struct name (field ...))
         ;; Define all descendant struct types.
         (define-struct-hierarchy/child name sub) ...
         ;; Provide everything.
         (provide-struct-hierarchy (name ((field contract) ...) sub ...)))]))

  (define-syntax define-struct-hierarchy/child
    (syntax-rules ()
      [(_ parent (name ((field contract) ...) sub ...))
       (begin
         (define-struct (name parent) (field ...))
         (define-struct-hierarchy/child name sub) ...)]))

  (define-syntax (provide-struct-hierarchy stx)
    (define (use-context ctxt-stx src-stx)
      (datum->syntax-object ctxt-stx (syntax-object->datum src-stx)))
    (syntax-case stx ()
      [(_ (name ((field contract) ...)
            (subname ((subfield subcontract) ...) subsub ...)
            ...))
       (with-syntax ([parent-contracts #'(contract ...)])
         #`(begin
             ;; Provide the root struct type.
             #,(use-context #'name #'(provide/contract (struct name ((field contract) ...))))
             ;; Provide all the descendant struct types.
             (provide-struct-hierarchy/child (subname parent-contracts ((subfield subcontract) ...) subsub ...))
             ...
             ))]))

  (define-syntax (provide-struct-hierarchy/child stx)

    (define (use-context ctxt-stx src-stx)
      (datum->syntax-object ctxt-stx (syntax-object->datum src-stx)))
    (define sym syntax-object->datum)
    (define (make-name name)
      (datum->syntax-object stx (string->symbol name)))
    (define (make-predicate-name type)
      (make-name (format "~a?" (sym type))))
    (define (make-struct-name type)
      (make-name (format "struct:~a" (sym type))))
    (define (make-constructor-name type)
      (make-name (format "make-~a" (sym type))))
    (define (make-selector-name type field)
      (make-name (format "~a-~a" (sym type) (sym field))))
    (define (make-mutator-name type field)
      (make-name (format "set-~a-~a!" (sym type) (sym field))))

    (syntax-case stx ()
      [(_ (type (parent-contract ...) ((field contract) ...) sub ...))
       (with-syntax ([predicate (make-predicate-name #'type)]
                     [struct (make-struct-name #'type)])
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
           #`(begin
               #,(use-context #'type #'(provide struct type))
               #,(use-context #'type #'(provide/contract (predicate (any/c . -> . boolean?))))
               #,(use-context #'type #'(provide/contract (constructor (parent-contract ... contract ... . -> . predicate))))
               #,@(use-context #'type #'((provide/contract (selector selector-contract)) ...))
               #,@(use-context #'type #'((provide/contract (mutator mutator-contract)) ...))
               (provide-struct-hierarchy/child sub*) ...)))]))

  ;; TODO: what module should `optional' go in?

  ;; optional : flat-contract -> flat-contract
  ;; converts to a flat-contract that also recognizes #f
  (define (optional c)
    (union c false/c))

  (provide define-struct-hierarchy optional))
