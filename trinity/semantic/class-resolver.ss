#cs(module class-resolver mzscheme
  (require (lib "string.ss" "srfi" "13"))
  (require (lib "class.ss"))
  (require (lib "contract.ss"))
  (require "../lang/struct.ss")

  (define class-resolver<%>
    (interface ()
      resolve-package
      resolve-type))
  

  (define current-class-resolver
    (make-parameter #f (lambda (new-resolver)
                         (unless (is-a? new-resolver class-resolver<%>)
                           (raise-type-error 'current-class-resolver
                                             "class-resolver<%>"
                                             new-resolver))
                         new-resolver)))

  (with-public-inspector
   (define-struct type-name (package type))
   (provide/contract (struct type-name ((package (listof symbol?))
                                        (type symbol?)))))

  ;; build-type-name : (listof symbol) -> type-name
  (define (build-type-name name)
    (let ([rev (reverse name)])
      (make-type-name (reverse (cdr rev))
                      (car rev))))
  (provide/contract (build-type-name ((listof symbol?) . -> . type-name?)))

  (define (type-name->string name)
    (string-append
     (string-join (map symbol->string (type-name-package name)) "." 'suffix)
     (symbol->string (type-name-type name))))
  (provide/contract (type-name->string (type-name? . -> . string?)))

  ;; TODO: I can't give these contracts because of cyclic module dependencies!

  ;; lookup-package : (listof symbol) -> package%
  (define (lookup-package name)
    (send (current-class-resolver) resolve-package name))

  ;; lookup-type : type-name -> type<%>
  (define (lookup-type name)
    ;(printf "lookup-type: ~a~n" (type-name->string name))
    (send (current-class-resolver) resolve-type name))

  (provide current-class-resolver class-resolver<%> lookup-package lookup-type))
