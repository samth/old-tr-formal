(module semantic-object mzscheme
  (require (lib "contract.ss"))
  (require (lib "etc.ss"))
  (require "../lang/hierarchy.ss")
  (require "../lang/struct.ss")
  (require (prefix ast: "../syntactic/ast.ss"))

  (define (positive-integer? v)
    (and (integer? v)
         (positive? v)))

  ;; TODO: get Robby to implement a `promiseof' contract constructor
  ;; TODO: define-struct-hierarchy feature: #f contract means private field

  (with-public-inspector
   (define-struct-hierarchy
     (semantic-object ((source (optional ast:ast?)))
       (package ((name (listof symbol?))
                 (types hash-table?) ;; TODO: this should be private
                 (lookup (symbol? . -> . (optional ground-type?)))))
       (type ()
         (ground-type ((package package?)
                       (name symbol?))
           (unknown-type ())
           (primitive-type ())
           (declared-type ((modifiers (listof symbol?))
                           (interfaces (listof interface?))
                           (elements (listof type-element?)))
             (class ((super (optional class?))))
             (interface ())))
         (array-type ((base-type ground-type?)
                      (dimension positive-integer?))))
       (type-element ((name symbol?))
         (field ((modifiers (listof symbol?))
                 (type promise?) ;; TODO: (promiseof type?)
                 (name symbol?)))
         (behavior ((formals (listof promise?)) ;; TODO: (promiseof type?)
                    (exceptions (listof promise?))) ;; TODO: (promiseof declared-type?)
           (method ((name symbol?)
                    (return-type (optional promise?)))) ;; TODO: (promiseof type?)
           (constructor ()))
         (inner-type ((type promise?))))))) ;; TODO: (promiseof declared-type?)

  ;; Treat the primitives as if they were in the default package.
  (define byte    (make-primitive-type #f null 'byte))
  (define char    (make-primitive-type #f null 'char))
  (define double  (make-primitive-type #f null 'double))
  (define float   (make-primitive-type #f null 'float))
  (define int     (make-primitive-type #f null 'int))
  (define long    (make-primitive-type #f null 'long))
  (define short   (make-primitive-type #f null 'short))
  (define boolean (make-primitive-type #f null 'boolean))

  (provide/contract (byte primitive-type?)
                    (char primitive-type?)
                    (double primitive-type?)
                    (float primitive-type?)
                    (int primitive-type?)
                    (long primitive-type?)
                    (short primitive-type?)
                    (boolean primitive-type?))

  ;; increase-type-dimension : type -> array-type
  (define (increase-type-dimension type)
    (if (ground-type? type)
        (make-array-type type 1)
        (make-array-type (array-type-base-type type)
                         (add1 (array-type-dimension type)))))

  (provide/contract (increase-type-dimension (type? . -> . array-type?)))

  (define all-packages (make-hash-table 'equal))

  ;; parse-qualified-name : (listof symbol) -> (cons package symbol)
  (define (parse-qualified-name name)
    (let* ([rev (reverse name)]
           [package-name (reverse (cdr rev))]
           [type-name (car rev)])
      (cons (get-package package-name) type-name)))

  ;; get-type : (listof symbol) -> (optional ground-type)
  (define (get-type name)
    (let* ([key (parse-qualified-name name)]
           [package (car key)]
           [type-name (cdr key)])
      ((package-lookup package) type-name)))

  (provide/contract (get-type ((listof symbol?) . -> . (optional ground-type?))))

  ;; build-package : (listof symbol) -> package
  (define (build-package name)
    (let ([types (make-hash-table)])
      (make-package #f
                    name
                    types
                    (lambda (type-name)
                      (hash-table-get types
                                      type-name
                                      (lambda () #f))))))

  ;; get-package : (listof symbol) -> package
  (define (get-package name)
    (hash-table-get all-packages
                    name
                    (lambda ()
                      (let ([new-package (build-package name)])
                        (hash-table-put! all-packages name new-package)
                        new-package))))

  (provide/contract (get-package ((listof symbol?) . -> . package?))))
