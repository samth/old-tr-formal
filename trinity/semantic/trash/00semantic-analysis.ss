(module semantic-analysis mzscheme
  (require (lib "contract.ss"))
  (require (lib "match.ss"))
  (require (lib "etc.ss"))
  (require "../lang/struct.ss")
  (require "../util/classfile.ss")
  (require "semantic-object.ss")
  (require "parse-classfile.ss")

  (define (interpret-class-file cf)
    (class-file-pool cf))

  ;; TODO: interpret it in an environment with the imports

  #|
  ;; interpret-type : (optional type-decl) package -> (optional type)
  (define (interpret-type decl package)
    (and decl
         (match decl
           [($ class-decl src mods name ints body super)
            (make-class decl
                        package
                        (map modifier-modifier mods)
                        (id-name name)
                        null
                        null ; TODO: implement this
                        #f)]
           [($ interface-decl src mods name ints body)
            (make-interface decl
                            package
                            (map modifier-modifier mods)
                            (id-name name)
                            null
                            null ; TODO: implement this
                            )])))

  (define (interpret-class-file cf)
    (let ([pool (class-file-pool cf)])
      #f))

  ;; build-package-alist : (listof compilation-unit)
  ;;                    -> (alistof (optional (listof symbol)) package)
  (define (build-package-alist source)
    (foldl (lambda (file packages)
             (match file
               [($ compilation-unit _ name-src _ types-src)
                (let* ([path (interpret-name name-src)]
                       [package (or (assoc packages path)
                                    (make-package null path null))]
                       ;; TODO: handle inner classes
                       [types (filter-map (lambda (type)
                                            (interpret-type type package))
                                          types-src)])
                  (match package
                    [($ package old-sources _ old-types)
                     (cons (cons path (make-package (cons file old-sources)
                                                    path
                                                    (append types old-types)))
                           (alist-delete path packages))]))]))
           source))

  ;; 1. create the hash table [package |-> (cons (listof symbol?) (listof type))]
  ;; 2. traverse classpath looking for types, add packages/types to hash table
  ;; 3. parse the source looking for types, add packages/types to hash table

  (define (build-package-hash-table classpath)
    (let ([table (make-hash-table 'equal)])
      (read-classpath classpath
                      (match-lambda
                        [($ class-file pool access-flags this-index super-index
                                       interfaces fields methods attributes)
                         (let ([deref (lambda (i) (vector-ref pool (sub1 i)))])
                           (let ([modifiers (parse-access-flags access-flags)]
                                 [this-name (parse-utf8-info
                                             (class-info-name-index
                                              (deref this-index)))]
                                 [super-name (parse-utf8-info
                                              (class-info-name-index
                                               (deref super-index)))])
                             (make-class 
      (for-each (lambda (file)
                  (match file
                    [($ compilation-unit _ name-src _ types-src)
                     (let* ([path (interpret-name name-src)]
                            [package 
  ;; build-world : (listof compilation-unit) -> world
  (define (build-world source)
    (let ([packages (map cdr (build-package-alist source))])
      (make-world packages
                  (append-map package-types packages))))
  |#

  (provide))
