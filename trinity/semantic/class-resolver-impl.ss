(module class-resolver-impl mzscheme
  (require (lib "string.ss" "srfi" "13"))
  (require (lib "list.ss" "srfi" "1"))
  (require (all-except (lib "class.ss") class-info))
  (require (lib "etc.ss"))
  (require (lib "file.ss"))
  (require "class-resolver.ss")
  (require "semantic-object.ss")
  (require "analyze-ast.ss")
  (require "analyze-classfile.ss")
  (require "../util/classfile.ss")
  (require "../util/unzip.ss")
  (require "../config.ss")
  ;(require (lib "utils.ss" "reduction-semantics" "examples" "classic-java"))

  ;; ===========================================================================
  ;; DELEGATES TO PERFORM RESOLUTION
  ;; ===========================================================================

  (define (extension-equal? ext path)
    (equal? ext (filename-extension path)))
  
  (define (java-filename? name)
    (extension-equal? #"java" name))

  (define (jar-filename? name)
    (or (extension-equal? #"jar" name)
        (extension-equal? #"zip" name)))

  (define (class-filename? name)
    (extension-equal? #"class" name))

  ;; make-jar-resolver : string -> (string -> (optional declared-type%))
  (define (make-jar-resolver filename)
    (time
     (zip-file-inflate (unzip/lazy filename (lambda (filename in)
                                              (analyze-classfile (read-class-file in)))))))

  ;; make-directory-resolver : string -> (string -> (optional declared-type%))
  (define (make-directory-resolver basedir)
    (lambda (filename)
      ;(printf "in a directory resolver, for ~a ~a~n" basedir filename)
      (and (class-filename? filename)
           (let ([fullpath (build-path basedir filename)])
             (and ;(printf "about to analyze-classfile fp: ~a~n" fullpath)
                  (file-exists? fullpath)
                  (analyze-classfile
                   (with-input-from-file fullpath
                     (lambda ()
                       (begin ;(printf "analyzing a class file~n")
                              (read-class-file (current-input-port)))))))))))

  ;; make-binary-resolver : string -> (string -> (optional declared-type%))
  (define (make-binary-resolver classpath-entry)
    (cond
      [(directory-exists? classpath-entry)
       (make-directory-resolver classpath-entry)]
      [(and (jar-filename? classpath-entry) (file-exists? classpath-entry))
       ;(printf "making jar resolver ~a~n" classpath-entry)
       (make-jar-resolver classpath-entry)]
      [else
       (error 'make-resolver "bad classpath entry: ~v" classpath-entry)]))

  ;; try : (listof (a -> (optional b))) a -> (optional b)
  (define (try preds x)
    (and (pair? preds)
         (or (let ((z ((car preds) x)))
               (begin
               ;(printf "trying a predicate ~a, got ~a~n" (car preds) z)
               z))
             (try (cdr preds) x))))

  ;; ===========================================================================
  ;; CLASS RESOLVER OBJECT
  ;; ===========================================================================

  ;; class-filename : type-name -> string
  (define (class-filename name)
    (string-append
     (string-join (map symbol->string (type-name-package name)) "/" 'suffix)
     (symbol->string (type-name-type name))
     ".class"))

 
  (define class-resolver%
    (class* object% (class-resolver<%>)
      (public resolve-package resolve-type)
      (define all-packages (make-hash-table 'equal))
      
      (define/public (ap) all-packages)
      (define classpath
        (begin ;(printf "the classpath is ~a~n" (current-classpath))
               (map make-binary-resolver (current-classpath))))
      
      (define/public (cp) classpath)

      (define/public (find-package name)
        (hash-table-get all-packages
                        name
                        (lambda ()
                          (let ([entry (cons (make-object package% name)
                                             (make-hash-table))])
                            (hash-table-put! all-packages name entry)
                            entry))))

      ;; resolve-package : (union package% (listof symbol)) -> package%
      (define (resolve-package pkg)
        (if (is-a? pkg package%)
            pkg
            (car (find-package pkg))))

      ;; TODO: where to create unknown-type% instances?

      (define (resolve-primitive-type name)
        (and (null? (type-name-package name))
             (case (type-name-type name)
               [(byte)    byte]
               [(char)    char]
               [(int)     int]
               [(long)    long]
               [(short)   short]
               [(float)   float]
               [(double)  double]
               [(boolean) boolean]
               [else      #f])))

      ;; resolve-type : (union type<%> type-name) -> (optional type<%>)
      (define (resolve-type ty)
        (cond
          [(is-a? ty type<%>) ty]
          [(resolve-primitive-type ty) => identity]
          [else
           (let* ([type-name (type-name-type ty)]
                  [entry (find-package (type-name-package ty))]
                  [package (car entry)]
                  [types (cdr entry)])
             (hash-table-get types
                             type-name
                             (lambda ()
                               (let ([type (try classpath (class-filename ty))])
                                 (and type
                                      ;(printf "attempting to resolve type: ~a ty: ~a~n" type ty)
                                      (begin 
                                        (hash-table-put! types type-name type)
                                        (send type resolve-all)
                                        type))))))]))

      (super-new)))

  (provide class-resolver%))
