(module classpath mzscheme
  (require (lib "list.ss" "srfi" "1"))
  (require (lib "string.ss" "srfi" "13"))
  (require "../util/unzip.ss")
  (require "../util/classfile.ss")

  (define (jar-filename? name)
    (or (string-suffix? ".jar" name)
        (string-suffix? ".zip" name)))

  (define (class-filename? name)
    (string-suffix? ".class" name))

  ;; read-jar-file : string (class-file -> a) -> (string -> (optional a))
  (define (read-jar-file filename parse-class-file)
    (zip-file-inflate (unzip/lazy filename (lambda (filename in)
                                             (parse-class-file (read-class-file in))))))

  ;; read-class-tree : string (class-file -> a) -> (string -> (optional a))
  (define (read-class-tree basedir parse-class-file)
    ;; read-class-subtree : (union string 'same) (listof string) -> (listof (cons string a))
    (define (read-class-subtree dirname subpath)
      (let* ([dir-relpath (if (eq? dirname 'same)
                              subpath
                              (append subpath (list dirname)))]
             [dir-fullpath (apply build-path basedir dir-relpath)])
        (append-map (lambda (entry-name)
                      (let ([entry-fullpath (build-path dir-fullpath entry-name)])
                        (cond
                          [(and (class-filename? entry-name) (file-exists? entry-fullpath))
                           (list (cons (string-join (append dir-relpath (list entry-name)) "/")
                                       (parse-class-file
                                        (with-input-from-file (build-path dir-fullpath entry-name)
                                          (lambda ()
                                            (read-class-file (current-input-port)))))))]
                          [(directory-exists? entry-fullpath)
                           (read-class-subtree entry-name dir-relpath)]
                          [else null])))
                    (directory-list dir-fullpath))))
    (let ([tree (read-class-subtree 'same null)])
      (lambda (filename)
        (cond
          [(assoc filename tree) => cdr]
          [else #f]))))

  ;; read-classpath-entry : (class-file -> a) -> (string -> (string -> (optional a)))
  (define (read-classpath-entry parse-class-file)
    (lambda (name)
      (cond
        [(directory-exists? name) (read-class-tree name parse-class-file)]
        [(and (jar-filename? name) (file-exists? name)) (read-jar-file name parse-class-file)]
        [else (error 'read-classpath-entry "bad classpath entry: ~v" name)])))

  ;; read-classpath : (listof string) (class-file -> a) -> (string -> (optional a))
  (define (read-classpath cp parse-class-file)
    (let ([repositories (map (read-classpath-entry parse-class-file) cp)])
      (lambda (filename)
        (ormap (lambda (lookup) (lookup filename))
               repositories))))

  (define (debug v)
    (fprintf (current-output-port) "DEBUG: ~v~n" v)
    v)

  ;; class-name : class-file -> string
  (define (class-name cf)
    (let ([pool (class-file-pool cf)]
          [this (class-file-this cf)])
      (debug (parse-utf8-info
              (vector-ref pool
                          (sub1
                           (class-info-name-index
                            (vector-ref pool
                                        (sub1 this)))))))))

  (define (test entry)
    ((read-classpath-entry class-name) entry))

  ;(test "C:\\Documents and Settings\\dherman\\My Documents\\NASA\\src\\util\\jce.zip")
  ;(test "C:\\Documents and Settings\\dherman\\My Documents\\NASA\\src\\util\\example1")
  ;(test "C:\\Documents and Settings\\dherman\\My Documents\\NASA\\src\\util\\example2")
  ;(test "C:\\Program Files\\Java\\j2re1.4.2\\lib\\rt.jar")

  (provide read-jar-file read-class-tree read-classpath))