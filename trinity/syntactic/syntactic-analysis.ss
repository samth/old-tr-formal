(module syntactic-analysis mzscheme
  (require (lib "etc.ss"))
  (require (lib "list.ss" "srfi" "1"))
  (require "parser.ss")

  (define directory-map
    (opt-lambda (f dir [recursive? #f])
      (let* ([entries (map (lambda (entry)
                             (build-path dir entry))
                           (directory-list dir))]
             [files (filter file-exists? entries)]
             [subdirs (filter directory-exists? entries)])
        (if recursive?
            (append (map f files)
                    (append-map (lambda (dir)
                                  (directory-map f dir #t))
                                subdirs))
            (map f files)))))

  (define (syntactic-analysis sourcepath)
    (append-map (lambda (entry)
                  (directory-map (lambda (filename)
                                   (with-input-from-file filename
                                     (lambda ()
                                       (parse (current-input-port)))))
                                 entry
                                 #t))
                sourcepath))

  (provide syntactic-analysis))
