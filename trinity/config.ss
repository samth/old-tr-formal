(module config mzscheme
  (define current-classpath
    (make-parameter (path-list-string->path-list (or (getenv "CLASSPATH") "") null)))
  (define current-sourcepath
    (make-parameter null))
  (define current-rules
    (make-parameter null))

  (provide current-classpath current-sourcepath current-rules))
