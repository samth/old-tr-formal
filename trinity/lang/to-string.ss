(module to-string mzscheme
  (require (lib "class.ss"))

  (define to-string<%>
    (interface () to-string))

  (define (make-object-display-handler default)
    (lambda (v out)
      (if (is-a? v to-string<%>)
          (display (send v to-string) out)
          (default v out))))

  (define (wrap-current-display-handlers!)
    (let ([stdout (current-output-port)]
          [stderr (current-error-port)])
      (port-display-handler stdout (make-object-display-handler (port-display-handler stdout)))
      (port-write-handler   stdout (make-object-display-handler (port-write-handler   stdout)))
      (port-print-handler   stdout (make-object-display-handler (port-print-handler   stdout)))
      (port-display-handler stderr (make-object-display-handler (port-display-handler stderr)))
      (port-write-handler   stderr (make-object-display-handler (port-write-handler   stderr)))
      (port-print-handler   stderr (make-object-display-handler (port-print-handler   stderr)))))

  (define-syntax with-object-display-handlers
    (syntax-rules ()
      [(_ e1 e2 ...)
       (parameterize ((port-display-handler stdout (make-object-display-handler (port-display-handler stdout)))
                      (port-write-handler   stdout (make-object-display-handler (port-write-handler   stdout)))
                      (port-print-handler   stdout (make-object-display-handler (port-print-handler   stdout)))
                      (port-display-handler stderr (make-object-display-handler (port-display-handler stderr)))
                      (port-write-handler   stderr (make-object-display-handler (port-write-handler   stderr)))
                      (port-print-handler   stderr (make-object-display-handler (port-print-handler   stderr))))
         e1 e2 ...)]))

  (provide to-string<%>
           make-object-display-handler
           wrap-current-display-handlers! with-object-display-handlers))
