(module oo mzscheme
  (require (lib "etc.ss")
           (lib "list.ss"))
  
 
  
  ;; Name [Object] [Object]
  ;; we try each object in thiss in order, until it works
  (define-struct msg (name thiss args))
  
  ;; Name [Object]
  (define-struct object (class fields))
  
  ;; Name [Name]
  (define-struct interface (name methods))
  
  ;; Name [Interface]
  (define-struct wrapper (field-name interf))
  
  ;; Name Body 
  ;; body must be a function which takes exactly one argument of type msg
  (define-struct method (name body))
  
  ;; Name [Name] [Wrapper] [Method] 
  (define-struct class (name field-names wrappers methods))
  
  (define (accepts-msg? obj m)
    #t ; FIXME
    )
  
  (define (get-method obj m)
    (let* ((cl (object-class obj))
          
           (meths (class-methods cl)))
      (let loop
        ((ms meths))
        (if (equal? (method-name (car ms)) m) (method-body (car ms))
            (loop (cdr ms))))))
  
  (define (find-acceptor meth objs)
    (cond [(empty? objs) #f ]
          [(accepts-msg? (car objs) meth) (car objs)]
          [else (find-acceptor meth (cdr objs))]))
  
  (define (send rcvr msg)
    (let*
        ([c (object-class rcvr)]
         [m (msg-name msg)]
         [thiss (cons rcvr (msg-thiss msg))]
         [real-rcvr (find-acceptor m thiss)]
         [meth (get-method real-rcvr m)]) 
      (meth msg)))
  
  (define C (make-class 'C '() '() `(,(make-method 'm (lambda (x) 1)))))
  (define D (make-class '
  
  (define c (make-object C '()))
  (define m (make-msg 'm '() 3))
  
  )