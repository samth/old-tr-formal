(module test mzscheme
  
  (require (lib "match.ss") (lib "list.ss") (lib "etc.ss"))
  
  
  ; alts is a list of types
  (define-struct union-ty (alts) (make-inspector))
  
  (define-struct ty-ref (name) (make-inspector))

  (define lon (make-union-ty `(Empty (Number . ,(make-ty-ref 'LoN)))))
  
  (define nelon (make-union-ty `((Number . Empty) (Number . ,(make-ty-ref 'nelon)))))
  
  (define tyenv `((LoN ,lon)
                  (nelon ,nelon)))

  (define (lookup sym env)
    (and (assoc sym env) (cadr (assoc sym env))))
  
  (define (id x) x)
  
  (define (map-opt f l)
    (filter id (map f l)))
  
  ; type -> type
  ; unfold a recursive list type
  (define (cons?-trans ty)
    (match ty
      [($ ty-ref t) (cons?-trans (lookup t tyenv))]
      [(_ . _) ty]
      [($ union-ty (cl ...))
       (make-union-ty (map-opt cons?-trans cl))]
      [ty #f])
    )
  
  (define pred-tranforms
    `((cons? ,cons?-trans)))
  
 
  (define (update-type-car ty transform)
    (match ty
      [($ union-ty (cl ...)) (make-union-ty (map-opt (lambda (x) (update-type-car x transform)) cl))]
      [_ (let ((t (transform (car ty))))
           (and t (cons  t (cdr ty)) ))]))
 
  (define (update-type-cdr ty transform)
    (match ty
      [($ union-ty (cl ...)) (make-union-ty (map-opt (lambda (x) (update-type-cdr x transform)) cl))]
      [_ (let ((t (transform (cdr ty))))
           (and t (cons (car ty) t)))]))
  
  (provide (all-defined))
  )