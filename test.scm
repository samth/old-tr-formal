(module test mzscheme
  
  (require (lib "match.ss") (lib "list.ss") (lib "etc.ss") (lib "contract.ss"))
  
  (define-syntax define*/c
    (syntax-rules ()
      [(_ (a args ...) cont b ...)
       (begin
         (define (a args ...) b ...)
         (provide/contract (a cont)))]))
  
  (define-syntax define*
    (syntax-rules ()
      [(_ (a args ...) b ...)
       (begin
         (define (a args ...) b ...)
         (provide a))]
      [(_ a b ...)
       (begin
         (define a b ...)
         (provide a))]))
  
  
  (define type/c any/c)
  
  ; alts is a list of types
  (define-struct union-ty (alts) (make-inspector))
  
  ; name is a symbol
  (define-struct ty-ref (name) (make-inspector))

  (define* lon (make-union-ty `(Empty (Number . ,(make-ty-ref 'LoN)))))
  
  (define* nelon (make-union-ty `((Number . Empty) (Number . ,(make-ty-ref 'nelon)))))
  
  ; alist of symbol * type 
  (define* tyenv `((LoN ,lon)
                  (nelon ,nelon)))

  ; sym alist[sym*x] -> x 
  (define*/c (lookup sym env)
    (symbol?  (listof (list/c symbol? any/c)). -> . any/c)
    (and (assoc sym env) (cadr (assoc sym env))))
  
  (define (id x) x)
  
  ; (x -> y or #f) listof[x] -> listof[y]
  (define*/c (map-opt f l)
    ((any/c . -> . any/c) (listof any/c) . -> . (listof any/c))
    (filter id (map f l)))
  
  ; type -> type
  ; unfold a recursive list type
  (define*/c (cons?-trans ty) 
    (-> any/c any/c)
    (match ty
      [($ ty-ref t) (cons?-trans (lookup t tyenv))]
      [(_ . _) ty]
      [($ union-ty (cl ...))
       (make-union-ty (map-opt cons?-trans cl))]
      [ty #f])
    )
  
  ; type -> type
  (define*/c (empty?-trans ty) 
    (-> type/c type/c)
    (match ty
      [($ ty-ref t) (empty?-trans (lookup t tyenv))]
      ['Empty ty]
      [($ union-ty (cl ...))
       (make-union-ty (map-opt empty?-trans cl))]
      [ty #f])
    )
  
 ; type (type -> type) -> type 
  (define*/c (update-type-car ty transform)
    (type/c (type/c . -> . type/c) . -> . type/c)
    (match ty
      [($ union-ty (cl ...)) (make-union-ty (map-opt (lambda (x) (update-type-car x transform)) cl))]
      [_ (let ((t (transform (car ty))))
           (and t (cons  t (cdr ty)) ))]))

  ; type (type -> type) -> type  
  (define*/c (update-type-cdr ty transform)
    (type/c (type/c . -> . type/c) . -> . type/c)
    (match ty
      [($ union-ty (cl ...)) (make-union-ty (map-opt (lambda (x) (update-type-cdr x transform)) cl))]
      [_ (let ((t (transform (cdr ty))))
           (and t (cons (car ty) t)))]))
  
  (define (update-type exp env transform)
    (match exp
      [('car (? symbol? v))
       (update-type-car (lookup v env) transform)]
      [('cdr (? symbol? v))
       (update-type-cdr (lookup v env) transform)] 
      [(? symbol? v)
       (transform (lookup v env))]
      [_ (error "bad cond question exp")]
      ))
  
  (define (extend-env-from-q question env)
    (match question
      [('cons? e) (update-type e env cons?-trans)]
      [('empty? e) (update-type e env empty?-trans)]))
  
  (define (check-equal-ty goal actual)
    (if (not (equal? goal actual))
        (printf "typecheck failed: ~a and ~a~n" goal actual)))

  (define (car-of-ty t)
    (match t
      [(a . _) a]
      [($ union-ty (cl ...))
       (make-union-ty (map-opt car-of-ty cl))]
      [_ (error "bad car" t)]))
  
  (define (cdr-of-ty t)
    (match t
      [(_ . a) a]
      [($ union-ty (cl ...))
       (make-union-ty (map-opt cdr-of-ty cl))]))  

  (define (check-car expr goal env)
    
    )
  
  (define (check-exp expr goal env)
    (match expr
      [(or 'empty '()) (check-equal-ty goal 'Empty) goal]
      [(? number? e) (check-equal-ty goal 'Number) goal]
      [('car e) (check-car e goal env)]
      [('cdr e) (check-cdr e goal env)]
      ))
  
  
  )