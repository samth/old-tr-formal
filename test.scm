(module test mzscheme
  
  (require (lib "match.ss") (lib "list.ss") (lib "etc.ss") (lib "contract.ss"))
  
  (define (simplify-list l)
    (let loop ((l l) (result l))
      (if (null? l) result
          (loop (cdr l)
                (cons (car l)
                      (filter (lambda (x) (not (equal? x (car l))))
                        result))))))
  
  (define (extend env key val)
    (cons (list key val) env))
  
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
  
  (define (mk-union-ty l)
    (let ((l (simplify-list l)))
          (if (= 1 (length l)) (car l) (make-union-ty l))))
  
  (print-struct #t)
  
  ; name is a symbol
  (define-struct ty-ref (name) (make-inspector))

  (define* lon (mk-union-ty `(Empty (Number . ,(make-ty-ref 'LoN)))))
  
  (define* nelon (mk-union-ty `((Number . Empty) (Number . ,(make-ty-ref 'nelon)))))
  
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
       (mk-union-ty (map-opt cons?-trans cl))]
      [ty #f])
    )
  
  ; type -> type
  (define*/c (empty?-trans ty) 
    (-> type/c type/c)
    (match ty
      [($ ty-ref t) (empty?-trans (lookup t tyenv))]
      ['Empty ty]
      [($ union-ty (cl ...))
       (mk-union-ty (map-opt empty?-trans cl))]
      [ty #f])
    )
  
 ; type (type -> type) -> type 
  (define*/c (update-type-car ty transform)
    (type/c (type/c . -> . type/c) . -> . type/c)
    (match ty
      [($ ty-ref t) (update-type-cdr (lookup t tyenv) transform)]
      [($ union-ty (cl ...)) (mk-union-ty (map-opt (lambda (x) (update-type-car x transform)) cl))]
      [_ (let ((t (transform (car ty))))
           (and t (cons  t (cdr ty)) ))]))

  ; type (type -> type) -> type  
  (define*/c (update-type-cdr ty transform)
    (type/c (type/c . -> . type/c) . -> . type/c)
    (match ty
      [($ union-ty (cl ...)) (mk-union-ty (map-opt (lambda (x) (update-type-cdr x transform)) cl))]
      [($ ty-ref t) (update-type-cdr (lookup t tyenv) transform)]
      [_ (let ((t (transform (cdr ty))))
           (and t (cons (car ty) t)))]))
  
  (define (update-type exp env transform)
    (match exp
      [('car (? symbol? v))
       (let ((new-t (update-type-car (lookup v env) transform)))
         (extend env v new-t))]
      [('cdr (? symbol? v))
       (let ((new-t (update-type-cdr (lookup v env) transform)))
         (extend env v new-t))]
      [(? symbol? v)
       (let ((new-t (transform (lookup v env))))
         (extend env v new-t))]
      [_ (error "bad cond question exp")]
      ))
  
  (define (extend-env-from-q question env)
    (match question
      [('cons? e) (update-type e env cons?-trans)]
      [('empty? e) (update-type e env empty?-trans)]))
  
  (define equal-ty 
    (match-lambda*
      [('Any _) #t]
      [(_ 'Any) #t] 
      [(t (and g ($ union-ty ts)))
       (andmap (lambda (x) (equal? t x)) ts)]
      [(goal actual)
       (equal? goal actual)]))
  
  (define (check-equal-ty goal actual)
    (if (not (equal-ty goal actual))
        (type-error goal actual)))
       
           

  (define (type-error goal actual)
    (printf "typecheck failed: ~a and ~a~n" goal actual))
  
  (define (car-of-ty t)
    (match t
      [($ ty-ref t) (car-of-ty (lookup t tyenv))]
      [(a . _) a]
      [($ union-ty (cl ...))
       (mk-union-ty (map car-of-ty cl))]
      [_ #f]))
  
  (define (cdr-of-ty t)
    (match t
      [($ ty-ref t) (cdr-of-ty (lookup t tyenv))]
      [(_ . a) a]
      [($ union-ty (cl ...))
       (mk-union-ty (map-opt cdr-of-ty cl))]))  
  
  
  (define (check-cond-clause clause goal env)
    (match clause
      [('else _) (error "else not supported")]
      [(question answer)
       (let ((new-env (extend-env-from-q question env)))
         (check-exp answer goal new-env))]))
  
  (define (check-cond clauses goal env)
    (for-each (lambda (cl) (check-cond-clause cl goal env)) clauses) 
    goal)
  
  (define (check-exp expr goal env)
    (match expr
      [('cond clauses ...) (check-cond clauses goal env)]
      [(or 'empty '()) (check-equal-ty goal 'Empty) goal]
      [(? number? e) (check-equal-ty goal 'Number) goal]
      [('car e) (let* ((t (check-exp e 'Any env))
                       (car-t (car-of-ty t)))
                      (check-equal-ty goal car-t)
                  car-t)]
      [('cdr e) 
;       (printf "env: ~a" env)
       (let* ((t (check-exp e 'Any env))
              (cdr-t (cdr-of-ty t)))
         (check-equal-ty goal cdr-t)
         cdr-t)]
      [(? symbol? exp) 
       (newline)
       (display env)
       (let ((var-ty (lookup exp env)))
         (check-equal-ty goal var-ty)
         var-ty)]
      ))
  
  (define (check-def def env)
    (match def
      [('define (fun (and args ((arg ty) ...))) result
         body)
       (let ((new-env (append args env)))
         (display new-env)
         (check-exp body result new-env))]))
  
  (define simple-def `(define (foo ((ll ,(make-ty-ref 'nelon)))) Number
                        (cond [(empty? (cdr ll)) 1]
                              [(cons? (cdr ll)) (car (cdr ll))])))
  
  (define wrong-def `(define (foo ((ll ,(make-ty-ref 'nelon)))) Number
                       (cond [(empty? ll) 1]
                             [(cons? ll) (car (cdr ll))])))
  (define simple-env 
    `((l ,(make-ty-ref 'LoN))
      (l2 ,(make-ty-ref 'nelon))))
  
  )