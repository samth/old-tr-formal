(module test mzscheme
  
  (require (lib "match.ss") (lib "list.ss")  (lib "contract.ss"))
  
  (require "useful.scm")
  
  (define current-expr (make-parameter #f))
  
  (define (simplify-list l)
    (let loop ((l l) (result l))
      (if (null? l) result
          (loop (cdr l)
                (cons (car l)
                      (filter (lambda (x) (not (equal? x (car l))))
                              result))))))
  
  (define (extend env key val)
    (cons (list key val) env))
  
  (define (extends env . key-vals)
    (foldr (lambda (x y) (extend y (car x) (cadr x)))
           env key-vals))
  
  
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
  
    (define (mk-union-ty l)
    (let ((l (simplify-list l)))
      (if (= 1 (length l)) (car l) (make-union-ty l))))
  
  (print-struct #t)
  
  
  
  
  (define-syntax type 
    (syntax-rules (-> : List)
      [(_ nm : args ... -> ret)
       (list (quote nm)
             (make-fun-ty (list (type args) ...)
                          (type ret)))]
      [(_ nm : t) (list (quote nm) (type t))]
      [(_ nm : List t) (make-list-ty (type t))]
      [(_ t) (quote t)]))
  
  (define-syntax types
    (syntax-rules ( : )
      [(_ (a . b) ...)
       (list (type a . b) ...)]))
  
  (define base-env
    (types 
     (+ : Number Number -> Number)
     (- : Number Number -> Number)
     (* : Number Number -> Number)
     (/ : Number Number -> Number)
     (and : Boolean Boolean -> Boolean)
     (foo : Number)
     (equal? : Any Any -> Boolean)
     (< : Number Number -> Boolean)
     (> : Number Number -> Boolean)
     (= : Number Number -> Boolean)
     (not : Boolean -> Boolean)
     (number? : Any -> Boolean)
     (boolean? : Any -> Boolean)
     (symbol? : Any -> Boolean)
     (cons? : Any -> Boolean)
     (empty? : Any -> Boolean)
     (argmax : Number Number -> Number)
     ))
  
  (define* lon (mk-union-ty `(Empty (Number . ,(make-ty-ref 'LoN)))))
  
  (define* nelon (mk-union-ty `((Number . Empty) (Number . ,(make-ty-ref 'nelon)))))
  
  ; alist of symbol * type 
  (define* tyenv `((LoN ,lon)
                   (nelon ,nelon)))
  
  ; sym alist[sym*x] -> x 
  (define* (lookup sym env)
           (cond [(assoc sym env) => cadr]
                 [else (printf "failed to find symbol ~a~n" sym) #f]))
  
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
               [($ union-ty (cl ...)) 
                (mk-union-ty (map-opt (lambda (x) (update-type-car x transform)) cl))]
               [_ (let ((t (transform (car ty))))
                    (and t (cons t (cdr ty)) ))]))
  
  ; type (type -> type) -> type  
  (define*/c (update-type-cdr ty transform)
             (type/c (type/c . -> . type/c) . -> . type/c)
             (match ty
               [($ union-ty (cl ...)) 
                (mk-union-ty (map-opt (lambda (x) (update-type-cdr x transform)) cl))]
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
  
  (define (print-env env)
    (printf "Environment:~n")
    (for-each (lambda (x) (printf "~a~n" x)) env)
    (newline))
  
  (define env1 `((nl ,(make-ty-ref 'nelon))))
  
  (define back-nelon (make-union-ty `((Number . Empty) (Number . ,(make-ty-ref 'nelon)))))
  
  (define cmp2 (lambda (x y) (<= (equal-hash-code x) (equal-hash-code y))))
  
  (define (equal-ty a b)
    (if (equal? a b) #t
        (match (list a b)
          [('Any _) #t]
          [(_ 'Any) #t] 
          [(($ ty-ref t) b) (equal-ty (lookup t tyenv) b)]
          [(a ($ ty-ref t)) (equal-ty (lookup t tyenv) a)]
          [(($ union-ty alts1) ($ union-ty alts2))
           (printf "comparing unions~n~a~n~a~n" a b)
           (andmap equal-ty (quicksort alts1 cmp2) (quicksort alts2 cmp2))]
          [(($ union-ty ts) t)
           (andmap (lambda (x) (equal-ty t x)) ts)]
          [(t ($ union-ty ts))
           (andmap (lambda (x) (equal-ty t x)) ts)]
          [_ #f])))
  
  (define (check-equal-ty goal actual)
    (if (not (equal-ty goal actual))
        (type-error goal actual)))
  
  
  
  (define (type-error goal actual)
    (printf "typecheck failed: ~a and ~a~n" goal actual)
    (printf "while checking: ~a~n" (current-expr)))
  
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
      [('else answer) (check-exp answer goal env)]
      [((and question (or ('cons? _) ('empty? _))) answer)
       (printf "checking a cons?: ~a~n" question)
       (check-exp question 'Boolean env)
       (let ((new-env (extend-env-from-q question env)))
         (check-exp answer goal new-env))]
      [(question answer)
       (check-exp question 'Boolean env)
       (check-exp answer goal env)]))
  
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
        [(or 'true 'false) 'Boolean]
        [(? symbol? exp) 
         ;(newline)
         ;(display env)
         (let ((var-ty (lookup exp env)))
           (check-equal-ty goal var-ty)
           var-ty)]
        [((? symbol? func) . args)
         ;(print-env env)
         (parameterize ((current-expr (cons func args)))
           (let* ((func-type (lookup func env))
                  (func-args (fun-ty-args func-type))
                  (func-ret (fun-ty-result func-type)))
             (for-each (lambda (arg ty) (check-exp arg ty env))
                       args func-args)
             (check-equal-ty goal func-ret)
             func-ret))]
        
        ))
  
  (define (zip a b)
    (map list a b))
  
  #;  (match '(def (foo ((a b) (a b))) foo foo3) 
        [('def (bar ((x y) ...)) baz baz2) 
         (list baz2 bar baz x y)])
  
  (define (check-def def env)
    (match def
      [('define (fun ((arg ty) ...)) result
         body)
       (let* ((func-ty (make-fun-ty ty result))
              (new-env (apply extends (extend env fun func-ty) (zip arg ty))))
         ;(display new-env)
         ;(newline)
         (check-exp body result new-env))]))
  
  (define simple-def `(define (foo ((ll ,(make-ty-ref 'nelon)))) Number
                        (cond [(empty? (cdr ll)) 1]
                              [(cons? (cdr ll)) (car (cdr ll))])))
  
  (define wrong-def `(define (foo ((ll ,(make-ty-ref 'nelon)))) Number
                       (cond [(empty? ll) 1]
                             [(cons? ll) (+ 1 (car (cdr ll)))])))
  (define simple-env 
    `((l ,(make-ty-ref 'LoN))
      (l2 ,(make-ty-ref 'nelon))))
  
  (define (argmax a b)
    (cond [(> a b) a]
          [else b]))
  
  (define test-argmax 
    `(define (argmax ((a Number) (b Number))) Number
       (cond [(> a b) a]
             [else b])))
  
  (define test-max
    `(define (my-max ((nl ,(make-ty-ref 'nelon)))) Number
       (cond
         [(empty? (cdr nl)) (car nl)]
         [(cons? (cdr nl)) (argmax (car nl) (my-max (cdr nl)))])))
  
  (define (my-max nl)
    (cond
      [(empty? (cdr nl)) (car nl)]
      [(cons? (cdr nl)) (argmax (car nl) (my-max (cdr nl)))]))
  
  (define ENV (append simple-env base-env))
  
  )