(module typecheck mzscheme
  
  (require (lib "match.ss") (lib "list.ss") (lib "etc.ss"))
  
  (require "test.scm")
  
  (define-struct fun-ty (args result) (make-inspector))
  
 
  
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
  
  (define informing
    `(
      (number? (Any) (Number))
      (boolean? (Any) (Boolean))
      (symbol? (Any) (Symbol))
      (posn? (Any) (posn))
      ))
  
  
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
     ))
  
  (define (symbol-append . x)
    (string->symbol (apply string-append (map symbol->string x))))
  
  (define (type-struct nm fields tys)
    (let* ((pred (symbol-append nm '?))
          (pred-ty (list pred (make-fun-ty '(Any) 'Boolean)))
          (maker (symbol-append 'make- nm))
          (maker-ty (list maker (make-fun-ty tys nm)))
          (accs (map (lambda (x) (symbol-append nm '- x)) fields))
          (acc-tys (map (lambda (n t)
                          (list n (make-fun-ty (list nm) t)))
                        accs tys)))
      (list* pred-ty maker-ty acc-tys)))
  
  
  (define current-exp (make-parameter #f))
  
  (define (check-cond clauses exp-ty env)
    (for-each (lambda (x) (parameterize ((current-exp (cons 'cond x))) (check-cond-clause x exp-ty env)))
              clauses)
    exp-ty)
  
  (define (check-cond-clause clause exp-ty env)
    (match clause
      [('else x) (error "else not supported")]
      [(question result)
       (check-exp question 'Boolean env)
       (let ((new-env (extend-env-from-q question env)))
         (check-exp result exp-ty new-env))]))
  
    
  (define variable? symbol?)
  
  (define (extend-env-from-q question old-env)
    (match question
      [('cons? (? symbol? v))
       (let* ((t (lookup v old-env))
              (new-t (cons?-trans t)))
         (if new-t
             (cons (list v new-t) old-env)
             old-env))]
         
      [('cons? ('car (? symbol? v))) 
       (let* ((t (lookup v old-env))
              (new-t (update-type-car t cons?-trans)))
         (if new-t
             (cons (list v new-t) old-env)
             old-env))]
      [('cons? ('cdr (? symbol? v)))
       (let* ((t (lookup v old-env))
              (new-t (update-type-cdr t cons?-trans)))
         (if new-t
             (cons (list v new-t) old-env)
             old-env))]
                   
      #;[(f . args) (let ((info (assoc f informing)))
                    (if info
                        (let* ((new-tys (third info))
                               (new-assocs (filter (lambda (x) (variable? (car x))) (map list args new-tys)))
                               )
                          (append new-assocs old-env))
                        old-env))]
      [_ old-env]))
  
  (define (verify-ty a b exp)
    (cond [(equal? a b) b]
          [(equal? a 'Any) b]
          [(equal? b 'Any) (error "expressions can't have Any type")]
          [(and (union-ty? a)
                (let ((alts (union-ty-alts a)))
                  (ormap (lambda (x) (equal? x b)) alts))) b]
          [(and 
            (pair? a)
            (equal? (car a) 'Listof)
            (or (equal? 'Empty b)
                (equal? (cons (cadr a) a) b))) a]
          [else
           (begin (printf "mismatched types - expected: ~a actual: ~a~n" a b)
                  (if (equal? 'cond (car (current-exp))) 
                      (printf "while checking cond clause: ~a~n" (cdr (current-exp)) )
                      (printf "while checking expression: ~a~n" (current-exp)))
                  (printf "the incorrect expression was: ~a~n" exp)
                  (newline)
                  a)]))
  
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
  
  (define (all-is-cons t)
    (match t
      [(_ . _) #t]
      [($ union-ty (cl ...))
       (andmap all-is-cons cl)]
      [($ ty-ref t)
       (lookup t tyenv)]))
  
  #;(define (check-exp exp exp-ty env)
    (match exp
      [(or 'empty '()) (verify-ty exp-ty 'Empty exp)]
      [(? number? exp) (verify-ty exp-ty 'Number exp)]
      [(or 'true 'false) (verify-ty exp-ty 'Boolean exp)]
      [('cond . clauses) (check-cond clauses exp-ty env)]
      #;[('car x) (let ((t (verify-ty (cons exp-ty `(Listof ,exp-ty)) (lookup x env) exp)))
                  exp-ty)]
      [('car x) (let ((t (check-exp )
                  (verify-ty exp-ty t))))]
      [('cdr x) (let ((t (cdr-of-ty (lookup x env))))
                  (verify-ty exp-ty t exp))]
      [('cons f r) (let ((ft (check-exp f 'Any env)))
                     (cons ft (check-exp r `(Listof ,ft) env)))]
      [((? symbol? fun) . args) (check-fun-app fun args exp-ty env)]
      [(? symbol? exp) (verify-ty exp-ty (lookup exp env) exp)]
      ))
  
  (define (check-fun-app fun args exp-ty env) 
    (let* ((fun-ty (lookup fun env))
           (_ (if (not fun-ty) (display fun)))
           (exp-args (fun-ty-args fun-ty))
           (ret (fun-ty-result fun-ty)))
      (parameterize ((current-exp `(,fun . ,args)))
        (for-each (lambda (x y) (check-exp y x env)) exp-args args))
      (verify-ty exp-ty ret `(,fun . ,args))))
  
  (define (check exp env)
    (match exp
      [('define (nm . args) (arg-tys ...) ret-ty body)
       (check-def nm args arg-tys ret-ty body env)]
      [('define-struct nm ((fields tys) ...))
       (append (type-struct nm fields tys) env)]
      [_ (current-exp exp)
         (check-exp exp 'Any env)
         env]))
  
  (define (check-multi forms env)
    (foldl check env forms))
  
  (define (checks f e) (check-multi f e) (void))
  
  (define (check-def nm args arg-tys ret-ty body env)
    (let* ((ft (list nm (make-fun-ty arg-tys ret-ty))) 
           (new-env (append 
                            (list ft)
                            (map list args arg-tys) 
                            env))
          (body-ty (parameterize ((current-exp body))
                     (check-exp body ret-ty new-env))))
      (cons ft env)
      ))
  
  
  (define test-exp '(cond
                      [(equal? 3 4) 5]
                      [(equal? 4 4) 6] ))
  (define test-exp2 '(cond
                      [(equal? 3 4) foo]
                      [(+ 6 4) 5]
                      [(equal? 4 4) (and true (+ true 6))] )) 
  
  (define test-exp3 '(make-posn 0 (+ (posn-x p) (posn-y p))))
  
  (define test-exp4 '(cond
                       [(number? a) (+ a 1)]
                       [(boolean? a) (and a false)]))
  
  (define test-def1 '(define (plus a b) (Number Number) Number
                       (+ a (< 3 b))))
  
  (define test-def2 `(define (foo a) ((Listof Number)) Number
                       (cond
                         [(cons? a) (+ (< (car a) 4) (car a))]
                         [(empty? a) 0])))
  (define test-def3 `(define (bar l) ((Listof Number)) Number
                       (car l)))
  
  (define posn-def `(define-struct posn ((x Number) (y Number))))
  
  (define new-env (append (list (list 'p 'posn) (list 'a 'Any))
                          base-env))
  
  (define all-tests (list posn-def test-def1 test-def2 test-def3 test-exp test-exp2 test-exp3
                          test-exp4))
  
  (checks all-tests new-env)

  (define new-test `(define (max l) ((nelon)) Number
                      (cond
                        [(cons? (cdr l)) (car (cdr l))]
                        [(empty? (cdr l)) (car l)])))
  
  (check test-exp 'Number base-env)
  (check test-exp2 'Number new-env)
  (check test-exp3 'posn new-env)

  )