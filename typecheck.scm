(module typecheck mzscheme
  
  (require (lib "match.ss") (lib "list.ss") (lib "etc.ss"))
  
  (define-struct fun-ty (args result) (make-inspector))
  
  (define-struct cons-ty (first rest) (make-inspector))
  
  (define-struct union-ty (alts) (make-inspector))
  
 
  
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
  
  (define (lookup sym env)
    (and (assoc sym env) (cadr (assoc sym env))))
  
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
      [('cons? v) (match (lookup v old-env)
                   [('Listof t)
                    (if (variable? v) 
                        (cons (list v (make-cons-ty t (list 'Listof t))) old-env)
                        old-env)])]
                   
      [(f . args) (let ((info (assoc f informing)))
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
                (equal? (make-cons-ty (cadr a) a) b))) a]
          [else
           (begin (printf "mismatched types - expected: ~a actual: ~a~n" a b)
                  (if (equal? 'cond (car (current-exp))) 
                      (printf "while checking cond clause: ~a~n" (cdr (current-exp)) )
                      (printf "while checking expression: ~a~n" (current-exp)))
                  (printf "the incorrect expression was: ~a~n" exp)
                  (newline)
                  a)]))
  
  (define (check-exp exp exp-ty env)
    (match exp
      [(or 'empty '()) (verify-ty exp-ty 'Empty exp)]
      [(? number? exp) (verify-ty exp-ty 'Number exp)]
      [(or 'true 'false) (verify-ty exp-ty 'Boolean exp)]
      [('cond . clauses) (check-cond clauses exp-ty env)]
      [('car x) (let ((t (verify-ty (make-cons-ty exp-ty `(Listof ,exp-ty)) (lookup x env) exp)))
                  exp-ty)]
      [('cons f r) (let ((ft (check-exp f 'Any env)))
                     (make-cons-ty ft (check-exp r `(Listof ,ft) env)))]
      [((? symbol? fun) . args) (check-fun-app fun args exp-ty env)]
      [(? symbol? exp) (verify-ty exp-ty (lookup exp env) exp)]
      ))
  
  (define (check-fun-app fun args exp-ty env) 
    (let* ((fun-ty (lookup fun env))
           (exp-args (fun-ty-args fun-ty))
           (ret (fun-ty-result fun-ty)))
      (parameterize ((current-exp `(,fun . ,args)))
        (for-each (lambda (x y) (check-exp y x env)) exp-args args))
      (verify-ty exp-ty ret `(,fun . ,args))))
  
  (define (check exp ty env)
    (match exp
      [('define (nm . args) (arg-tys ...) ret-ty body)
       (check-def nm args arg-tys ret-ty body env)]
      [_ (current-exp exp)
         (check-exp exp ty env)]))
  
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
  
  (define new-env (append (list (list 'p 'posn) (list 'a 'Any))
                          (type-struct 'posn '(x y) '(Number Number)) 
                          base-env))
  
  (check test-exp 'Number base-env)
  (check test-exp2 'Number new-env)
  (check test-exp3 'posn new-env)
  )