(module fj mzscheme
  (require (lib "match.ss"))
  (require (lib "list.ss"))
  (require (lib "etc.ss"))
  
  (require (lib "utils.ss" "reduction-semantics" "examples" "classic-java"))
  (require (prefix env: (lib "environment.ss" "reduction-semantics" "examples" "classic-java")))
  
  ;; env?           :: Any -> Bool
  ;; make-empty-env :: () -> (Env X)
  ;; lookup         :: (Env X) Symbol (() -> Y) -> (union X Y)
  ;; extend-env     :: (Env X) (listof Symbol) (listof X) -> (Env X)
  ;; env->alist     :: (Env X) -> (Listof (List Symbol X))
  
  (require (lib "test.ss" "schemeunit"))
  (require (lib "graphical-ui.ss" "schemeunit"))
  (require (lib "text-ui.ss" "schemeunit"))
  
  (print-struct #t)
  
  (define (assert2 p)
    (if (not p)
        (error "assertion failed")))
  
  (define (hash-table-values h)
    (hash-table-map h (lambda (x y) y)))
  
  (with-public-inspector
   (define-struct expr ())
   (define-struct class (name super fields methods))
   (define-struct dec (type name))
   (define-struct (field dec) ())
   (define-struct method (name ret-type arg-decs body))
   (define-struct (arg dec) ())
   (define-struct (var expr) (name))
   (define-struct (ref expr) (rcvr fname))
   (define-struct (send expr) (rcvr mname args))
   (define-struct (constr expr) (cname args))
   (define-struct (cast expr) (cname exp))
   (define-struct (const expr) (val))
   
   (define-struct program (ct exp))
   (define-struct obj (type fields))
   
   (define-struct arrow-ty (args ret))
   
   )
  
  
  (define (field-ref o f)
    (let ((fs (obj-fields o)))
      (hash-table-get fs f)))
  
  (define field-ref-tests
    (make-test-suite "Tests for field-ref"
                     (make-test-case "ref x"
                                     (let ((o (make-obj 'Object (hash-table ('x 5)))))
                                       (assert-equal? 5 (field-ref o 'x))))))
  
  (define object (make-class 'Object #f '() (make-hash-table)))
  (define class-table (make-parameter (hash-table ('Object object))))
  (define (reinit-class-table) (class-table (hash-table ('Object object))))
  
  (define (lookup-class cname) 
    (if (eq? cname 'Object)
        object
        (hash-table-get (class-table) cname)))

  (define c1 '(class C1 Object ((int x))))
  (define c2 '(class C2 C1 () (int getx ((int y)) y)))
  
  (define lookup-class-tests
    (make-test-suite "Tests for lookup-class"
                     'setup
                     (reinit-class-table)
     (make-test-case "Object"
                     (assert-equal? object (lookup-class 'Object)))
     (make-test-case "Object with classtable"
                     (assert-equal? object (lookup-class 'Object))
                     setup
                     (hash-table-put! (class-table) 'C1 c1)
                     (hash-table-put! (class-table) 'C2 c2)
                     teardown 
                     (reinit-class-table)
                     )
     (make-test-case "Object with no classtable"
                     (assert-exn exn:fail:contract? (lookup-class 'Object))
                     setup (class-table (hash-table))
                     teardown (reinit-class-table))
     (make-test-case "C1"
                     (assert-equal? c1 (lookup-class 'C1))
                     setup (hash-table-put! (class-table) 'C1 c1)
                     teardown (reinit-class-table))
     (make-test-case "C1 fail"
                     (assert-exn exn:fail:contract? (lambda () (lookup-class 'C1))))
     ))
  
  (define (methods c) (class-methods (lookup-class c)))
  
  (define (mtype c m) 
    (let* ((meth (hash-table-get (methods c) m)))
      (values (method-ret-type meth)
              (map dec-type (method-arg-decs meth)))))
  
  (define (mbody c m)
     (let* ((meth (hash-table-get (methods c) m)))
       (values (map dec-name (method-arg-decs meth))
               (method-body meth))))
  
  (define (method-send o m args)
    (let*-values (((vars body) (mbody (obj-type o) m))
                  ((new-body) (subst-multiple vars args body)))
      (subst 'this o new-body)))
  
  (define (check-cast o t)
    (let ((tt (obj-type o)))
      (supertype? t tt)))
  
  (define (supertype? sub sup)
    (cond [(eq? sub sup) #t]
          [(eq? 'Object sub) #f]
          [else (supertype? (class-super (lookup-class sub)) sup)]))
  
  (define (subst-multiple olds news exp)
    (foldr subst exp olds news))
  
  (define (subst-list old new l)
    (map (lambda (x) (subst old new x)) l))
  
  (define (subst old new exp)
    (match exp
      [($ var n) (if (eq? old n) new exp)]
      [($ ref r f) (make-ref (subst old new r) f)]
      [($ send r m args) (make-send (subst old new r) m (subst-list old new args))]
      [($ cast t e) (make-cast t (subst old new e))]
      [($ constr t args) (make-constr t (subst-list old new args))]
      [($ const _) exp]
      ))
  
  
  
  (define (fields t)
    (class-fields (lookup-class t)))
  
  (define (field-names t)
    (map dec-name (fields t)))
  
  (define (field-types t)
    (map dec-type (fields t)))
  
  (define (check-expr gamma expr t) #t)
  
  (define (class-ok cl) 
    (let* ((cl (lookup-class cl)))
      (or (eq? (class-name cl) 'Object)
          (and
           (class-ok (class-super cl))
           (andmap (lambda (m) (method-ok m cl)) (hash-table-values (class-methods cl)))))))
  
  (define (override m cl ty) #t)
  
  (define (method-ok m cl) 
    (match m
      [($ method nm ret (($ dec tys params) ...) body)
       (let* ((gamma (env:make-empty-env params tys))
              (gamma2 (env:extend-env '(this) (list (class-name cl)) gamma))
              (meth-ty (make-arrow-ty tys ret)))
         (and
          (override nm (class-super cl) meth-ty)
          (check-expr gamma2 ret body)))]))


  
  (define (fj-eval exp)
    (match exp
      [($ ref r f) (field-ref (fj-eval r) f)]
      [($ send r m args) (fj-eval (method-send (fj-eval r) m (map fj-eval args)))]
      [($ cast t e) (let ((ee (fj-eval e)))
                      (if (check-cast ee t) 
                          ee
                          (error "bad cast")))]
      [($ constr t args) (make-obj t (make-immutable-hash-table (map cons (field-names t) (map fj-eval args))))]
      [_ exp]))
  
  
  (define (create-class name super fields methods)
    (let* ((super-class (lookup-class super))
           (super-fields (class-fields super-class))
           (super-methods (class-methods super-class))
           (new-cl (make-class name 
                               super 
                               (append fields super-fields) 
                               (let ((meths (append methods (hash-table-values super-methods))))
                                 (make-immutable-hash-table
                                  (map cons
                                       (map method-name meths)
                                       meths))))))
      (hash-table-put! (class-table) name new-cl)))
  
  
  
  (define parse-expr
    (match-lambda
      [('send r m . args) (make-send (parse-expr r) m (map parse-expr args))]
      [('ref r f) (make-ref (parse-expr r) f)]
      [('new C . args) (make-constr C (map parse-expr args))]
      [(? number? n) (make-const n)]
      [(? symbol? v) (make-var v)]
      [('cast T e) (make-cast T (parse-expr e))]))
  
  (define parse-class
    (match-lambda
      [('class nm super 
         (fields ...)
         methods ...)
       (list nm super 
             (map (lambda (x) (apply make-field x)) fields)
             (map (match-lambda
                    [(ret nm (args ...) body)
                     (make-method nm ret (map (lambda (x) (apply make-arg x)) args) (parse-expr body))])
                  methods) )]))
  
  
     

  (define fj
    (match-lambda 
      [((classes ...) expr)
       (match (make-program (map parse-class classes) (parse-expr expr))
         [($ program classes expr)
          (class-table (make-hash-table))
          (map (lambda (x) (apply create-class x)) classes)
          (hash-table-for-each (class-table) (lambda (cn cl) (assert2 (class-ok cn))))
          (assert2 (check-expr (env:make-empty-env) expr 'Object))
          (fj-eval expr)])]))
  
  (define fj-tests
    (make-test-suite "FJ Tests"
     lookup-class-tests))
  
  (define (run-tests)
    (test/graphical-ui fj-tests))
  
  (define (simp) (fj (list (list c1 c2) '(send (new C2 7) getx 5))))
  (define (simp2) (fj (list (list '(class C1 foo ())) '(send (new C2 7) getx 5))))
  
  )