;;; base/env2.scm: bigstep interpreter using environment
;;; representation and distinct expressed values

(load "test-harness.scm")
(load "test-suite.scm")

(let ((time-stamp "Time-stamp: <2003-09-18 21:05:24 wand>"))
  (eopl:printf "base/env.scm larger illustrative language ~a~%"
               (substring time-stamp 13 29)))

;;; this file is self-contained, no need to load lang.scm or reductions.scm

;;;;;;;;;;;;;;;; top level ;;;;;;;;;;;;;;;;

(define run
  (lambda (string)
    (value-of-program (scan&parse string))))

(define run-all
  (lambda ()
    (run-experiment run use-execution-outcome
                    groups-for-test all-tests equal-external-reps?)))

;;;;;;;;;;;;;;;; syntax ;;;;;;;;;;;;;;;;

(define the-lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier
     (letter (arbno (or letter digit "_" "-" "?")))
     make-symbol)
    (number (digit (arbno digit)) make-number)
    (number ("-" digit (arbno digit)) make-number)
    ))

(define the-grammar
  '((program (expression) a-program)
    
    ;; numeric computations, but with many primitives
    
    (expression (number) const-exp)
    (expression
     (primitive "(" (separated-list expression ",") ")")
     primapp-exp)
    
    (primitive ("+")     add-prim)
    (primitive ("-")     subtract-prim)
    (primitive ("*")     mult-prim)
    (primitive ("add1")  incr-prim)
    (primitive ("sub1")  decr-prim)
    (primitive ("zero?") zero-test-prim) 
    
    ;; booleans: producers and consumers
    
    (expression ("true") true-exp)
    (expression ("false") false-exp)
    
    (expression
     ("if" expression "then" expression "else" expression)
     if-exp)
    
    ;; multi-argument procedures
    
    (expression (identifier) var-exp) 
    (expression ("%lexvar-exp" identifier number number) lexvar-exp)
    (expression
     ("proc" "(" (separated-list identifier ",") ")" expression)
     proc-exp)
    (expression
     ("(" expression (arbno expression) ")")
     app-exp)
    
    ;; let and letrec and let*
    
    (expression
     ("let" (arbno  identifier "=" expression) "in" expression)
     let-exp)
    
    ; syntax is just like let
    (expression
     ("let*" (arbno identifier "=" expression) "in" expression)
     let*-exp)
    
    (expression                         ; letrec is restricted to procs, sorry
     ("letrec"
      (arbno identifier
             "=" "proc" "(" (separated-list identifier ",") ")" expression)
      "in" expression) 
     letrec-exp)
    ))


;; expressed values

(define-datatype expval expval?
                 (num-val
                  (number number?))
                 (bool-val (bool boolean?))
                 (closure-val
                  (ids  (list-of symbol?))
                  (body expression?)
                  (env  environment?)))

;; environments

(define-datatype environment environment?
                 (empty-env)
                 (extend-env
                  ; change enviroments to be vectors
                  (ids     vector?)
                  (vals    vector?)
                  (old-env environment?)))

;;;;;;;;;;;;;;;; test groups ;;;;;;;;;;;;;;;;

(define groups-for-test '(base let new-letrec))

;; tests for new letrec

(add-test! 'new-letrec 'fact-of-6  "letrec
fact = proc (x) if zero?(x) then 1 else *(x, (fact sub1(x)))
in (fact 6)" 720)


(add-test! 'new-letrec 'odd-of-13  "letrec
even = proc (x) if zero?(x) then 1 else (odd sub1(x))
odd  = proc (x) if zero?(x) then 0 else (even sub1(x))
in (odd 13)" 1)

(add-test! 'new-letrec 'HO-nested-letrecs
           "letrec even = proc (odd,x) if zero?(x) then 1 else (odd sub1(x))
           in letrec  odd = proc (x) if zero?(x) then 0 else (even odd sub1(x))
           in (odd 13)" 1)


;; tests for let* (5 lines)
(add-test! 'base 'let*-1 "let* x = 1 y = x x = 2 in +(x,y)" 3)
(add-test! 'base 'let*-2 "let* x = 1 in let* y = 4 x = 2 in +(x,y)" 6)
(add-test! 'base 'let*-3 "let* x = 1 in x" 1)
(add-test! 'base 'let*-4 "let* x = 1 in let x = 2 in x" 2)
(add-test! 'base 'let*-5 "let* x = proc (x,y) +(x,y) y = (x 3 4) in y" 7)

;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes the-lexical-spec the-grammar)))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

(define just-scan
  (sllgen:make-string-scanner the-lexical-spec the-grammar))

;;;;;;;;;;;;;;;; interface to test harness ;;;;;;;;;;;;;;;;

(define run-one
  (lambda (test-name)
    (run-test run test-name)))

(define equal-external-reps?
  (lambda (actual-outcome correct-outcome)
    (equal? actual-outcome (suite-val-to-exp correct-outcome))))

;; this tests numeric and boolean values only

(define suite-val-to-exp
  (lambda (correct-answer)
    (cond
      ((memv correct-answer '(error dontrun)) correct-answer)
      ((number? correct-answer) (num-val correct-answer))
      ((boolean? correct-answer) (bool-val correct-answer))
      (else (eopl:error 'suite-val-to-exp
                        "bad value in test suite: ~s"
                        correct-answer)))))

;;;;;;;;;;;;;;;; utils for substitution ;;;;;;;;;;;;;;;;

;;; these are also used by environments

(define list-find-position
  (lambda (sym los)
    (list-index (lambda (sym1) (eqv? sym1 sym)) los)))

(define list-index
  (lambda (pred ls)
    (cond
      ((null? ls) #f)
      ((pred (car ls)) 0)
      (else (let ((list-index-r (list-index pred (cdr ls))))
              (if (number? list-index-r)
                  (+ list-index-r 1)
                  #f))))))

;;;;;;;;;;;;;;;; evaluator ;;;;;;;;;;;;;;;;

(define value-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp) 
                 (value-of-expression (translation-of-expression exp '()) (empty-env))))))

;; value-of-expression :: exp * closing-env -> closed value
;;
;; specification:
;;
;; (value-of-expression exp env) 
;; = (old-value-of-expression (subst exp env))
(define value-of-expression
  (lambda (exp env)
    (cases expression exp
      
      (const-exp (n) (num-val n))
      
      (primapp-exp (prim rands)
                   (let ((vals (value-of-expressions rands env)))
                     (reduce-delta-redex prim vals)))
      
      (true-exp () (bool-val #t))
      (false-exp () (bool-val #f))
      (if-exp (e0 e1 e2)
              (let ((val0 (value-of-expression e0 env)))
                (value-of-expression
                 (reduce-if-redex val0 e1 e2)
                 env)))
      
      ; just apply the enviroment with the appropriate indexes
      (lexvar-exp (id d p) (apply-env env id d p))
      
      (var-exp (_) (eopl:error "who translated this?"))
      
      (proc-exp (bvars body) 
                (closure-val bvars body env))
      
      (app-exp (rator rands)
               (let ((proc (value-of-expression  rator env))
                     (args (value-of-expressions rands env)))
                 (cases expval proc
                   (closure-val (bvars body saved-env)
                                (value-of-expression body
                                                     (extend-env (list->vector bvars) (list->vector args) saved-env)))
                   (else (eopl:error 'value-of-expression
                                     "bad rator ~s"
                                     val1)))))
      
      (let-exp (ids rhss body)
               (let ((vals (value-of-expressions rhss env)))
                 (value-of-expression body
                                      (extend-env (list->vector ids) (list->vector vals) env))))
      
      ; the original code for letrec - not changed a whit
      (letrec-exp (proc-names idss proc-bodies letrec-body)
                  (value-of-expression letrec-body
                                       (extend-env-recursively proc-names idss proc-bodies env)))
      
      ; caculate the value of the first right-hand-side
      ; then evaluate everything else with the first binding in the enviroment
      (let*-exp (ids rhss body)
                (if (null? ids) 
                    (value-of-expression body env)
                    (let ((v (value-of-expression (car rhss) env)))
                      (value-of-expression (let*-exp (cdr ids) (cdr rhss) body)
                                           (extend-env (vector (car ids)) (vector v) env)
                                           ))))
      
      
      )))

(define value-of-expressions
  (lambda (exps env)
    (map
     (lambda (exp) (value-of-expression exp env))
     exps)))

;;;;;;;;;;;;;;;; environments ;;;;;;;;;;;;;;;;

; apply-env now takes additional arguments, a depth and a position
; and it just goes straight to where it wants to go
(define apply-env
  (lambda (env sym d p)
    (cases environment env
      (empty-env ()
                 (eopl:error 'apply-env "unbound variable ~s" sym))
      (extend-env (vars vals old-env)
                  (if (and (zero? d)
                           (equal? (vector-ref vars p) sym))
                      (vector-ref vals p)
                      (apply-env old-env sym (- d 1) p))))))

; this is the extend-env-recursively from the next to last page of lecture 4
; with minor additions so that it actually works (ie, list->vector)
(define extend-env-recursively
  (lambda (proc-names idss bodies old-env)
    (let ((len (length proc-names)))
      (let ((vec (make-vector len))
            (positions (iota len)))
        (let ((new-env (extend-env (list->vector proc-names) vec old-env)))
          (for-each
            (lambda (pos ids body)
              (vector-set! vec pos (closure-val ids body new-env)))
            positions idss bodies)
          new-env)))))

; the iota function mentioned in the lecture notes
(define (iota n)
  (let riota ((k 0))
    (if (= k n) '()
        (cons k (riota (+ k 1))))))

; a function, useful for debugging, which merely translates a program
; but doesn't run it
(define (top s)
  (let ((p (scan&parse s)))
    (cases program p
      (a-program (e)
                 (translation-of-expression e '())))))

; expression context -> expression
; a context is a list of triples of the form (var-name depth position)
(define (translation-of-expression exp cxt)
  (define (toe e)
    (translation-of-expression e cxt))
  (cases expression exp
    (const-exp (_) exp)
    (true-exp () exp)
    (false-exp () exp)
    
    (lexvar-exp (a b c) (eopl:error "foo"))
    
    (primapp-exp (prim operands)
                 (primapp-exp prim (map toe operands)))
    
    (if-exp (test a b)
            (if-exp (toe test) (toe a) (toe b))) 
    
    (var-exp (v)
             (let* ((r (lookup-var v cxt))
                    (d (car r))
                    (p (cdr r)))   
               (lexvar-exp v d p)))
    
    (app-exp (rator rands)
             (app-exp (toe rator) (map toe rands)))
    
    (proc-exp (bvars body)
              (proc-exp bvars (translation-of-expression body (append (turn-ids-to-cxts bvars) (increase-depth cxt)))))
    
    (let-exp (ids exps body)
             (let-exp ids (map toe exps) (translation-of-expression body (append (turn-ids-to-cxts ids) (increase-depth cxt)))))
    
    (let*-exp (ids exps body)
              (if (null? ids) (let*-exp '() '() (toe body))
                  (let-exp (list (car ids)) (list (toe (car exps)))
                           (translation-of-expression (let*-exp (cdr ids) (cdr exps) body)
                                                      (append (turn-ids-to-cxts (list (car ids))) (increase-depth cxt))
                                                      )
                           )))
    
    (letrec-exp (proc-names param-lists proc-bodies body)
                (letrec-exp proc-names 
                            param-lists 
                            ; translate all the bodies
                            (map (lambda (plist pbody)
                                   (translation-of-expression pbody 
                                                              (append 
                                                               ; add the formals to the cxt
                                                               (turn-ids-to-cxts plist) 
                                                               ; add the other procs in the letrec to the cxt
                                                               (increase-depth (turn-ids-to-cxts proc-names))
                                                               ; the outer cxt is now at level 2
                                                               (increase-depth (increase-depth cxt)))))
                                 param-lists 
                                 proc-bodies)
                            (translation-of-expression body 
                                                       (append (turn-ids-to-cxts proc-names) 
                                                               (increase-depth cxt)))))
    
    (else (eopl:error "where did this come from"))
    
    ) )

; bump all the depths up by one
(define (increase-depth cxt)
  (map (lambda (x)
         (list (car x)
               (+ 1 (cadr x))
               (caddr x)))
       cxt))

; given a variable sym and a context, 
; find the depth and position of the sym in the cxt
(define (lookup-var v cxt)
  (if (null? cxt) (eopl:error "variable ~v not found" v)
      (let ((sym (car (car cxt)))
            (d (cadr (car cxt)))
            (p (caddr (car cxt))))
        (if (equal? v sym) (cons d p)
            (lookup-var v (cdr cxt))))))

; take a list of symbols, and make them a context at depth 0
(define (turn-ids-to-cxts ids)
  (map (lambda (x y)
         (list x 0 y))
       ids (iota (length ids)))) 

;;;;;;;;;;;;;;;; other reductions ;;;;;;;;;;;;;;;;

(define reduce-delta-redex
  (lambda (prim exps)
    (let
        ((args (map value->num exps)))
      (cases primitive prim
        (add-prim () (num-val (+ (car args) (cadr args))))
        (subtract-prim () (num-val (- (car args) (cadr args))))
        (mult-prim  () (num-val (* (car args) (cadr args))))
        (incr-prim  () (num-val (+ (car args) 1)))
        (decr-prim  () (num-val (- (car args) 1)))
        (zero-test-prim () (bool-val (zero? (car args))))
        ))))

(define value->num
  (lambda (v)
    (cases expval v
      (num-val (n) n)
      (else (eopl:error 'value-to-num "Not a num-val: ~s" exp)))))

(define reduce-if-redex
  (lambda (val0 e1 e2)
    (cases expval val0
      (bool-val (b) (if b e1 e2))
      (else
       (eopl:error 'reduce-if-redex "non-boolean test: ~s" e0)))))

