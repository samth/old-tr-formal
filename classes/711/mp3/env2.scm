;;; base/env2.scm: bigstep interpreter using environment
;;; representation and distinct expressed values

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
    (expression
      ("proc" "(" (separated-list identifier ",") ")" expression)
      proc-exp)
    (expression
      ("(" expression (arbno expression) ")")
      app-exp)

    ;; let and letrec

    (expression
      ("let" (arbno  identifier "=" expression) "in" expression)
      let-exp)

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
    (ids     (list-of symbol?))
    (vals    (list-of expval?))
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
      (a-program (exp) (value-of-expression exp (empty-env))))))

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

      (var-exp (id) (apply-env env id))

      (proc-exp (bvars body) 
        (closure-val bvars body env))

      (app-exp (rator rands)
        (let ((proc (value-of-expression  rator env))
              (args (value-of-expressions rands env)))
          (cases expval proc
            (closure-val (bvars body saved-env)
              (value-of-expression body
                (extend-env bvars args saved-env)))
            (else (eopl:error 'value-of-expression
                    "bad rator ~s"
                    val1)))))

      (let-exp (ids rhss body)
        (let ((vals (value-of-expressions rhss env)))
          (value-of-expression body
            (extend-env ids vals env))))

      (letrec-exp (proc-names idss proc-bodies letrec-body)
        (value-of-expression letrec-body
          (extend-env-recursively proc-names idss proc-bodies env)))

      )))

(define value-of-expressions
  (lambda (exps env)
    (map
      (lambda (exp) (value-of-expression exp env))
      exps)))

;;;;;;;;;;;;;;;; environments ;;;;;;;;;;;;;;;;

(define apply-env
  (lambda (env sym)
    (cases environment env
      (empty-env ()
        (eopl:error 'apply-env "unbound variable ~s" sym))
      (extend-env (vars vals old-env)
        (cond
          ((list-find-position sym vars)
           => (lambda (n) (list-ref vals n)))
          (else (apply-env old-env sym)))))))

(define extend-env-recursively
  (lambda (proc-names idss proc-bodies old-env)
    (extend-env proc-names
      (map
        (lambda (ids proc-body)
          (closure-val ids 
            (letrec-exp proc-names idss proc-bodies proc-body)
            old-env))
        idss
        proc-bodies)
      old-env)))

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

