;;; base/env-lang.scm

(let ((time-stamp "Time-stamp: <2003-09-29 20:57:31 wand>"))
  (eopl:printf "base/env-lang.scm ~a~%"
    (substring time-stamp 13 29)))

;;; like base/lang.scm, but with letrec restricted to procedures
(load "../mp4/test-harness.scm")

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

    ;; try-catch
    (expression
     ("try" expression "recover-from-errors-with" expression)
     try-exp)
    
    ;; error
    (expression
     ("%error")
     error-exp)
    
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
    
    (expression
     ("cond" (arbno expression "=>" expression) "end")
     cond-exp)

;; multi-argument procedures
    (expression (identifier) var-exp) 
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

    (expression
      ("let*" (arbno  identifier "=" expression) "in" expression)
      let*-exp)
    
; EOPL letrec syntax
;     (expression  
;       ("letrec"
;         (arbno identifier "(" (separated-list identifier ",") ")"
;           "=" expression)
;         "in" expression)
;       letrec-exp)

; base/lang.scm letrec syntax
;     (expression
;       ("letrec" (arbno identifier "=" expression) "in" expression)
;       letrec-exp)

    (expression                         ; letrec is restricted to procs, sorry
      ("letrec"
        (arbno identifier
          "=" "proc" "(" (separated-list identifier ",") ")" expression)
        "in" expression) 
      letrec-exp)

    ))

;;;;;;;;;;;;;;;; expressed values ;;;;;;;;;;;;;;;;

(define-datatype expval expval?
  (num-val
    (number number?))
  (bool-val (bool boolean?))
  (error-val)
  (closure-val
    (ids  (list-of symbol?))
    (body expression?)
    (env  environment?)))

;;;;;;;;;;;;;;;; environments ;;;;;;;;;;;;;;;;

(define-datatype environment environment?
  (empty-env)
  (extend-env
    (ids     (list-of symbol?))
    (vals    (list-of expval?))
    (old-env environment?)))

(define apply-env
  (lambda (env sym)
    (cases environment env
      (empty-env ()
        (error-val))
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


;;;;;;;;;;;;;;;; test groups ;;;;;;;;;;;;;;;;

(define groups-for-test '(base let new-letrec cond try))

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


(add-test! 'cond 'one "cond false => 1 end" 0)
(add-test! 'cond 'two "cond false => 1 true => 3 end" 3)
(add-test! 'cond 'three "cond false => 1 true => 3 true => 4 end" 3)
(add-test! 'cond 'four "cond false => 1 zero?(0) => 3 true => 4 end" 3)
(add-test! 'cond 'five "cond zero?(1) => 1 zero?(0) => 3 true => 4 end" 3)

(add-test! 'base 'let*-1 "let* x = 1 y = x x = 2 in +(x,y)" 3)
(add-test! 'base 'let*-2 "let* x = 1 in let* y = 4 x = 2 in +(x,y)" 6)
(add-test! 'base 'let*-3 "let* x = 1 in x" 1)
(add-test! 'base 'let*-4 "let* x = 1 in let x = 2 in x" 2)
(add-test! 'base 'let*-4 "let* x = proc (x,y) +(x,y) y = (x 3 4) in y" 7)
(add-test! 'base 'cond1 "cond true => 2 false => 1 end" 2)
(add-test! 'base 'cond2 "cond false => 2 true => 1 end" 1)
(add-test! 'base 'cond3 "let* x = 0 in cond zero? (+(x,1)) => 2 zero?(x) => 1 end" 1)
(add-test! 'base 'cond4 "let* x = 0 in cond zero? (+(x,1)) => 2 zero?(1) => 1 end" 0)

(add-test! 'try 'try1 "let x = (1 2) in x" 99)
(add-test! 'try 'try2 "let y = 3 x = (1 2) in x" 99)
(add-test! 'try 'try3 "(proc (x,y) 3 (1 2) 4)" 99)
(add-test! 'try 'try4 "try (proc (x,y) 3 (1 2) 4) recover-from-errors-with 12" 12)
(add-test! 'try 'try5 "(1 2)" 99)
(add-test! 'try 'try6 "try (1 2) recover-from-errors-with 12" 12)
(add-test! 'try 'try8 "+(3,(1 2))" 99)
(add-test! 'try 'try7 "let x = 4
in letrec
    loop = proc (x) (loop add1(x))
   in
    try 3
    recover-from-errors-with (loop x)" 3)
(add-test! 'try 'try9 "(proc (x) y 3)" 99)
;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes the-lexical-spec the-grammar)))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

(define just-scan
  (sllgen:make-string-scanner the-lexical-spec the-grammar))

;;;;;;;;;;;;;;;; interface to test harness ;;;;;;;;;;;;;;;;

(define run-all
  (lambda ()
    (run-experiment run use-execution-outcome
      groups-for-test all-tests equal-external-reps?)))

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

;;;;;;;;;;;;;;;; utils for environments;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;; other reductions ;;;;;;;;;;;;;;;;
    
(define reduce-delta-redex
  (lambda (prim vals)
    (let
      ((args (map value->num vals)))
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
      (else (error-val)))))

(define reduce-if-redex
  (lambda (val0 e1 e2)
    (cases expval val0
      (bool-val (b) (if b e1 e2))
      (else
        (error-exp)))))

(define reduce-cond-redex
  (lambda (val res mt mr)
    (cases expval val
      (bool-val (b) (if b res
                        (cond-exp mt mr)))
      (else (error-exp)))))


