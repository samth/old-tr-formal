;;; implicit-store/lang.scm

(let ((time-stamp "Time-stamp: <2003-10-05 11:59:20 wand>"))
  (eopl:printf "implicit-store/lang.scm ~a~%"
    (substring time-stamp 13 29)))

;;; like base/lang.scm, but with letrec restricted to procedures
;;; and implicit store opns.

(load "../init.scm")


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
    
    (expression
     ("%error")
     error-exp)
    
    ; begin
    (expression
     ("begin" (separated-list expression ";") "end")
     begin-exp)

    ; checkpoint
    (expression
     ("checkpoint" expression "recover-from-errors-with" expression)
     cp-exp)
    (expression
     ("try" expression "recover-from-errors-with" expression)
     try-exp)
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
    
    (expression
      ("set" identifier "=" expression)
      varassign-exp)

    (expression
      (effect "(" (separated-list expression ",") ")")
      effect-exp)

    (effect ("pair") pair-effect)
    (effect ("left") left-effect)
    (effect ("right") right-effect)
    (effect ("setleft") setleft-effect)
    (effect ("setright") setright-effect)
    (effect ("array") array-effect)
    (effect ("arrayset") arrayset-effect)
    (effect ("arrayref") arrayref-effect)
    ))

;;;;;;;;;;;;;;;; expressed values ;;;;;;;;;;;;;;;;

(define-datatype expval expval?
  (num-val
    (number number?))
  (bool-val (bool boolean?))
  (closure-val
    (ids  (list-of symbol?))
    (body expression?)
    (env  environment?))
  (error-val
   )
  (pair-val 
    (pairval pairval?))
  (array-val
   (arrayval arrayval?))
  )

;;;;;;;;;;;;;;;; environments ;;;;;;;;;;;;;;;;

(define-datatype environment environment?
  (empty-env)
  (extend-env
    (ids     (list-of symbol?))
    (vals    (list-of location?))
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

(define groups-for-test '(base let new-letrec implicit-store mutable-pairs begin checkpoint array try))

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

(add-test! 'explicit-store 'gensym-test-1 
"let g = let counter = newref(0) 
         in proc () let d = setref(counter, add1(deref(counter)))
                    in deref(counter)
in +((g),(g))" 3)
                  

(add-test! 'explicit-store 'even-odd-via-set-1 "
let x = newref(0)
in letrec even = proc () if zero?(deref(x)) 
                         then true
                         else let d = setref(x, sub1(deref(x)))
                              in (odd)
          odd = proc () if zero?(deref(x)) 
                        then false
                        else let d = setref(x, sub1(deref(x)))
                             in (even)
   in let d = setref(x,13) in (odd)" #t)



(add-test! 'implicit-store 'gensym-test
"let g = let count = 0 in proc() 
                        let d = set count = add1(count)
                        in count
in +((g), (g))"
3)

(add-test! 'implicit-store 'even-odd-via-set "
let x = 0
in letrec even = proc () if zero?(x) then true
                         else let d = set x = sub1(x)
                              in (odd)
          odd  = proc () if zero?(x) then false
                         else let d = set x = sub1(x)
                              in (even)
   in let d = set x = 13 in (odd)" #t)

(add-test! 'mutable-pairs 'gensym-using-mutable-pair-left
"let g = let count = pair(0,0) in proc() 
                        let d = setleft(count,add1(left(count)))
                        in left(count)
in +((g), (g))"
3)

;;; gotta check the right, too!

(add-test! 'mutable-pairs 'gensym-using-mutable-pair-right
"let g = let count = pair(0,0) in proc() 
                        let d = setright(count,add1(right(count)))
                        in right(count)
in +((g), (g))"
3)

;; test begin

(add-test! 'begin 'begin1 "begin 3 ; 4 end" 4)
(add-test! 'begin 'begin2 "begin 3 end" 3 )
(add-test! 'begin 'begin3 "let x = 3 in begin let x = 4 in x ; x end" 3 )
(add-test! 'begin 'begin4 "begin end" 0)
(add-test! 'begin 'begin5 "let x = 3 in begin set x = 4; x end" 4 )
(add-test! 'array 'array1 "let a = array(2)
p = proc (x)
let v = arrayref (x,1)
in arrayset(x,1,add1(v))
in begin
arrayset(a,1,0);
(p a);
(p a);
arrayref(a,1)
end"
2
           )
(add-test! 'array 'array2 "let x = array(2) in arrayref(x,1)" 0)
(add-test! 'array 'array3 "let x = array(2) in begin arrayset(x,1,2) ; arrayref(x,0) end" 0)

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

(add-test! 'checkpoint 'checkpoint1 "let x = (1 2) in x" 99)
(add-test! 'checkpoint 'checkpoint2 "let y = 3 x = (1 2) in x" 99)
(add-test! 'checkpoint 'checkpoint3 "(proc (x,y) 3 (1 2) 4)" 99)
(add-test! 'checkpoint 'checkpoint4 "checkpoint (proc (x,y) 3 (1 2) 4) recover-from-errors-with 12" 12)
(add-test! 'checkpoint 'checkpoint5 "(1 2)" 99)
(add-test! 'checkpoint 'checkpoint6 "checkpoint (1 2) recover-from-errors-with 12" 12)
(add-test! 'checkpoint 'checkpoint8 "+(3,(1 2))" 99)
(add-test! 'checkpoint 'checkpoint7 "let x = 4
in letrec
    loop = proc (x) (loop add1(x))
   in
    checkpoint 3
    recover-from-errors-with (loop x)" 3)
(add-test! 'checkpoint 'checkpoint9 "(proc (x) y 3)" 99)
(add-test! 'checkpoint 'cp10 "let x = 5 in checkpoint begin set x = 6 ; (2 3) end recover-from-errors-with x" 5)
(add-test! 'checkpoint 'try10 "let x = 5 in try begin set x = 6 ; (2 3) end recover-from-errors-with x" 6)
(add-test! 'array 'more-array "let x = array(2) in begin arrayset(x,1,7); arrayref(x,1) end" 7)
; change these tests to have the correct result
(add-test! 'base 'pgm3-1-2 "add1(x)" 99)
(add-test! 'base 'test3-1-unbound-variable "foo" 99)
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
      (else (error-exp)))))

(define reduce-if-redex
  (lambda (val0 e1 e2)
    (cases expval val0
      (bool-val (b) (if b e1 e2))
      (else
        (error-exp)))))

