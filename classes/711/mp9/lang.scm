;;; base/lang.scm

(let ((time-stamp "Time-stamp: <2003-09-17 16:38:46 wand>"))
  (eopl:printf "base/lang.scm larger illustrative language ~a~%"
    (substring time-stamp 13 29)))

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

    (expression
      ("letrec" (arbno identifier "=" expression) "in" expression)
      letrec-exp)

    ))

;;;;;;;;;;;;;;;;; test groups ;;;;;;;;;;;;;;;;
;
;(define groups-for-test '(base let new-letrec))
;
;;; tests for new letrec
;
;(add-test! 'new-letrec 'fact-of-6  "letrec
;  fact = proc (x) if zero?(x) then 1 else *(x, (fact sub1(x)))
;  in (fact 6)" 720)
;
;
;(add-test! 'new-letrec 'odd-of-13  "letrec
;         even = proc (x) if zero?(x) then 1 else (odd sub1(x))
;         odd  = proc (x) if zero?(x) then 0 else (even sub1(x))
;       in (odd 13)" 1)
;
;(add-test! 'new-letrec 'HO-nested-letrecs
;  "letrec even = proc (odd,x) if zero?(x) then 1 else (odd sub1(x))
;   in letrec  odd = proc (x) if zero?(x) then 0 else (even odd sub1(x))
;   in (odd 13)" 1)

;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes the-lexical-spec the-grammar)))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

(define just-scan
  (sllgen:make-string-scanner the-lexical-spec the-grammar))

;;;;;;;;;;;;;;;; substitution ;;;;;;;;;;;;;;;;

;; subst-closed : expression * (listof symbol) * (listof closed expression)
;;    -> expression

(define subst-closed
  (lambda (exp ids new-exps)
   (let recur ((exp exp)
               (bvars '()))             ; bvars are variables that are
                                        ; subtracted from the domain
                                        ; of the substitution.
     ;; no mysterious auxiliaries!:
     ;; (recur exp bvars)
     ;;  = (subst-closed exp
     ;;      (set-diff ids bvars) (remove new-exps right-things)) 

     (let
       ((recur*                         ; handy mapping function
          (lambda (exps bvars)
            (map (lambda (exp) (recur exp bvars)) exps))))

       (cases expression exp 

        (const-exp (n) exp)
        (primapp-exp (primop rands)
          (primapp-exp primop (recur* rands bvars)))

        (var-exp (id)
          (cond
            ((memq id bvars) exp)
            ((list-find-position id ids)
             => (lambda (pos) (list-ref new-exps pos)))
            (else exp)))

        (true-exp () exp)
        (false-exp () exp)
        (if-exp (e0 e1 e2)
          (if-exp (recur e0 bvars) (recur e1 bvars) (recur e2 bvars)))

        (proc-exp (ids body)
          (proc-exp ids (recur body (append ids bvars))))
        (app-exp (rator rands)
          (app-exp
            (recur rator bvars)
            (recur* rands bvars)))

        (let-exp
          (ids rhss body)
          (let-exp
            ids
            (recur* rhss bvars)
            (recur body (append ids bvars))))
; code for old EOPL letrec
;         (letrec-exp
;           (proc-names idss proc-bodies letrec-body)
;           (letrec-exp
;             proc-names
;             idss
;             (map
;               (lambda (ids proc-body)
;                 (recur proc-body (append ids proc-names bvars)))
;               idss
;               proc-bodies)
;             (recur letrec-body (append proc-names bvars))))
        (letrec-exp
          (ids rhss letrec-body)
          (letrec-exp
            ids
            (recur* rhss (append ids bvars))
            (recur letrec-body (append ids bvars))))

        )))))


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
      ((number? correct-answer) (const-exp correct-answer))
      ((boolean? correct-answer) 
       (if correct-answer (true-exp) (false-exp)))
      (else (eopl:error 'suite-val-to-exp
              "bad value in test suite: ~s"
              correct-answer)))))

;;;;;;;;;;;;;;;; utils for substitution ;;;;;;;;;;;;;;;;

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
