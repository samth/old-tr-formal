(let ((time-stamp "Time-stamp: <2003-11-11 11:10:17 wand>"))
  (eopl:printf
    "cfa/datalog.scm ~a~%"
    (substring time-stamp 13 29)))

;; extremely simple-minded datalog solver

;; atomic-formula ::= (symbol literal ...)

;; literal ::= number | symbol

(define (atomic-formula? x)
  (and
    (pair? x) (symbol? (car x))
    (let loop ((x (cdr x)))
      (or
        (null? x)
        (and
          (or (number? (car x)) (symbol? (car x)))
          (loop (cdr x)))))))

(define-datatype formula formula?
  (a-formula
    (patvars (list-of symbol?))              ; pattern variables
    (hypotheses (list-of atomic-formula?))
    (conclusions (list-of atomic-formula?))))

;; every pattern variable in the conclusions should be bound by in the
;; hypotheses, but we don't check this.

;;;;;;;;;;;;;;;; the solver ;;;;;;;;;;;;;;;;

;; we'll keep 2 lists:  assertions and formulas.

;; object is to close the set of assertions under the set of formulas,
;; which of course is growing itself.

;; with each formula, we'll keep a pointer to the list of assertions
;; that it has already been rubbed against

(define *assertions* '())
(define *formulas*   '())
(define *seens*      '())

(define (reset-solver)
  (set! *assertions* '())
  (set! *formulas*   '())
  (set! *seens*      '()))

(define (solve!)
  (let ((ass0 *assertions*) (fmlas *formulas*))
    (for-each rub-formula! *formulas* *seens*)
    (if (and (eqv? *assertions* ass0) (eqv? *formulas* fmlas))
      ;; nothing new concluded, so we're done
      #t
      ;; found something new
      (solve!))))

(define (solver-state)
  (list 'assertions: *assertions* 'formulas: *formulas*))

(define (rub-formula! fmla seen)
  (cases formula fmla
    (a-formula (patvars hypotheses conclusions)
      (if (null? hypotheses)
        (for-each assert! conclusions)
        (let loop! ((assertions *assertions*))
          (cond
            ((or (null? assertions) (eqv? assertions seen)) #t)
            ((match-atomic-formula
               (car hypotheses) (car assertions) patvars)
             =>
             (lambda (env)
               (assert-formula!
                 (subst-in-formula
                   (a-formula patvars (cdr hypotheses) conclusions)
                   env))
               (loop! (cdr assertions))))
             (else (loop! (cdr assertions)))))))))

(define (assert! assertion)
  (if (member assertion *assertions*) #t
    (set! *assertions* (cons assertion *assertions*))))

(define (assert-formula! fmla)
  (if (member fmla *formulas*) #t
    (begin
      (set! *formulas* (cons fmla *formulas*))
      (set! *seens*    (cons '()  *seens*)))))

;;;;;;;;;;;;;;;; pattern-matching and substitution ;;;;;;;;;;;;;;;;

(define (match-atomic-formula pattern0 subject0 patvars)
  (let loop ((pattern pattern0) (subject subject0) (env '()))
    (cond
      ;; nothing to match, return accumulated environment
      ((null? pattern) env)
      (else
        (let ((pat-item (subst-in-literal (car pattern) env)))
          (cond
            ;; pat-item is an unbound pattern variable.  So bind it.
            ((memv pat-item patvars)

             (loop (cdr pattern) (cdr subject)
                   (cons
                    (cons pat-item (car subject))
                    env)))
            ;; pat-item is a literal
            ((same-literal? pat-item (car subject))
             (loop (cdr pattern) (cdr subject) env))
            (else #f)))))))

;; ooh, sneaky!

(define same-literal? eqv?)

(define subst-in-literal
  (lambda (literal env)
    (cond
      ((assv literal env) => cdr)
      (else literal))))

(define subst-in-atomic-formula
  (lambda (atomic-fmla env)
    (map (lambda (x) (subst-in-literal x env)) atomic-fmla)))

(define subst-in-atomic-formulas
  (lambda (atomic-fmlas env)
    (map (lambda (x) (subst-in-atomic-formula x env)) atomic-fmlas)))

(define subst-in-formula
  (lambda (fmla env)
    (cases formula fmla
      (a-formula (patvars hypotheses conclusions)
        (a-formula
          patvars
          (subst-in-atomic-formulas hypotheses env)
          (subst-in-atomic-formulas conclusions env))))))

;;;;;;;;;;;;;;;; tests ;;;;;;;;;;;;;;;;

(define (assert-trans-closure sym)
  (assert-formula!
    (a-formula
      '(x y z)
      `((,sym x y) (,sym y z))
      `((,sym x z)))))

(define (test1)
  (reset-solver)
  (assert-trans-closure 'edge)
  (assert! '(edge a b))
  (assert! '(edge b c))
  (solve!)
  (solver-state))

(define (test2)
  (reset-solver)
  (assert-trans-closure 'edge)
  (assert! '(edge b c))
  (assert! '(edge a b))
  (solve!)
  (solver-state))

(define (test3)
  (reset-solver)
  (assert-trans-closure 'edge)
  (assert! '(edge 1 2))
  (assert! '(edge 2 3))
  (assert! '(edge 3 4))
  (assert! '(edge 4 5))
  (assert! '(edge 5 6))
  (assert! '(edge 6 7))
  (assert! '(edge 7 8))
  (solve!)
  (solver-state))
