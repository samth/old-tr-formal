;;; big-step interpreter for CSG 711 basic language

(load "lang.scm")
(load "reductions.scm")

(let ((time-stamp "Time-stamp: <2003-09-17 16:38:12 wand>"))
  (eopl:printf
    "base/bigstep.scm ~a~%"
    (substring time-stamp 13 29)))

;;;;;;;;;;;;;;;; top level ;;;;;;;;;;;;;;;;

(define run
  (lambda (string)
    (value-of-program (scan&parse string))))

;;;;;;;;;;;;;;;; evaluator ;;;;;;;;;;;;;;;;

(define value-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp) (value-of-expression exp)))))

;; value-of-expression :: closed exp -> closed value
(define value-of-expression
  (lambda (exp)
    (cases expression exp
                                       
      (const-exp (n) exp)
      (primapp-exp (prim rands)
        (let ((vals (value-of-expressions rands)))
          (value-of-expression (reduce-delta-redex prim vals))))

      (true-exp () exp)
      (false-exp () exp)
      (if-exp (e0 e1 e2)
        (let ((val0 (value-of-expression e0)))
          (value-of-expression (reduce-if-redex val0 e1 e2))))

      (var-exp (id)
        (eopl:error 'step-once "non-closed expression ~s" exp))
      (proc-exp (bvar body) exp)        ; lambda-abstractions are values 
      (app-exp (rator rands)
        (let ((proc (value-of-expression  rator))
              (args (value-of-expressions rands)))
          (value-of-expression (reduce-beta-redex proc args))))
      
      (let-exp (ids rhss body)
        (let ((vals (value-of-expressions rhss)))
          (value-of-expression (reduce-let-redex ids vals body))))

; old eopl syntax
;       (letrec-exp (proc-names idss proc-bodies letrec-body)
;         (value-of-expression
;           (reduce-letrec-redex proc-names idss proc-bodies letrec-body)))

      (letrec-exp (ids rhss body)
        (value-of-expression (reduce-letrec-redex ids rhss body)))
      (let*-exp (ids rhss body)
                (value-of-expression (reduce-let*-redex ids rhss body)))
      
      (cond-exp (tests results) 
                (if (null? tests) (value-of-expression (const-exp 0))
                    (let ((v0 (value-of-expression (car tests))))
                      (value-of-expression (reduce-cond-redex (cons v0 (cdr tests)) results)))))
      
      (nil-exp ()
               (nil-exp))
      
      (cons-exp (a b)
                (let ((v0 (value-of-expression a))
                      (v1 (value-of-expression b)))
                  (cons-exp v0 v1)))
      
      (car-exp (l)
               (let ((v0 (value-of-expression l)))
                 (value-of-expression (reduce-car-redex v0))))
      
      (cdr-exp (l)
               (let ((v0 (value-of-expression l)))
                 (value-of-expression (reduce-cdr-redex v0))))
            
      (nil-test-exp (l)
               (let ((v0 (value-of-expression l)))
                 (value-of-expression (reduce-nil-test-redex v0))))

      )))

(define value-of-expressions
  (lambda (exps)
    (map value-of-expression exps)))





