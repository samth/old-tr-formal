;;; small-step interpreter for base language

;(load "../init.scm")
(load "lang.scm")
(load "reductions.scm")


(let ((time-stamp "Time-stamp: <2003-09-17 16:37:46 wand>"))
  (eopl:printf
    "base/smallstep.scm ~a~%"
    (substring time-stamp 13 29)))

;;;;;;;;;;;;;;;; top level ;;;;;;;;;;;;;;;;

(define run
  (lambda (string)
    (reduce-to-value-program (scan&parse string))))

(define reduce-to-value-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp) (reduce-to-value exp)))))

;; reduce-to-value : closed-expression -> closed-value
(define reduce-to-value
  (lambda (exp)
    (let loop ((exp exp))              
      (if *trace* (eopl:pretty-print exp))
      (cond
        ((step-once exp)                ; step-once either returns the
                                        ; next exp or #f
         => (lambda (next-exp) (loop next-exp)))
        ;; or just ((step-once exp) => loop) !!!
        (else exp)))))

(define *trace* #f)                     ; default tracing off
(define (toggle-trace) (set! *trace* (not *trace*)) *trace*)

;;;;;;;;;;;;;;;; the stepper ;;;;;;;;;;;;;;;;

;; step-once : closed expression -> (optional closed expression)
;; reduces by one step, else returns #f
;;
(define step-once
  (lambda (exp)
    (cases expression exp

      (const-exp (n) #f)
      (primapp-exp (prim rands)
        (cond
          ((step-once-list rands)
           => (lambda (new-rands) (primapp-exp prim new-rands)))
          (else (reduce-delta-redex prim rands))))

      (true-exp () #f)
      (false-exp () #f)
      (if-exp (e0 e1 e2)
        (cond
          ((step-once e0) => (lambda (new-e0) (if-exp new-e0 e1 e2)))
          (else (reduce-if-redex e0 e1 e2))))

      (var-exp (id)
        (eopl:error 'step-once "non-closed expression ~s" exp))
      (proc-exp (id body) #f)
      (app-exp (rator rands)
        (cond
          ((step-once rator)
           => (lambda (new-rator) (app-exp new-rator rands)))
          ((step-once-list rands)
           => (lambda (new-rands) (app-exp rator new-rands)))
          (else
            (reduce-beta-redex rator rands))))

      (let-exp (ids rhss body)
        (cond
          ((step-once-list rhss)
           => (lambda (new-rhss) (let-exp ids new-rhss body)))
          (else
            (reduce-let-redex ids rhss body))))
      (let*-exp 
       (ids rhss body)
       (cond ((null? rhss) (reduce-let*-redex ids rhss body))
             ((step-once (car rhss)) => (lambda (x) (reduce-let*-redex ids (cons x (cdr rhss)) body)))
             (else (reduce-let*-redex ids rhss body))))
; old eopl version
;       (letrec-exp (proc-names idss proc-bodies letrec-body)
;         (reduce-letrec-redex proc-names idss proc-bodies letrec-body))
      (letrec-exp (ids rhss body)
        (reduce-letrec-redex ids rhss body))
      (cond-exp 
       (tests results)
       (cond 
         ((null? tests) (const-exp 0))
         ((step-once (car tests)) =>
          (lambda (new-test) (cond-exp (cons new-test (cdr tests)) results)))
         (else (reduce-cond-redex tests results))))
      
      (car-exp (l)
               (cond 
                 ((step-once l) => (lambda (x) (car-exp x))) 
                 (else (reduce-car-redex l)))) 
      (cdr-exp (l)
               (cond 
                 ((step-once l) => (lambda (x) (cdr-exp x)))
                 (else (reduce-cdr-redex l))))
      (nil-exp () #f)
      (nil-test-exp (l)
              (cond ((step-once l) => (lambda (x) (nil-test-exp x))) 
                    (else (reduce-nil-test-redex l))))
      (cons-exp (l1 l2)
       (cond  ((step-once l1) => (lambda (x) (cons-exp x l2)))
              ((step-once l2) => (lambda (x) (cons-exp l1 x)))
              (else #f))) 
 
      )))

(define step-once-list
  (lambda (exps)
    (cond
      ((null? exps) #f)                 ; the empty list can't take a step
      ((step-once (car exps))
       => (lambda (exp1) (cons exp1 (cdr exps))))
      ((step-once-list (cdr exps))
       => (lambda (new-exps) (cons (car exps) new-exps)))
      (else #f))))


