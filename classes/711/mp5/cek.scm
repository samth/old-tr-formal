;;; base/cek.scm

;;; cek machine for the base language

(let ((time-stamp "Time-stamp: <2003-10-08 11:37:01 wand>"))
  (eopl:printf
   "base/cek.scm ~a~%"
   (substring time-stamp 13 29)))

(load  "env-lang.scm")

;;; test with (run-all)
;;; toggle tracing with (toggle-trace)

;;;;;;;;;;;;;;;; top level ;;;;;;;;;;;;;;;;

(define run
  (lambda (string)
    (reduce-to-value-program (scan&parse string))))

(define reduce-to-value-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp)
                 (reduce-to-value (try-exp exp (const-exp 99)) (empty-env) (empty-context))))))

(define *trace* #f)                     ; default tracing off
(define (toggle-trace) (set! *trace* (not *trace*)) *trace*)

;;;;;;;;;;;;;;;; contexts ;;;;;;;;;;;;;;;;

(define-datatype context context?
                 (empty-context
                  )                       ; []
                 (if-test-context                      ; E o (if [] e1.r e2.r)
                  (then-exp expression?)
                  (else-exp expression?)
                  (env      environment?)
                  (cxt      context?))
                 (cond-context                         ; E o (cond [] => e1.r ... en.r => en+1.r)
                  (result expression?)
                  (more-tests (list-of expression?))
                  (more-results (list-of expression?))
                  (env environment?)
                  (cxt context?))
                 (app-rator-context                    ; E o ap([] e2.r ... en.r)
                  (rands (list-of expression?))
                  (env environment?)
                  (cxt context?))
                 (reduce-car-exps-context                ; EL o ([], e2.r ... en.r)
                  (exps (list-of expression?))
                  (env  environment?)
                  (lcxt list-context?))
                 (try-context                      ; E o try [] catch e
                  (handler expression?)
                  (env environment?)
                  (cxt context?))
                 )

(define-datatype list-context list-context?
                 (prim-rands-context                   ; E circ p([*])
                  (prim primitive?)
                  (cxt  context?))
                 (app-rands-context                    ; E circ ap(v [*])
                  (proc expval?)
                  (cxt  context?))
                 (let-rands-context                    ; E circ (let xs = [*] in e).r
                  (ids  (list-of symbol?))
                  (body expression?)
                  (env  environment?)
                  (cxt  context?))
                 (reduce-cdr-exps-context                ; EL circ (v, [*])
                  (val expval?)
                  (lcxt list-context?))
                 )

;;;;;;;;;;;;;;;; the simulator ;;;;;;;;;;;;;;;;

;; reduce-to-value : exp * env * cxt -> final value

(define reduce-to-value
  (lambda (exp env cxt)
    (cases expression exp
      
      (try-exp (body handler)
               (reduce-to-value body env 
                                (try-context handler env cxt)))
      
      (error-exp ()
                 (apply-context (error-val) cxt))
      
      (const-exp (n) (apply-context (num-val n) cxt))
      (primapp-exp (prim rands)
                   (reduce-expressions-to-value rands env
                                                (prim-rands-context prim cxt)))
      
      (true-exp () (apply-context (bool-val #t) cxt))
      (false-exp ()(apply-context (bool-val #f) cxt))
      (if-exp (test-exp then-exp else-exp)
              (reduce-to-value test-exp env
                               (if-test-context then-exp else-exp env cxt)))
      
      (cond-exp (tests results)
                (if (null? tests)
                    (reduce-to-value (const-exp 0) env cxt)
                    (reduce-to-value 
                     (car tests) env
                     (cond-context (car results) (cdr tests) (cdr results) env cxt))))
      
      (var-exp (id)
               (apply-context (apply-env env id) cxt))
      (proc-exp (ids body)
                (apply-context (closure-val ids body env) cxt))
      (app-exp (rator rands)
               (reduce-to-value rator env (app-rator-context rands env cxt)))
      
      (let-exp (ids rhss body)
               (reduce-expressions-to-value
                rhss env (let-rands-context ids body env cxt)))
      
      ; this is all the code for let* - we just macro-expand
      (let*-exp (ids rhss body)
                (if (null? ids) (reduce-to-value (let-exp '() '() body) env cxt)
                    (reduce-to-value (let-exp (list (car ids))
                                              (list (car rhss))
                                              (let*-exp (cdr ids)
                                                        (cdr rhss)
                                                        body)) env cxt)))
      
      
      (letrec-exp (proc-names idss proc-bodies letrec-body)
                  (reduce-to-value
                   letrec-body
                   (extend-env-recursively proc-names idss proc-bodies env)
                   cxt))
      )))


;; reduce-expressions-to-value
;;     : (list-of exp) * env * list-context -> final value

(define reduce-expressions-to-value
  (lambda (exps env lcxt)
    (if (null? exps)
        (apply-list-context '() lcxt)
        (reduce-to-value (car exps) env
                         (reduce-car-exps-context (cdr exps) env lcxt)))))


(define (error-val? v)
  (cases expval v
    (error-val ()
               #t)
    (else #f)))

(define (get-outer-context lcxt)
  (cases list-context lcxt
    (prim-rands-context (p cxt)
                        cxt)
    (app-rands-context (p cxt)
                       cxt)
    (let-rands-context (i b e cxt)
                       cxt)
    (reduce-cdr-exps-context (v lcxt)
                             (get-outer-context lcxt))))

;; apply-context : expval * cxt -> final value

(define apply-context
  (lambda (val cxt)
    
    (cases context cxt
     
      (empty-context () val) ; nothing to do, this is the final value
      
      (if-test-context (then-exp else-exp env cxt)
                       (if (error-val? val) (apply-context val cxt)
                           (reduce-to-value
                            (reduce-if-redex val then-exp else-exp)
                            env
                            cxt)))
      (cond-context (result mt mr env cxt)
                    (if (error-val? val) (apply-context val cxt)
                        (reduce-to-value
                         (reduce-cond-redex val
                                            result
                                            mt 
                                            mr)
                         env
                         cxt)))
      (app-rator-context (rands env cxt)
                         (if (error-val? val) (apply-context val cxt)
                             (reduce-expressions-to-value rands env (app-rands-context val cxt))))
      
      (try-context (handler env cxt)
                   (if (error-val? val) (reduce-to-value handler env cxt)
                       val))
      
      (reduce-car-exps-context (exps env lcxt)
                               (if (error-val? val) (apply-context val (get-outer-context lcxt))
                                   (reduce-expressions-to-value exps env 
                                                                (reduce-cdr-exps-context val lcxt))))
      )))


;; apply-list-context : (list-of expval) * list-context -> final value

(define apply-list-context
  (lambda (vals lcxt)
    (cases list-context lcxt
      (prim-rands-context (prim cxt)
                          (apply-context
                           (reduce-delta-redex prim vals)
                           cxt))
      (app-rands-context (proc cxt)
                         (cases expval proc
                           (closure-val (bvars body saved-env)
                                        (reduce-to-value
                                         body
                                         (extend-env bvars vals saved-env)
                                         cxt))
                           (else (apply-context (error-val) cxt))))
      (let-rands-context (ids body env cxt)
                         (reduce-to-value
                          body
                          (extend-env ids vals env)
                          cxt))
      (reduce-cdr-exps-context (val lcxt)
                               (apply-list-context
                                (cons val vals)
                                lcxt))
      )))

