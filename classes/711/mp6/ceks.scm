;;; mutable-pairs/ceks.scm

;;; ceks machine for the base language + implicit store ops
;;; + mutable pairs

(let ((time-stamp "Time-stamp: <2003-10-05 12:57:15 wand>"))
  (eopl:printf
    "mutable-pairs/ceks.scm ~a~%"
    (substring time-stamp 13 29)))

;;; requires lang.scm and store{1,2}.scm and mutable-pairvals{1,2}.scm
;;; test with (run-all)
;;; toggle tracing with (toggle-trace)

(load "lang.scm")
(load "store1.scm")
(load "pairval2.scm")
(load "array.scm")

;;;;;;;;;;;;;;;; top level ;;;;;;;;;;;;;;;;

(define run
  (lambda (string)
    (reduce-to-value-program (scan&parse string))))

(define reduce-to-value-program
  (lambda (pgm)
    (initialize-trace)
    (cases program pgm
      (a-program (exp)
        (reduce-to-value (cp-exp exp (const-exp 99))
          (empty-env)
          (empty-context)
          (empty-store))))))

(define *steps* 0)

(define *trace* #f)                     ; default tracing off
(define (toggle-trace) (set! *trace* (not *trace*)) *trace*)
(define (initialize-trace) (set! *steps* 0))

;; default tracing fcn.
;; Make this smarter to do selective tracing, etc.

;; this one doesn't work very well
(define trace-fcn
  (lambda l
    (if *trace* (eopl:pretty-print l))))

(define trace-fcn
  (lambda l
    (set! *steps* (+ 1 *steps*))
    (if (> *steps* 1000)
      (eopl:error 'trace-fn "step-count exceeded"))
    (if *trace* (eopl:printf "steps: ~s~%" *steps*))))


;;;;;;;;;;;;;;;; contexts ;;;;;;;;;;;;;;;;

(define-datatype context context?
  (empty-context)                       ; []
  (if-test-context                      ; E o (if [] e1.r e2.r)
    (then-exp expression?)
    (else-exp expression?)
    (env      environment?)
    (cxt      context?))
  (app-rator-context                    ; E o ap([] e2.r ... en.r)
    (rands (list-of expression?))
    (env environment?)
    (cxt context?))
  (cp-context                     ; E o checkpoint [] handle e
   (handler expression?)
   (env environment?)
   (cxt context?)
   (store (lambda l #t)))  
  (try-context                     ; E o try [] handle e
   (handler expression?)
   (env environment?)
   (cxt context?)
   )
  (begin-context                  ; E o begin [] e2 .. en end
   (more (list-of expression?))
   (env environment?)
   (cxt context?))
  (car-exps-context                ; EL o ([], e2.r ... en.r)
    (exps (list-of expression?))
    (env  environment?)
    (lcxt list-context?))
  ;; new for implicit-store
  (rhs-set-context                      ; E o (set l [])
    (loc location?)
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
  (cdr-exps-context                     ; EL circ (v, [*])
    (val expval?)
    (lcxt list-context?))
  (effect-rands-context                 ; E circ eff([*])
    (eff effect?)
    (cxt context?))
  )

;;;;;;;;;;;;;;;; the simulator ;;;;;;;;;;;;;;;;

;; reduce-to-value : exp * env * cxt * store -> final value

(define reduce-to-value
  (lambda (exp env cxt store)
    (trace-fcn 'reduce-to-value exp env cxt store)
    
    ;(eopl:pretty-print exp)
    
    (cases expression exp
      (error-exp () (apply-context (error-val) cxt store))
      (const-exp (n) (apply-context (num-val n) cxt store))
      (primapp-exp (prim rands)
        (reduce-expressions-to-value
          rands env
          (prim-rands-context prim cxt)
          store))

      (true-exp ()  (apply-context (bool-val #t) cxt store))
      (false-exp () (apply-context (bool-val #f) cxt store))
      (if-exp (test-exp then-exp else-exp)
        (reduce-to-value test-exp env
          (if-test-context then-exp else-exp env cxt)
          store))

      (var-exp (id)
               (begin
                 ;(eopl:pretty-print store)
                 (apply-context (deref store (apply-env env id)) cxt store)))
      (proc-exp (ids body)
        (apply-context (closure-val ids body env) cxt store))
      (app-exp (rator rands)
        (reduce-to-value rator env
          (app-rator-context rands env cxt)
          store))

      (cp-exp (body handler)
              (reduce-to-value body env
                              (cp-context handler env cxt (copy-store store))
                              store))
      
      (try-exp (body handler)
              (reduce-to-value body env
                              (try-context handler env cxt) 
                              store))
      
      
      (let-exp (ids rhss body)
        (reduce-expressions-to-value
          rhss
          env
          (let-rands-context ids body env cxt)
          store))

      (letrec-exp (proc-names idss proc-bodies letrec-body)
        (reduce-letrec proc-names idss proc-bodies letrec-body
          env cxt store))

      (begin-exp (exps)
                 (cond 
                   ((null? exps) (reduce-to-value (const-exp 0) env cxt store))
                   (else (reduce-to-value (car exps) env (begin-context (cdr exps) env cxt) store))))
      
      (varassign-exp (lhs rhs)
        (reduce-to-value
          rhs
          env
          (rhs-set-context
            (apply-env env lhs)
            cxt)
          store))

      (effect-exp (eff exps)
        (reduce-expressions-to-value
          exps env
          (effect-rands-context eff cxt)
          store))

      )))


;; reduce-expressions-to-value
;;     : (list-of exp) * env * list-context -> final value

(define reduce-expressions-to-value
  (lambda (exps env lcxt store)
    (trace-fcn 'reduce-expressions-to-value exps env lcxt store)

    (if (null? exps)
      (apply-list-context '() lcxt store)
      (reduce-to-value
        (car exps) env
        (car-exps-context (cdr exps) env lcxt)
        store))))
        

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
    (effect-rands-context (e cxt)
                           cxt)
    (cdr-exps-context (v lcxt)
                             (get-outer-context lcxt))))


;; apply-context : expval * cxt -> final value

(define apply-context
  (lambda (val cxt store)
    (trace-fcn 'apply-context val cxt store)

    (cases context cxt

      (empty-context () val) ; nothing to do, this is the final value

      (cp-context (handler env cxt2 old-store)
                  (if (error-val? val) (reduce-to-value handler env cxt2 old-store)
                      val))

      (try-context (handler env cxt2)
                   
                   (if (error-val? val) 
                       (begin
                         ;(eopl:pretty-print store)
                         (reduce-to-value handler env cxt2 store))
                       val))
      
      (begin-context (more-exps env cxt)
                     (cond ((error-val? val) (apply-context val cxt store))
                           ((null? more-exps) (apply-context val cxt store))
                           (else (reduce-to-value (car more-exps) env (begin-context (cdr more-exps) env cxt) store))))
      
      (if-test-context (then-exp else-exp env cxt)
                       (if (error-val? val) (apply-context val cxt store)
                           (reduce-to-value
                            (reduce-if-redex val then-exp else-exp)
                            env cxt store)))
      (app-rator-context (rands env cxt)
                         (if (error-val? val) (apply-context val cxt store)
                             (reduce-expressions-to-value rands env
                                                          (app-rands-context val cxt)
                                                          store)))

      (car-exps-context (exps env lcxt)
                        (if (error-val? val) 
                            (apply-context val 
                                           (get-outer-context lcxt) store)
                            (reduce-expressions-to-value exps env
                                                         (cdr-exps-context val lcxt)
                                                         store)))

      (rhs-set-context (loc cxt)
                       (if (error-val? val) (apply-context val cxt store)
                           (apply-context
                            (num-val 1)
                            cxt
                            (setref store loc val))))
                       
      )))


;; apply-list-context : (list-of expval) * list-context -> final value

(define apply-list-context
  (lambda (vals lcxt store)
    (trace-fcn 'apply-list-context vals lcxt store)

    (cases list-context lcxt
      (prim-rands-context (prim cxt)
        (apply-context
          (reduce-delta-redex prim vals)
          cxt
          store))
      (app-rands-context (proc cxt)
        (cases expval proc
          (closure-val (bvars body saved-env)
            (reduce-in-new-scope body bvars vals saved-env cxt store))
          (else (apply-context (error-val) cxt store))))

      (let-rands-context (ids body env cxt)
        (reduce-in-new-scope body ids vals env cxt store))
      
      (cdr-exps-context (val lcxt)
        (apply-list-context
          (cons val vals)
          lcxt store))

      (effect-rands-context (eff cxt)
        (apply-effect eff vals cxt store))

      )))

(define reduce-in-new-scope
  (lambda (exp ids vals env cxt store)
    (let ((new-locs (iota2 (next-location store) (length ids))))
      (let ((new-env (extend-env ids new-locs env))
            (new-store (adjoin-many-to-store store vals)))
        (reduce-to-value exp new-env cxt new-store)))))

;; produce (start start+1 ... start+number)
(define iota2
  (lambda (start number)
    (if (zero? number)
      '()
      (cons start (iota2 (+ start 1) (- number 1))))))

(define reduce-letrec
  (lambda (proc-names idss proc-bodies letrec-body env cxt store)
    (let* ((new-locs
            (iota2 (next-location store) (length proc-names)))
           (new-env (extend-env proc-names new-locs env))
           (new-store
              (adjoin-many-to-store store
                (map
                  (lambda (ids proc-body)
                    (closure-val ids proc-body new-env))
                  idss proc-bodies))))
        (reduce-to-value letrec-body new-env cxt new-store))))

(define apply-effect
  (lambda (eff vals cxt store)
    (trace-fcn 'apply-effect eff vals cxt store)
    


    (cases effect eff

      (pair-effect ()
        (new-pair (car vals) (cadr vals) store
          (lambda (p new-store)
            (apply-context (pair-val p) cxt new-store))))


      (left-effect ()
        (cases expval (car vals)
          (pair-val (p)
            (apply-context
              (left p store)
              cxt
              store))
          (else (error-val))))

      (setleft-effect ()
        (cases expval (car vals)
          (pair-val (p)
            (apply-context
                  (num-val 13)
                  cxt
                  (setleft p (cadr vals) store)))
          (else (error-val))))

      (right-effect ()
        (cases expval (car vals)
          (pair-val (p)
            (apply-context
              (right p store)
              cxt
              store))
          (else (error-val))))

      (setright-effect ()
        (cases expval (car vals)
          (pair-val (p)
            (apply-context
                  (num-val 13)
                  cxt
                  (setright p (cadr vals) store)))
          (else (error-val))))

      (array-effect ()
                    (cases expval (car vals)
                      (num-val (n)
                               (new-array n store
                                          (lambda (p ns)
                                            (apply-context (array-val p) cxt ns))))
                      (else (error-val))))
                               
      
      (arrayset-effect () 
                       (let ((arr (car vals))
                             (n (cadr vals))
                             (val (caddr vals)))
                         (cases expval arr
                           (array-val (p)
                                      (cases expval n
                                        (num-val (m)
                                                 (apply-context (num-val -1)
                                                                cxt
                                                                (arrayset p m val store)))
                                        (else (error-val)))
                                      ) 
                           (else (error-val)))))
      (arrayref-effect () 
                       (cases expval (car vals)
                         (array-val (p)
                                    (cases expval (cadr vals)
                                      (num-val (n)
                                               (apply-context
                                                (arrayref p n store)
                                                cxt 
                                                store))
                                      (else (error-val))))
                         (else (error-val))))

      )))


(define (deepcopy-vector v)
  (list->vector (map (lambda (x) (if (vector? x) (deepcopy-vector x) x)) (vector->list v))))

(define (copy-store store)
  (if (list? store) store
      (deepcopy-vector store)))