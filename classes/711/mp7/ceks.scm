;;; threads/ceks.scm

(load "lang.scm")

;;; ceks machine for the base language + implicit store ops
;;; + lists + thread ops

(let ((time-stamp "Time-stamp: <2003-10-25 10:32:20 wand>"))
  (eopl:printf
   "threads/ceks.scm ~a~%"
   (substring time-stamp 13 29)))

;;;;;;;;;;;;;;;; top level ;;;;;;;;;;;;;;;;

(define run
  (lambda (string)
    (reduce-to-value-program (scan&parse string))))

(define reduce-to-value-program
  (lambda (pgm)
    (initialize-trace)
    (cases program pgm
      (a-program (exp)
                 (reduce-to-value exp
                                  (empty-env)
                                  (main-thread-initial-continuation)
                                  (initial-store))))))

(define *trace* #f)                     ; default tracing off
(define (toggle-trace) (set! *trace* (not *trace*)) *trace*)
(define *steps* 0)
(define (initialize-trace) (set! *steps* 0))

;; default tracing fcn.
;; Make this smarter to do selective tracing, etc.

;; this one doesn't work very well
(define trace-fcn
  (lambda l
    (if *trace* (pretty-print l))))

(define trace-fcn
  (lambda l
    (set! *steps* (+ 1 *steps*))
    (if #f
        (eopl:error 'trace-fn "step-count exceeded"))
    (if *trace* (eopl:printf "steps: ~s~%" *steps*))))


;;;;;;;;;;;;;;;; contexts ;;;;;;;;;;;;;;;;

(define-datatype context context?
                 
                 (yield-context)                       ; []
                 
                 (set-final-answer-context             ; set the final answer
                  (cxt context?))
                 
                 (if-test-context                      ; E o (if [] e1.r e2.r)
                  (then-exp expression?)
                  (else-exp expression?)
                  (env      environment?)
                  (cxt      context?))
                 (app-rator-context                    ; E o ap([] e2.r ... en.r)
                  (rands (list-of expression?))
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

;;;;;;;;;;;;;;;; threads ;;;;;;;;;;;;;;;;

(define-datatype thread thread?
                 (a-thread
                  (tid number?)
                  (val expval?)
                  (cxt context?)))

;;;;;;;;;;;;;;;; the simulator ;;;;;;;;;;;;;;;;

;; reduce-to-value : exp * env * cxt * store -> final value

(define reduce-to-value
  (lambda (exp env cxt store)
    (trace-fcn 'reduce-to-value exp env cxt store)
    
    (cases expression exp
      
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
               (apply-context (deref store (apply-env env id)) cxt store))
      (proc-exp (ids body)
                (apply-context (closure-val ids body env) cxt store))
      (app-exp (rator rands)
               (reduce-to-value rator env
                                (app-rator-context rands env cxt)
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

;; apply-context : expval * cxt -> final value

;; first, check to see that there is time left on the current thread's
;; counter.  If not, put the current thread on the ready queue, then grab
;; another thread from the ready queue and restart it.  Otherwise,
;; continue with the current thread.

(define apply-context
  (lambda (val cxt store)
    (trace-fcn 'apply-context val cxt store)
    
    (if (zero? (store-get-timer store))
        
        (yield
         (store-enqueue-thread store
                               (a-thread (store-get-tid store) val cxt)))
        
        (let ((store (store-decrement-timer store)))
          (cases context cxt
            
            ;; throw away the current thread and try another
            (yield-context () (yield store))
            
            (set-final-answer-context (cxt)
                                      (apply-context (bool-val #t) cxt
                                                     (store-set-final-answer store val)))
            
            (if-test-context (then-exp else-exp env cxt)
                             (reduce-to-value
                              (reduce-if-redex val then-exp else-exp)
                              env cxt store))
            (app-rator-context (rands env cxt)
                               (reduce-expressions-to-value rands env
                                                            (app-rands-context val cxt)
                                                            store))
            (car-exps-context (exps env lcxt)
                              (reduce-expressions-to-value exps env
                                                           (cdr-exps-context val lcxt)
                                                           store))
            (rhs-set-context (loc cxt)
                             (apply-context
                              (num-val 1)
                              cxt
                              (setref store loc val)))
            
            )))))


;; yield : store -> answer

;; give up on the current thread.  Instead, try to grab a thread from
;; the ready queue and run it.  If there are no ready threads, then
;; terminate the computation.

(define yield
  (lambda (store)
    (let ((q (store-get-queue store)))
      (if (queue-empty? q)
          (finalize store)
          (queue-dequeue q
                         (lambda (thrd new-queue)
                           (cases thread thrd
                             (a-thread (tid val cxt)
                                       (apply-context val cxt
                                                      (store-reset-timer
                                                       (store-set-tid tid
                                                                      (store-set-queue new-queue store))))))))))))

(define main-thread-initial-continuation
  (lambda ()
    (set-final-answer-context
     (yield-context))))

(define finalize
  (lambda (store)
    (eopl:pretty-print (deref store output-location)) 
    (newline)
    (store-get-final-answer store)))

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
                           (else (eopl:error 'value-of-expression
                                             "bad rator ~s"
                                             proc))))
      
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


(define t-get-tid 
  (lambda (t) (cases thread t
                (a-thread (tid x y)
                          tid))))

(define apply-effect
  (lambda (eff vals cxt store)
    (trace-fcn 'apply-effect eff vals cxt store)
    
    (cases effect eff
      
      ;; print prints all its values, as a list.
      
      (print-effect ()
                    (apply-context (num-val 1) cxt
                                   (store-append-to-stdout vals store)))
      
      (lock-effect ()
                   (let* ((newl (lock #f
                                      '()))
                          (ll (next-location store))
                          (new-store (adjoin-to-store store newl)))
                     (apply-context (lock-val ll) cxt new-store)))  
      
      
      (acquire-effect () 
                      (cases  expval (car vals)
                        (lock-val (l)
                                  (let ((lck (deref store l)))
                                    (cases lockt lck
                                      (lock (t q)
                                            (if t
                                                (if (equal? (t-get-tid t) (store-get-tid store))
                                                    (eopl:error "you already own that lock")
                                                    (let* ((new-q (queue-enqueue  q (a-thread (store-get-tid store) (num-val 0) cxt)))
                                                          (new-l (lock t new-q))
                                                          (new-store (setref store l new-l) ))
                                                      (yield
                                                       new-store)
                                                      ))
                                                (let* ((new-l (lock (a-thread (store-get-tid store) (num-val 0) cxt )q))
                                                       (new-store (setref store l new-l)))
                                                  (apply-context (num-val 0) cxt new-store))
                                                ))
                                      (else (eopl:error "how did this happen?")))))
                        (else 
                         (eopl:error "not a lock"))
                        ))
      (release-effect () 
                      (cases  expval (car vals)
                        (lock-val (l)
                                  (let ((lck (deref store l)))
                                    (cases lockt lck
                                      (lock (t q)
                                            (if t
                                                (if (not (equal? (t-get-tid t) (store-get-tid store)))
                                                    (eopl:error "you don't own that lock")
                                                    (if (null? q)
                                                        (let* ((new-l (lock #f '()))
                                                               (new-store (setref store l new-l))
                                                               )
                                                          (apply-context (num-val 0) cxt new-store))
                                                        (queue-dequeue 
                                                         q 
                                                         (lambda (new-t new-q)
                                                           (let* ((new-l (lock new-t new-q))
                                                                  (new-store (setref store l new-l) )
                                                                  (new-new-store (store-enqueue-thread new-store new-t))) 
                                                             (apply-context (num-val 0) cxt new-new-store)
                                                             ))
                                                         )))
                                                (eopl:error "lock unowned")
                                                ))
                                      (else (eopl:error "how did this happen?")))))
                        (else 
                         (eopl:error "not a lock"))
                        ))
      
      ;; Create a new thread. Pass the parent's tid to the child as
      ;; its first and only argument, and place this new thread on the
      ;; ready queue.  Then return the child's tid to the parent.
      
      (spawn-effect () 
                    (let ((proc (car vals))
                          (parent-tid (store-get-tid store)))
                      (store-allocate-tid store
                                          (lambda (child-tid store)
                                            (apply-context
                                             (num-val child-tid)
                                             cxt
                                             (store-enqueue-thread store
                                                                   (a-thread
                                                                    child-tid
                                                                    (tid-val parent-tid)
                                                                    (car-exps-context '() (empty-env) 
                                                                                      (app-rands-context
                                                                                       proc
                                                                                       (yield-context))))))))))))) 


