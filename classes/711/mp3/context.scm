;;; base/context.scm

;; context-passing interpreter for base language

(let ((time-stamp "Time-stamp: <2003-09-18 23:20:40 wand>"))
  (eopl:printf
    "base/context.scm ~a~%"
    (substring time-stamp 13 29)))

;;;;;;;;;;;;;;;; top level ;;;;;;;;;;;;;;;;

(define run
  (lambda (string)
    (reduce-to-value-program (scan&parse string))))

(define reduce-to-value-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp)
        (reduce-to-value
          (a-config exp (empty-context)))))))

;; reduce-to-value : closed-expression -> closed-value
(define reduce-to-value
  (lambda (config)
    (if *trace* (pretty-print exp))
    (cond
      ((step-once config) => reduce-to-value)
      (else                             ; keep only the exp
        (cases configuration config
          (a-config (exp cxt)
            (cases context cxt          ; make sure context is empty
              (empty-context () exp)
              (else
                (eopl:error 'reduce-to-value
                  "reduce-to-value terminated with non-empty context ~s"
                  config)))))))))
      
(define *trace* #f)                     ; default tracing off
(define (toggle-trace) (set! *trace* (not *trace*)) *trace*)

;;;;;;;;;;;;;;;; configurations ;;;;;;;;;;;;;;;;

(define (either pred1 pred2) (lambda (v) (or (pred1 v) (pred2 v))))

(define-datatype configuration configuration?
  (a-config
    (exp expression?)
    (cxt context?)))

(define-datatype list-config list-config?
  (a-list-config
    (exps (list-of expression?))
    (cxt list-context?)))

(define-datatype context context?
  (empty-context)                       ; represents hole


  (if-test-context                      ; represents E[(if [] e1 e2)]
    (then-exp expression?)
    (else-exp expression?)
    (cxt context?))

  (app-rator-context                    ; represents E[([] e1 ... en)]
    (rands (list-of expression?))
    (cxt context?))
  
  (car-of-exps-context                  ; represents E[([],e1,..,en)]
    (exps (list-of expression?))
    (list-cxt list-context?))           ; note list-context? 

  )

;; a context that expects a LIST of values, represented as [*]

(define-datatype list-context list-context?

  (primapp-rands-list-context            ; represents E[p([*])]
    (prim primitive?)
    (cxt context?))

  (let-rhss-list-context                ; represents E[(let ids [*] body)]
    (ids (list-of symbol?))
    (body expression?)
    (cxt context?))

  (app-rands-list-context               ; represents E[(v [*])]
    (rator expression?)
    (cxt context?))


  (cdr-of-exps-list-context             ; represents E[(v,[*])]
    (val expression?)
    (list-cxt list-context?))

)

;;;;;;;;;;;;;;;; the stepper ;;;;;;;;;;;;;;;;

;; step-once : closed expression -> (optional closed expression)
;; reduces by one step, else returns #f
;;
(define step-once
  (lambda (config)
    (cases configuration config
      (a-config (exp cxt)
        (let ((pop (lambda () (try-next exp cxt))))
          (cases expression exp
            (const-exp (n) (pop))

            (primapp-exp (prim rands)
              (step-once-list
                (a-list-config rands (primapp-rands-list-context prim cxt))))

            (true-exp () (pop))
            (false-exp () (pop))
            (if-exp (e0 e1 e2)
              (step-once
                (a-config e0 (if-test-context e1 e2 cxt))))

            (var-exp (id)
              (eopl:error 'step-once "non-closed expression ~s" exp))
            (proc-exp (id body) (pop))
            (app-exp (rator rands)
              (step-once
                (a-config rator (ap-rator-context rands cxt))))

            (let-exp (ids rhss body)
              (step-once-list
                (a-list-config rhss (let-rhss-list-context ids body cxt))))

            (letrec-exp (ids rhss body)
              (a-config
                (reduce-letrec-redex ids rhss body)
                cxt))
            ))))))

;; step-once-list :: list-config -> optional-config  (hmm...)
(define step-once-list
  (lambda (l-config)
    (cases list-config l-config
      (a-list-config (exps list-cxt)
        (cond
          ((null? exps) (try-next-list '() list-cxt) )
          (else
            (step-once
             (a-config
               (car exps)
               (car-of-exps-context (cdr exps) cxt)))))))))

;; try-next :: closed value * context -> optional closed config
;; (try-next v E) = (old-step-once E[v])
;; works by unwinding E one step and calling step-once or
;; step-once-list again

(define try-next
  (lambda (val cxt)
    (cases context cxt
      (empty-context () #f)
      (if-test-context (e1 e2 cxt)          ; ok, ready to reduce
        (a-config
          (reduce-if-redex val e1 e2)
          cxt))
      (app-rator-context (rands cxt)
        (step-once-list
          (a-list-config rands (app-rands-list-context val cxt))))
      (car-of-exps-context (exps list-cxt)
        (step-once-list
          (a-list-config exps (cdr-of-exps-list-context val list-cxt))))
      )))
      

(define try-next-list
  (lambda (vals list-cxt)
    (cases list-context list-cxt

      (primapp-rands-list-context (prim cxt)
        ;; ok, ready to take a step
        (a-config
          (reduce-delta-redex prim vals)
          cxt))

      (let-rhss-list-context (ids body cxt)
        (a-config
          (reduce-let-redex ids vals body)
          cxt))

      (app-rands-list-context (rator cxt)
        (a-config
          (reduce-beta-redex rator vals)
          cxt))
      
      (cdr-of-exps-list-context (val cxt)
        (try-next-list 
          (cons val vals)               ; a list of values, so call
                                        ; try-next-list 
          cxt))
      )))
