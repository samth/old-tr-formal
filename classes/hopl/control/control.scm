
  ;; shift/reset Danvy/Filinski 90
  ;; This code copied from scheme48 and Sperber's ICFP '02 paper
  
  (require (lib "defmacro.ss"))
  (require (lib "errortrace.ss" "errortrace"))


  
  (define-syntax reset
    (syntax-rules ()
      ((_ ?e) (*reset (lambda () ?e)))))
  
  (define-syntax shift
    (syntax-rules ()
      ((_ ?k ?e) (*shift (lambda (?k) ?e)))))
  
  (define *meta-continuation*
    (lambda (v)
      (error "You forgot the top-level reset...")))
  
  (define *abort
    (lambda (thunk)
      (let ((val (thunk)))
        (*meta-continuation* val))))
  
  (define null-continuation #f)
  
  (define *reset
    (lambda (thunk)
      (let ((mc *meta-continuation*))
        (call/cc
         (lambda (k)
           (begin
             (set! *meta-continuation*
                   (lambda (v)
                     (set! *meta-continuation* mc)
                     (k v)))
             (*abort thunk)))))))
  
  (define *shift
    (lambda (f)
      (call/cc
       (lambda (k)
         (*abort (lambda ()
                   (f (lambda (v)
                        (reset (k v))))))))))
  
  ;; splitter
  
  
  (define stack-of-marker '())
  
  (define (splitter f)
    (let ((marker '())
          (v '())
          (topmarker '())
          )
      (set! v
            (call/cc
             (lambda (kk)
               (set! marker (cons kk '()))
               (set! stack-of-marker
                     (cons marker stack-of-marker))
               (let ((v (f
                         (make-abort marker)
                         (make-call/pc marker))))
                 (set-car! (car stack-of-marker) '())
                 v))
             ))
      (if (not (null? (caar stack-of-marker)))
          ;;Someone did (kk thunk)
          (begin
            (obsolete-stack! marker)
            (set! v (v))
            (set-car! (car stack-of-marker)
                      '())))
      (set! topmarker (car stack-of-marker))
      (set! stack-of-marker (cdr stack-of-marker))
      (cond
        ((null? (cdr topmarker)) v)
        (else ((cdr topmarker) v)))))
  
  (define (make-abort marker)
    (lambda (thunk)
      (if (null? (car marker))
          (error "obsolete splitter")
          ((car marker) thunk))))
  
  (define (make-call/pc marker)
    (lambda (g)
      (if (null? (car marker))
          (error "out of extent")
          (call/cc
           (lambda (kj)
             (g (make-pc kj marker)))))))
  
  (define (make-pc kj marker)
    (let ((slice (marker-prefix
                  stack-of-marker
                  marker)))
      (lambda (v)
        (call/cc
         (lambda (kc)
           (set! stack-of-marker
                 (append slice
                         (cons (cons #t kc)
                               stack-of-marker)))
           (kj v))))))
  
  (define (marker-prefix l m)
    (if (eq? (car l) m)
        '()
        (cons (cons #t (cdar l))
              (marker-prefix (cdr l) m))))
  
  (define (obsolete-stack! marker)
    (if (eq? (car stack-of-marker) marker)
        marker
        (begin (set-car! (car stack-of-marker)
                         '())
               (set! stack-of-marker
                     (cdr stack-of-marker))
               (obsolete-stack! marker))))
  
  ;; sigma by felix
  
  (define-syntax sigma
    (syntax-rules ()
      [(sigma "transit" () (V1 V2 ...) (SET!1 SET!2 ...) EXP)
       (lambda (V1 V2 ...) SET!1 SET!2 ... EXP)]
      [(sigma "transit" (X1 X2 ...) (V4 ...) (SET!4 ...) EXP)
       (sigma "transit" (X2 ...) (V4 ... V1) ((set! X1 V1) SET!4 ...) 
              EXP)]
      [(sigma (X1 X2 ...) EXP)
       (sigma "transit" (X1 X2 ...) () () EXP)]))
  
  (define-syntax *set!
    (syntax-rules ()
      [(_ ([x exp] ...) body ...)
       ((sigma (x ...) body ...) exp ...)]))
  
  (define run*-stack '())
  
  (define run*
    (lambda (th)
      (let* ([run-cont 'any]
             [v (call/cc (sigma (run-cont)
                                (*set! ([run*-stack (cons (cons run-cont '()) run-stack)])
                                       th)))]
             [top-frame (car run*-stack)]
             [top-run-cont (car top-frame)]
             [top-sub-stack (cdr top-frame)]
             )
        (cond
          [(not (null? top-sub-stack))
           (let ([k (car top-sub-stack)])
             (set-cdr! top-frame (cdr top-sub-stack))
             (k v))]
          [(not (eq? run-cont top-run-cont))
           (top-run-cont (lambda () v))]
          [else (*set! ([run*-stack (cdr run-stack)]) v)]
          )
        )))
  
  (define control*
    (lambda (f)
      (call/cc
       (lambda (control-cont)
         (let* ([control-frame (car run*-stack)]
                [control-run-cont (car control-frame)]
                [control-sub-stack (cdr control-frame)])
           (set-cdr! control-frame '())
           (control-run-cont
            (lambda ()
              (f (lambda (v)
                   (call/cc (lambda (invoke-cont)
                              (let* ([invoke-top-frame (car run*-stack)]
                                     [invoke-sub-stack (cdr invoke-top-frame)])
                                (set-cdr! invoke-top-frame
                                          (append control-sub-stack
                                                  (cons invoke-cont invoke-sub-stack)))
                                (control-cont v)))))))))))))
  
  
  (define old-run #f)
  (define old-control #f)
  
  (let ((old-run-stack '()))
    (set! old-run
          (lambda (thunk)
            (let ((old-rs old-run-stack))
              (begin0
                (splitter
                 (lambda (abort call/pc)
                   (define (cpc f)
                     (call/pc
                      (lambda (c)
                        (abort (lambda () (f c))))))
                   (set! old-run-stack (cons cpc old-run-stack))
                   (thunk)))
                (set! old-run-stack old-rs)))))
    (set! old-control (lambda (f) ((car old-run-stack) f) )) )
  
  (define-syntax old%
    (syntax-rules ()
      [(old% e ...) (old-run (lambda () e ...))]))
  
  (define-syntax abort
    (syntax-rules ()
      [(_ e) (old-control (lambda (dummy) e))]))
  
  (let ([g (old% (* 2 (old-control (lambda (k) k))))])
    (* 3 (old% (* 5 (abort (g 7))))))
  
  (define (spawn f)
    (define (mk-cpc curr-cpc curr-abort)
      (lambda (c)
        (curr-cpc
         (lambda (cc)
           (curr-abort
            (lambda ()
              (c (lambda (v)
                   (splitter
                    (lambda (na ncpc)
                      (set! curr-cpc ncpc)
                      (set! curr-abort na)
                      (cc v)))))))))))
    (splitter
     (lambda (abort call/pc)
       (f (mk-cpc call/pc abort)))))
  
  
  
  ;runf.ss
  ;Iswym in Scheme
  ;(c) Dorai Sitaram, Dec. 1992, Rice University
  ;Previous versions: Apr. 1991, Jan. 1992
  
  
  (define run-stack '())
  (define fcontrol-message "fcontrol-message")
  
  (defmacro record-evcase (tag . clauses)
    (if (not (or (symbol? tag) (boolean? tag)))
        `(let ((%tmp% ,tag))
           (record-evcase %tmp% ,@clauses))
        (if (null? clauses) `'any
            (let* ((clause (car clauses)) (clauses (cdr clauses))
                                          (tag2 (car clause)))
              (if (and (null? clauses) (eq? tag2 'else))
                  `(begin ,@(cdr clause))
                  (if (and (pair? tag2) (eq? (car tag2) 'either))
                      `(if (and (pair? ,tag)
                                (or ,@(map (lambda (tag3)
                                             `(eqv? (car ,tag) ,tag3))
                                           (cdr tag2))))
                           (apply (lambda ,@(cdr clause)) (cdr ,tag))
                           (record-evcase ,tag ,@clauses))
                      `(if (and (pair? ,tag) (eqv? (car ,tag) ,tag2))
                           (apply (lambda ,@(cdr clause)) (cdr ,tag))
                           (record-evcase ,tag ,@clauses))))))))
  
  
  (define system-run
    (lambda (th hdlr)
      (let* ((p 'void)
             (v (call/cc
                 (lambda (k)
                   (set! p k)
                   (set! run-stack
                         (cons (cons p '()) run-stack))
                   (th)))))
        (record-evcase v
                       (fcontrol-message (fctl-rcr fun-cont)
                                         (set! run-stack (cdr run-stack))
                                         (hdlr fctl-rcr fun-cont))
                       (else (let* ((frame2 (car run-stack))
                                    (p2 (car frame2))
                                    (substack2 (cdr frame2)))
                               (cond ((not (eq? p p2))
                                      (p2 v))
                                     ((not (null? substack2))
                                      (set-cdr! frame2 (cdr substack2))
                                      ((car substack2) v))
                                     (else (set! run-stack (cdr run-stack))
                                           v))))))))
  
  (define system-fcontrol
    (lambda (r)
      (call/cc
       (lambda (fctl-cont)
         (if (null? run-stack) (error 'no-surrounding-run))
         (let* ((fctl-frame (car run-stack))
                (fctl-p (car fctl-frame))
                (fctl-substack (cdr fctl-frame)))
	   (set-cdr! fctl-frame '())
	   (fctl-p
            (list fcontrol-message r
                  (lambda (v)
                    (call/cc
                     (lambda (invoke-cont)
                       (if (null? run-stack) (error 'no-surrounding-run))
                       (let* ((invoke-frame (car run-stack))
                              (invoke-substack (cdr invoke-frame)))
                         (set-cdr! invoke-frame
                                   (append fctl-substack
                                           (cons invoke-cont invoke-substack)))
                         (fctl-cont v))))))))))))
  
  (define flush-run-stack
    (lambda ()
      (set! run-stack '())))
  
  (define identity (lambda (x) x))
  (define compose (lambda (f g) (lambda (x) (f (g x)))))
  
  (define run-tagged
    (lambda (tag th h)
      (system-run th
                  (lambda (r k)
                    (let ((tag2 (car r))
                          (r2 (cadr r))
                          (k2 (compose k (caddr r))))
                      (if (eqv? tag2 tag) (h r2 k2)
                          (system-fcontrol (list tag2 r2 k2))))))))
  
  (define fcontrol-tagged
    (lambda (tag r)
      (system-fcontrol (list tag r identity))))
  
  (defmacro % (arg1 arg2 . rest)
    (if (null? rest)
        `(% #f ,arg1 ,arg2)
        `(run-tagged ,arg1 (lambda () ,arg2) ,(car rest))))
  
  (define run 
    (lambda (x y . z)
      (if (null? z) (run-tagged #f x y)
          (run-tagged x y (car z)))))
  
  (define fcontrol
    (lambda (x . z)
      (if (null? z) (fcontrol-tagged #f x)
          (fcontrol-tagged x (car z)))))
  
  
  ;; tests for splitter
  
  (splitter (lambda (a c) 'foo))
  ;; returns foo
  
  (splitter
   (lambda (ab cp)
     (cons (cp (lambda (c) (cons 'b (c (c 'd)))))
           'a)))
  
  (spawn
   (lambda (control)
     (cons (control (lambda (k) (cons 1 (k 4))))
           (control (lambda (k) (cons 2 (k 3)))))))
  ;;(1 2 4 . 3)
  
  (splitter
   (lambda (abort call/pc)
     (let ((control (lambda (func)
                      (call/pc (lambda (k) (abort (lambda () (func k))))))))
       (cons
        (control
         (lambda (k)
           (cons 1 (k 4))))
        (control
         (lambda (k)
           (cons 2 (k 3))))))))
  ;  (2 1 4 . 3)
  (splitter
   (lambda (abort call/pc)
     (cons
      (call/pc
       (lambda (c1)
         (abort (lambda () (cons 1 (c1 4))))))
      (call/pc
       (lambda (c2)
         (abort (lambda () (cons 2 (c2 3)))))))))
  
  ; (2 1 4 . 3)
  
  ; inf loop
  
  ; (splitter
  ;  (lambda (abort call/pc)
  ;    (cons
  ;     (call/pc
  ;      (lambda (c1)
  ;        (cons 1 (c1 4))))
  ;     (call/pc
  ;      (lambda (c2)
  ;        (cons 2 (c2 3)))))))
  
  (old%
   (cons
    (old-control (lambda (k) (cons 1 (k 4))))
    (old-control (lambda (k) (cons 2 (k 3))))
    ))
  
  ;(2 1 4 . 3)
  
  (reset
   (cons
    (shift k (cons 1 (k 4)))
    (shift k (cons 2 (k 3)))
    ))
  
  ;(1 2 4 . 3)
  
  (% (cons
      (cons 1 (fcontrol 4))
      (cons 2 (fcontrol 3))
      )
     (lambda (x y)
       (% (y x)
          (lambda (x2 y2)
            (% (y2 x2)
               (lambda (x3 y3) (y3 x3))
               )))))
  
  ; (let ((g (old% (* 2 (old-control (lambda (k) k))))))
  ;   (* 3 (g 7)))
  
  (let ((g (reset (* 2 (shift k k)))))
    (* 3 (g 7)))
  
  (splitter 
   (lambda (abort call/pc)
     (add1 (call/pc (lambda (k) (k (k 4)))))))
  
  (require (lib "match.ss"))
  (require (lib "pretty.ss"))
  (require (lib "errortrace.ss" "errortrace"))
  
  (define (shift-expander exp env)
    (match exp
      [(? number? x) `(lambda (k) (k ,x))]
      [(? symbol? x) (if (assoc x env)
                         (cadr (assoc x env))
                         x)]
      [('shift k e) (let ((new-env (cons (list k `(lambda (a) (lambda (kk) (kk (k a))))) env)))
                      `(lambda (k) (,(shift-expander e new-env) (lambda (x) x))))]
      [('lambda (x) e) `(lambda (k) (k (lambda (,x) ,(shift-expander e env))))]
      [(rator rand) `(lambda (k) (,(shift-expander rator env) (lambda (f) (,(shift-expander rand env) (lambda (a) (f (a k)))))))]))

(define (orr f g)
  (lambda (x) (or (f x) (g x)))
  )

(define (cps exp k p)
  (match exp
         [(? number? x) (list k x)]
         [(? symbol? x) (list k (cadr (assoc x p)))]
         [('lambda (x) e) `(,k (lambda (,x k) ,(cps e 'k (cons (list x x) p))))]
         [('shift p e) (cps e i (cons (list p `(lambda (v kk) (kk (,k v)))) p))]
         [('reset e) `(,k ,(cps e i p))]
         [('add1 e) (cps e `(lambda (a) (,k (add1 a))) p)]
         [('call/cc p e) (cps e k (cons (list p `(lambda (a kk) (,k a))) p))]
         [('begin e1 e2) (cps `((lambda (,(gensym)) ,e2 ) ,e1) k p)]
         [(e1 e2) (cps e1 `(lambda (f) ,(cps e2 `(lambda (a) (f a ,k)) p)) p)]
  ))

(define (c x)
  (cps x i '((add1 add1))))

(define (ec x)
  (eval (cps x i '((add1 add1)))))

(define i `(lambda (x) x))

  (define (se x) (list (shift-expander x '()) `(lambda (x) x)))


(require (lib "etc.ss"))


(reset (begin (add1 (shift k (add1 (k 1)))) (shift k (add1 (k 2)))))

(old% (begin (add1 (old-control (lambda (k) (add1 (k 1))))) (add1 (old-control (lambda (k) (add1 (k 2)))))))

(reset (add1 (*shift (lambda (k) (add1 (*shift (lambda (kk) (kk 3))))))))
      
(old% (add1 (old-control (lambda (k) (add1 (old-control (lambda (kk) (kk 3))))))))

  
