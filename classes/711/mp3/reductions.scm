(let ((time-stamp "Time-stamp: <2003-09-17 16:37:11 wand>"))
  (eopl:printf
    "~a ~a~%"
    "base/reductions.scm"
    (substring time-stamp 13 29)))

;;;;;;;;;;;;;;;; reductions ;;;;;;;;;;;;;;;;

(define reduce-delta-redex
  (lambda (prim exps)
    (let
      ((args (map value->num exps)))
      (cases primitive prim
        (add-prim () (const-exp (+ (car args) (cadr args))))
        (subtract-prim () (const-exp (- (car args) (cadr args))))
        (mult-prim  () (const-exp (* (car args) (cadr args))))
        (incr-prim  () (const-exp (+ (car args) 1)))
        (decr-prim  () (const-exp (- (car args) 1)))
        (zero-test-prim () (if (zero? (car args)) (true-exp) (false-exp)))
        ))))
      
(define value->num
  (lambda (exp)
    (cases expression exp
      (const-exp (n) n)
      (else (eopl:error 'value-to-num "Not a const-exp: ~s" exp)))))

;; reduce-beta : rator rand -> (optional closed expression)
(define reduce-beta-redex
  (lambda (rator rands)
    (cases expression rator
      (proc-exp (ids body) (subst-closed body ids rands))
      (else #f))))                      

(define reduce-if-redex
  (lambda (e0 e1 e2)
    (cases expression e0
      (true-exp () e1)
      (false-exp () e2)
      (else (eopl:error 'reduce-if-redex "non-boolean test: ~s" e0)))))

(define reduce-let-redex
  (lambda (ids rhs-values body)
    (subst-closed body ids rhs-values)))

;; old EOPL letrec syntax
; (define reduce-letrec-redex
;   (lambda (proc-names idss proc-bodies letrec-body)
;     (subst-closed
;       letrec-body
;       proc-names
;       (map                              
;         (lambda (ids proc-body)
;           (proc-exp ids
;             (letrec-exp proc-names idss proc-bodies proc-body)))
;         idss
;         proc-bodies))))
        

; new letrec syntax
(define reduce-letrec-redex
  (lambda (ids rhss body)
    (subst-closed
      body
      ids
      (map
        (lambda (rhs) (letrec-exp ids rhss rhs))
        rhss))))

; cond 
(define reduce-cond-redex
  (lambda (tests results)
    (cases expression (car tests)
           (true-exp () (car results))
           (false-exp () (cond-exp (cdr tests) (cdr results)))
           (else (eopl:error 'reduce-cond-redex "non-boolean-test: ~s" (car tests))))))

(define reduce-car-redex
  (lambda (l)
    (cases expression l
      (cons-exp (a b) a)
      (else (eopl:error 'reduce-car-redex "car expects a list: ~s" l)))))

(define reduce-cdr-redex
  (lambda (l)
    (cases expression l
      (cons-exp (a b) b)
      (else (eopl:error 'reduce-cdr-redex "cdr expects a list: ~s" l)))))

(define reduce-nil-test-redex
  (lambda (l)
    (cases expression l
      (cons-exp (a b) (false-exp))
      (nil-exp () (true-exp))
      (else (eopl:error 'reduce-nil-test-redex "nil? expects a list: ~s" l)))))

(define (reduce-let*-redex ids rhss body)
  (if (null? ids) (let-exp '() '() body)
      (let-exp (list (car ids)) (list (car rhss) )
               (let*-exp (cdr ids)
                         (map (lambda (x) (subst-closed x (list (car ids)) (list (car rhss)))) (cdr rhss))
                         body))))