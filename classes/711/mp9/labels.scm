;; cfa/generate.scm-- produce syntactic assertions

(let ((time-stamp "Time-stamp: <2003-11-11 16:02:42 wand>"))
  (eopl:printf
    "cfa/labels.scm ~a~%"
    (substring time-stamp 13 29)))

;; assertions:

;; assertion ::= (CONST l ) | (PRIM l l1 l2) | (VAR l x) 
;;            |  (ABS l x l') | (APP l l1 l2)
;;            |  (LET l x l1 l2) | (IF l l1 l2 l3)

;; first argument is always the label of the current expression.

;; assertions-of : exp -> (labelled-expression . (list assertions))

;; uses local state to manage labels and constraints.

;; main loop takes exp and its label, and adds its constraints to the
;; list by local side-effect.

(define (assertions-of-exp exp0)
  (let* ((next-label
          (let ((next-free-label 0))
            (lambda ()
              (let ((x next-free-label))
                (set! next-free-label (+ next-free-label 1))
                x))))
         (assertions '())
         (assert! (lambda (x)
                    (set! assertions (cons x assertions))))
    ;; traverse exp0, generating assertions
         (labelled-exp
           (let label ((exp exp0) (lab (next-label)))
             (cases expression exp
               (const-exp (number)
                 (assert! (list 'const lab))
                 (list lab ': exp))
               (true-exp ()
                         (assert! (list 'const lab))
                         (list lab ': exp))
               (false-exp ()
                          (assert! (list 'const lab))
                          (list lab ': exp))
               (primapp-exp 
                (prim exps)
                (cases primitive prim
                  (zero-test-prim 
                   ()
                   (let ((new-lab (next-label)))
                     (begin 
                       (assert! (list 'prim1 lab new-lab))
                       (list lab ': 'primapp-exp (label (car exps) new-lab)))
                   ))
                  (else
                   (let ((new-labs (map (lambda (x) (next-label)) exps)))
                     (begin
                       (assert! (append (list 'prim lab) new-labs))
                       (list lab ':
                             (cons 'primapp-exp (map label exps new-labs))))))))
               (if-exp (test then else)
                       (let ((lab1 (next-label))
                             (lab2 (next-label))
                             (lab3 (next-label))
                             )
                         (begin
                           (assert! (list 'if lab lab1 lab2 lab3))
                           (list lab ': (list 'if-exp 
                                              (label test lab1) 
                                              (label then lab2)
                                              (label else lab3))))))
               (var-exp (id)
                 (assert! (list 'var lab id))
                 (list lab ': exp))
               (proc-exp (ids body)
                 (let ((lab1 (next-label)))
                   (cond 
                     [(null? ids)
                      (label (proc-exp '(_) body) lab)]
                     [(= 1 (length ids))
                      (begin
                        (assert! (list 'abs lab (car ids) lab1))
                        (list lab ': (list 'proc-exp (car ids) (label body lab1))))]
                     [else (begin
                             (assert! (list 'abs lab (car ids) lab1))
                             (list lab ': (list 'proc-exp (car ids) (label (proc-exp (cdr ids) body) lab1))))])))
                   
               (app-exp (rator rands)
                 (let ((lab1 (next-label))
                       (rand-lab (next-label)))
                   (cond
                     [(null? rands) (label (app-exp rator '(0)) lab)]
                     [(= 1 (length rands))
                      (begin
                        (assert! (list 'app lab lab1 rand-lab))
                        (list lab ':
                              (list 'app-exp 
                                    (label rator lab1)
                                    (label (car rands) rand-lab))))]
                      [else (label (app-exp (app-exp rator (list (car rands))) (cdr rands)) lab)]
                     )))
               
               (let-exp (ids rhss body)
                        (let ((labs (map (lambda (x) (next-label)) rhss))
                                 (let-lab (next-label)))
                             (begin
                               (for-each (lambda (id rhs l)
                                           (assert! (list 'bind l id)))
                                         ids rhss labs)
                               (assert! (list 'let lab let-lab))
                               (list lab ': (list 'let ids (map label rhss labs) (label body let-lab))))))
               (letrec-exp (ids rhss body)
                           (let ((labs (map (lambda (x) (next-label)) rhss))
                                 (let-lab (next-label)))
                             (begin
                               (for-each (lambda (id rhs l)
                                           (assert! (list 'bind l id)))
                                         ids rhss labs)
                               (assert! (list 'let lab let-lab))
                               (list lab ': (list 'letrec ids (map label rhss labs) (label body let-lab))))))
                            
               ))))
    
               ;; now return the list of generated assertions
    (cons labelled-exp assertions)
               ))

(define (assertions-of-program pgm)
  (cases program pgm
    (a-program (exp) (assertions-of-exp exp))))

(define (assertions str)
  (assertions-of-program (scan&parse str)))

              

            