;; cfa/generate.scm-- produce syntactic assertions

(let ((time-stamp "Time-stamp: <2003-11-10 22:27:43 wand>"))
  (eopl:printf
    "cfa/labels.scm ~a~%"
    (substring time-stamp 13 29)))

;; assertions:

;; assertion ::= (CONST l e) | (DIFF l l1 l2 e) | (VAR l x e) 
;;            |  (ABS l x l' e) | (APP l l1 l2 e)

;; first argument is always the label of the current expression, last
;; argument is always the expression itself.


;; assertions-of : exp -> (list assertions)

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
                    (set! assertions (cons x assertions)))))
    ;; traverse exp0, generating assertions
    (let loop! ((exp exp0) (lab (next-label)))
      (cases expression exp
        (const-exp (number) (assert! (list 'const lab exp)))
        (diff-exp (exp1 exp2)
          (let ((lab1 (next-label))
                (lab2 (next-label)))
            (begin
              (assert! (list 'diff lab lab1 lab2 exp))
              (loop! exp1 lab1)
              (loop! exp2 lab2))))
        (var-exp (id)
          (assert! (list 'var lab id exp)))
        (proc-exp (id body)
          (let ((lab1 (next-label)))
            (begin
              (assert! (list 'abs lab id lab1 exp))
              (loop! body lab1))))
        (app-exp (rator rand)
          (let ((lab1 (next-label))
                (lab2 (next-label)))
            (begin
              (assert! (list 'app lab lab1 lab2 exp))
              (loop! rator lab1)
              (loop! rand lab2))))))
    ;; now return the list of generated assertions
    assertions
    ))

(define (assertions-of-program pgm)
  (cases program pgm
    (a-program (exp) (assertions-of-exp exp))))

(define (assertions str)
  (assertions-of-program (scan&parse str)))

              

            