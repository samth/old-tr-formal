(define-syntax test-compile
  (syntax-rules ()
      ((test-compile e e1 e2 e3 asm)
       (begin
         (define e1 (make-readable (pass1 e usual-syntactic-environment) #t))
         (define e2 (make-readable (pass2 (pass1 e usual-syntactic-environment)) #t))
         (define e3 (make-readable (pass3 (pass2 (pass1 e usual-syntactic-environment))) #t))
         (define asm (assemble (compile e)))))))

(define exp1 '((lambda (x y) (+ x y)) 3 4))
(define exp2 '((lambda (f x y) (f x y)) + 3 4))
(define exp3 '((lambda () 
		 ((lambda (f) (f 3 4)) 
		  +))))

(define exp4 '((lambda (x y) (((lambda (x) x) +) x y)) 3 4))

(test-compile exp1 exp1.1 exp1.2 exp1.3 asm.1)
(test-compile exp2 exp2.1 exp2.2 exp2.3 asm.2)
(test-compile exp3 exp3.1 exp3.2 exp3.3 asm.3)
(test-compile exp4 exp4.1 exp4.2 exp4.3 asm.4)

(define dis disassemble)
