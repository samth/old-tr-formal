(define-syntax DEFINE-VALUES
  (syntax-rules
   ()
   ((define-values (<name> ...) <body> ...)
    (begin
      (define <name> #f) ...
      (call-with-values
       (lambda () <body> ...)
       (lambda all-the-values
	 (define-values-helper all-the-values <name> ...)))))))

(define-syntax DEFINE-VALUES-HELPER
  (syntax-rules
   ()
   ((define-values-helper accum)
    #f)
   ((define-values-helper accum <name1> <name2> ...)
    (begin
      (set! <name1> (car accum))
      (define-values-helper (cdr accum) <name2> ...)))))            
       

(define use usual-syntactic-environment)

(define-syntax test-compile
  (syntax-rules ()
      ((test-compile e e1 e2 e3 asm)
       (begin
         (define e1 (make-readable (pass1 e usual-syntactic-environment) #t))
         (define e2 (make-readable (pass2 (pass1 e usual-syntactic-environment)) #t))
         (define e3 (make-readable (pass3 (pass2 (pass1 e usual-syntactic-environment))) #t))
         (define asm (disassemble (assemble (compile e))))))))

