;; ==================================================
;; Test harness
;; ==================================================
(define run-tests2
  (lambda (list-of-test-cases)
    (run-the-tests2 list-of-test-cases 0 '())))

(define run-the-tests2
  (lambda (list-of-test-cases num-passed list-of-failures)
    (if (null? list-of-test-cases)
        (begin
          (newline)
          (eopl:printf "Passed ~s, failed ~s" num-passed (if (null? list-of-failures) 0 list-of-failures))
          (newline))
        (if (run-test2 (car list-of-test-cases))
            (run-the-tests2 
             (cdr list-of-test-cases)
             (+ num-passed 1)
             list-of-failures)
            (run-the-tests2 
             (cdr list-of-test-cases)
             num-passed
             (cons (caar list-of-test-cases)
                   list-of-failures))))))

(define run-test2
  (lambda (test-case)
    (let ((name (car test-case))
          (proc-to-test (cadr test-case))
          (input (if (list? (caddr test-case))
                     (caddr test-case)
                     (list (caddr test-case))))
          (expected-result (cadddr test-case)))
      (let ((actual-result (apply proc-to-test input)))
        (begin
          (newline)
          (eopl:printf "--- ~s -------------------------" name) (newline)
          (eopl:printf "  Call: ~s" (cons proc-to-test input)) (newline)
          (eopl:printf "  Want: ~s" expected-result) (newline)
          (eopl:printf "  Have: ~s" actual-result) (newline)
          (let ((result (equal? expected-result actual-result)))
            (begin
              (eopl:printf "  -> ~s" (if result 'OK 'Failed!))
              (newline))
            result))))))
