;; ==================================================
;; Test harness 2
;; ==================================================
(define run-tests
  (lambda (proc-to-test list-of-test-cases)
    (run-the-tests proc-to-test list-of-test-cases 0 '())))

(define run-the-tests
  (lambda (proc-to-test list-of-test-cases num-passed list-of-failures)
    (if (null? list-of-test-cases)
	(begin
	  (newline)
	  (eopl:printf "Passed ~s, failed ~s" num-passed list-of-failures)
	  (newline))
	(if (run-test proc-to-test (car list-of-test-cases))
 	    (run-the-tests proc-to-test 
			   (cdr list-of-test-cases)
			   (+ num-passed 1)
			   list-of-failures)
 	    (run-the-tests proc-to-test 
			   (cdr list-of-test-cases)
			   num-passed
			   (cons (caar list-of-test-cases) 
				 list-of-failures))))))

(define run-test
  (lambda (proc-to-test test-case)
    (let ((name (car test-case))
	  (input (if (list? (cadr test-case)) 
		     (cadr test-case) 
		     (list (cadr test-case))))
	  (expected-result (caddr test-case)))
      (let ((actual-result (apply proc-to-test input)))
	(begin
	  (newline)
	  (eopl:printf "--- ~s -------------------------" name) (newline)
	  (eopl:printf "  Args: ~s" input) (newline)
	  (eopl:printf "  Want: ~s" expected-result) (newline)
	  (eopl:printf "  Have: ~s" actual-result) (newline)
	  (let ((result (equal? expected-result actual-result)))
	    (begin
	      (eopl:printf "  -> ~s" (if result 'OK 'Failed!))
	      (newline))
	    result))))))

;;
;; Testing for run
;;
(define run-test-cases
  '(
    (example-0       "3 - 2 - 1"           0)
    (example-1       "3 + 2 * 66 - 5"    130)
    (example-2       "(3 + 2) * 66 - 5"  325)
    (simple-1        "0"                   0)
    (simple-2        "1"                   1)
    (sum-1           "1+2"                 3)
    (sum-2           "1+2+3"               6)
    (sum-3           "1+2+3+4"            10)
    (minus-1         "1-2"                -1)
    (minus-2         "1-2-3"              -4)
    (minus-3         "1-2-3-4"            -8)
    (times-1         "2*3"                 6)
    (times-2         "3*4*5"              60)
    (times-3         "1*2*3*4"            24)
    (divide-1        "2/1"                 2)
    (divide-2        "24/4/2"              3)
    (divide-3        "360/6/5/4"           3)
    (parens-1        "(1)"                 1)
    (parens-1a       "(1)+2"               3)
    (parens-1b       "(1)+(2)"             3)
    (parens-2        "((1))"               1)
    (parens-2a       "((1)+2)"             3)
    (parens-2b       "((1)+2)+3"           6)
    (parens-2c       "(2+(1))+3"           6)
    (parens-2d       "2+((1))+3"           6)
    (parens-2e       "2+((1)+3)"           6)
    (parens-2f       "2+(3+(1))"           6)
    (parens-3        "(((1)))"             1)
    (neg-1           "-1"                 -1)
    (neg-2           "--1"                +1)
    (neg-3           "---1"               -1)
    (assoc-right-1   "1+4*2"               9)
    (assoc-right-2   "1+4/2"               3)
    (assoc-right-3   "1-4*2"              -7)
    (assoc-right-4   "1-4/2"              -1)
    (assoc-left-1    "4*2+1"               9)
    (assoc-left-2    "4/2+1"               3)
    (assoc-left-3    "4*2-1"               7)
    (assoc-left-4    "4/2-1"               1)
    (neg-example-1   "3*-2"               -6)
    (neg-example-2   "-(2+3)*4"          -20)
    (neg-example-3   "-2+3*4"             10)
    (neg-example-4   "4+-2"                2)
    (neg-example-5   "4*-(2+3)"          -20)
    ))
(define test-run
  (lambda ()
    (run-tests run run-test-cases)))

;;
;; Tests for scan&parse
;;
(define scan&parse-tests
  `(
    (example-1 "2" ,(sum
                     (product (const-factor 2)
                              `() `())                              
                     `() `()))
    (example-2 "2 * 1" ,(sum (product
                              (const-factor 2)
                              `(,(times-op))
                              `(,(const-factor 1)))
			   '() '()))
    (example-3 "2 * 1 / 4" ,(sum 
                             (product
                              (const-factor 2)
                              `(,(times-op) ,(divide-op))
                              `(,(const-factor 1) ,(const-factor 4)))
                             '() '()))
    
    (example-4 "2 + 1" ,(sum (product (const-factor 2) '() '())
			   `(,(plus-op))
			   `(,(product (const-factor 1) '() '()))))
    
    (example-5 "3 - 2 - 1" ,(sum
                             (product (const-factor 3) '() '())
                             `(,(minus-op) ,(minus-op))
                             `(,(product (const-factor 2) '() '())
                               ,(product (const-factor 1) '() '()))))
    
    (example-6 "3 + 2 * 66 - 5" ,(sum
                                  (product (const-factor 3) '() '())
                                  `(,(plus-op) ,(minus-op))
                                  `(,(product (const-factor 2) `(,(times-op)) `(,(const-factor 66)))
                                    ,(product (const-factor 5) '() '()))))
    (example-7 "(3 + 2)* 66 - 5" ,(sum
                                   (product
                                    (paren-exp
                                     (sum (product (const-factor 3) '() '())
                                          `(,(plus-op))
                                          `(,(product (const-factor 2) '() '()))))
                                    `(,(times-op))
                                    `(,(const-factor 66)))
                                   `(,(minus-op))
                                   `(,(product (const-factor 5) '() '()))))
	      ))
(define test-scan&parse
  (lambda ()
    (run-tests scan&parse scan&parse-tests)))



;; test-all: () -> ()
;; Run all the tests
(define test-all
  (lambda ()
    (begin
      (test-run)
      (test-scan&parse)
      )))
