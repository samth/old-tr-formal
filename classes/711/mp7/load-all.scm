;;; threads/load-all.scm

;;; like implicit-store/lang.scm, but with lists and multiple threads

(let ((time-stamp "Time-stamp: <2003-10-25 10:19:15 wand>"))
  (eopl:printf "threads/load-all.scm ~a~%"
    (substring time-stamp 13 29)))

;;; the thread language is now spread over too many files to load by hand

;;; load by loading this file or saying (reload)
;;; test with (run-all)
;;; toggle tracing with (toggle-trace)


;;; the loader:

(define reload
  (lambda ()
    (for-each load
      '("lang.scm"
        "../init.scm"
         "tests.scm"
         "utils.scm"
         "ceks.scm"
         "store1.scm"
         "runtime.scm"))))


(define run-all
  (lambda ()
    (run-experiment run use-execution-outcome
      groups-for-test all-tests equal-external-reps?)))

(define run-one
  (lambda (test-name)
    (run-test run test-name)))

;; now load
(reload)