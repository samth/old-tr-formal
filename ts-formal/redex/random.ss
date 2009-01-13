#lang scheme

(require "opsem.ss" "types.ss" redex/reduction-semantics "utils.ss")

(define-extended-language nw-occur-lang occur-lang
  ;; no wrong
  [e x
     (e e ...) 
     (if e e e)
     v])

(caching-enabled? #t)

(define (run-random-tests)
  (redex-check occur-lang t (term (<: t (U N t))) #:attempts 10)
  (redex-check nw-occur-lang e (sub? (term e) (r (term e))) #:attempts 10))



