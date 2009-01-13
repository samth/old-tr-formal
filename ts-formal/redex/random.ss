#lang scheme

(require "opsem.ss" "types.ss" redex/reduction-semantics "utils.ss")

(define-extended-language nw-occur-lang occur-lang
  ;; no wrong
  [e x
     (e e ...) 
     (if e e e)
     v])

(caching-enabled? #t)

(redex-check occur-lang t (term (<: t (U N t))) #:attempts 10)

(define (sub? trm)
  (term (check-sub ,(no-fail (tc-fun trm))
                   ,(no-fail (map tc-fun (r trm))))))

(redex-check nw-occur-lang e (sub? (term e)) #:attempts 10)



