#lang scheme

(require "opsem.ss" "types.ss" redex/reduction-semantics "utils.ss")

(define-extended-language nw-occur-lang occur-lang
  ;; no wrong
  [e x
     (e e ...) 
     (if e e e)
     v])

(caching-enabled? #t)

(define-metafunction occur-lang
  implies : b b -> b
  [(implies #t #f) #f]
  [(implies b_1 b_2) #t])

(define (run-random-tests)
  (redex-check occur-lang t (term (<: t (U N t))) #:attempts 10)
  (redex-check occur-lang (t_1 t_2) (term (all ((restrict t_1 t_2) . <: . t_2)))
               #:attempts 1000)
  (redex-check occur-lang (t_1 t_2) (term (implies (no-overlap t_1 t_2)
                                                   (any
                                                    (t_1 . <: . (U))
                                                    (t_2 . <: . (U))
                                                    (all ,(not (term (t_1 . <: . t_2)))
                                                         ,(not (term (t_2 . <: . t_1)))))))
               #:attempts 1000)
  (redex-check nw-occur-lang e (sub? (term e) (r (term e))) #:attempts 10))



