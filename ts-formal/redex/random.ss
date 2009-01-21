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

(define-metafunction occur-lang
  ! : b -> b
  [(! #f) #t]
  [(! #t) #f])

(define (run-random-tests [p 100])
  (redex-check occur-lang t (term (<: t (U N t))) #:attempts p)
  (redex-check occur-lang t (term ((restrict top t) . <: . t)) #:attempts p)
  ;; we'd like it to be a subtype of t_1 too, but that's hard to ensure
  (redex-check occur-lang (t_1 t_2) (term (all ((restrict t_1 t_2) . <: . t_2)))
               #:attempts p)
  (redex-check occur-lang (t_1 t_2) (*term-let occur-lang
                                      ([t (term (remove t_1 t_2))])
                                      (term (all (t . <: . t_1)
                                               (any (! (t . <: . t_2))
                                                    (t . <: . (U))))))
               #:attempts p)
  (redex-check occur-lang (t_0 t t_s)
               (term (implies (all (t_0 . <: . t)
                                   (! (t_0 . <: . t_s)))
                              (t_0 . <: . (remove t t_s))))
               #:attempts p)  
  (redex-check occur-lang (t_1 t_2) (term (implies (no-overlap t_1 t_2)
                                                   (any
                                                    (t_1 . <: . (U))
                                                    (t_2 . <: . (U))
                                                    (all (! (t_1 . <: . t_2))
                                                         (! (t_2 . <: . t_1))))))
               #:attempts p)
  (redex-check nw-occur-lang e (sub? (term e) (r (term e))) #:attempts p))



