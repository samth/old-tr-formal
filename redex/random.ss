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
  !! : b -> b
  [(!! #f) #t]
  [(!! #t) #f])

(define (run-random-tests [p 100])
  (define-syntax-rule (rc pat e)
    (begin (printf "checking: ~a~n" 'e)
           (redex-check nw-occur-lang pat e #:attempts p)))
  (rc t (term (<: t (U N t))))
  (rc t (term ((restrict top t) . <: . t)))
  ;;lemma apo_abo_id:
  ;;fixes ph :: ph and p :: p 
  ;;assumes A:"abo x p = Some ph"
  ;;shows "apo ph Top (Some ([], x)) = Some p"
  (time
   (rc (side-condition (p x) (not (equal? (term (abo x p)) '())))
       (match/redex occur-lang (abo x p)
         [(ph) (equal? (term (p)) (term (apo ph top (() x))))]
         [any #t]))
   )
  (time
   (rc (p x) (equal? (term (p))
                     (match/redex occur-lang (abo x p)
                       [(ph) (term (apo ph top (() x)))]
                       [any (term (p))])))
   )
  ;; we'd like it to be a subtype of t_1 too, but that's hard to ensure
  (rc (t_1 t_2) (term (all ((restrict t_1 t_2) . <: . t_2))))
  (rc (t_1 t_2) (*term-let occur-lang
                  ([t (term (remove t_1 t_2))])
                  (term (all (t . <: . t_1)
                             (any (!! (t . <: . t_2))
                                  (t . <: . (U)))))))
  (rc (t_0 t t_s)
      (term (implies (all (t_0 . <: . t)
                          (!! (t_0 . <: . t_s)))
                     (t_0 . <: . (remove t t_s)))))  
  (rc (t_1 t_2) (term (implies (no-overlap t_1 t_2)
                               (any
                                (t_1 . <: . (U))
                                (t_2 . <: . (U))
                                (all (!! (t_1 . <: . t_2))
                                     (!! (t_2 . <: . t_1)))))))
  (rc e (sub? (term e) (r (term e)))))


