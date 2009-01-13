#lang scheme

(require "opsem.ss" redex "utils.ss")

(define-extended-language nw-occur-lang occur-lang
  ;; no wrong
  [e x
     (e e ...) 
     (if e e e)
     v])

#;
(for/list ([i (in-range 20)])
  (generate-term nw-occur-lang e 5))

(caching-enabled? #t)

(redex-check occur-lang t (term (<: t (U N t))) #:attempts 10)

(define (r t) (apply-reduction-relation reductions t))

(define counter 0)

(define (sub? trm)
  (match/redex occur-lang ,(with-handlers ([exn:fail? (lambda _ #f)])
                             (tc-fun trm))
    [(t f s)     
     (*term-let occur-lang
       ([(e ...) (r trm)])
       (match/redex occur-lang ,(with-handlers ([exn:fail? (lambda _ #f)])
                                  (term ((tc () e) ...)))
         [((t_s f_s s_s) ...)
          (term (all (t_s . <: . t) ...))]
         [any (begin (printf "failing~n") #f)]))]
    [any #t]))

(redex-check nw-occur-lang e (sub? (term e)) #:attempts 10000)

counter


