#lang scheme/base

(require mzlib/trace
         (except-in scheme/list flatten)
         (only-in srfi/1 lset= lset<=)
         redex/reduction-semantics
         "utils.ss"
         (for-syntax scheme/base))

(provide (all-defined-out))

(define-language occur-lang
  ;; expressions
  [e x
     (e e ...) 
     (if e e e)
     wrong
     v]
  ;; values
  [v (lambda ([x : t] ...) e) number #t #f c (cons v v)]
  [(n i) number]
  [b boolean]
  [boolean #t #f]
  ;; constants
  [c add1 number? boolean? zero? not cons car cdr cons? procedure?]
  ;; variables
  [(x y) (variable-except lambda add1 if number? boolean? zero? not cons car cdr cons? procedure?)]

  ;; contexts
  [E (v ... E e ...) (if E e e) hole]

  ;; types
  [(t u) N proctop top #t #f (t ..._a -> t : fh ..._a : sh) (pr t t) (union t ...)]
  ;; filters
  [f ((p ...) (p ...))]
  [fh ((ph ...) (ph ...))]
  [p (t pi x) (! t pi x) bot]
  
  [ph (t pi) (! t pi) both]
  
  ;; subjects
  [s 0 (pi x)]
  [sh 0 (pi number)]
  
  ;; paths
  [pi (pe ...)]
  [pe car cdr]
  
  ;; environments
  [G ((x t) ...)]
  )

(define type? (redex-match occur-lang t))

(define-metafunction occur-lang
  all : boolean ... -> boolean  
  [(all #t ...) #t]
  [(all any_1 ...) #f])

(define-metafunction occur-lang
  any : boolean ... -> boolean
  [(any #f ...) #f]
  [(any any_1 ...) #t])

(define-metafunction occur-lang
  <: : t t -> boolean
  ;; S-Refl
  [(t_1 . <: . t_1) #t]
  ;; S-ProcTop
  [((t_1 ... -> t_2 : fh ... : sh) . <: . proctop) #t]
  ;; S-Top
  [(t_1 . <: . top) #t]
  ;; S-Pair
  [((pr t_1 u_1) . <: . (pr t_2 u_2)) 
   #t
   (side-condition (term (t_1 . <: . t_2)))
   (side-condition (term (u_1 . <: . u_2)))]
  ;; S-UnionSub
  [((union t_1 ...) . <: . t_2)
   #t
   (side-condition (term (all (t_1 . <: . t_2) ...)))]
  ;; S-UnionSuper
  [(t_2 . <: . (union t_1 ...))
   #t
   (side-condition (term (any (t_2 . <: . t_1) ...)))]
  ;; S-Fun
  [((t_a ..._1 -> t_r : fh_1 ..._1 : sh_1) . <: . (u_a ..._1 -> u_r : fh_2 ..._1 : sh_2))
   #t   
   (side-condition (term (t_r . <: . u_r)))
   ;; FIXME - shouldn't be necessary
   (side-condition (= (length (term (u_a ...))) (length (term (t_a ...)))))
   (side-condition (term (all (u_a . <: . t_a) ...)))   
   (side-condition (or (equal? (term sh_1) (term sh_2))
                       (equal? (term sh_2) (term 0))))   
   (side-condition (term (all (subset-fh fh_2 fh_1) ...)))]
  ;; otherwise
  [(t_1 . <: . t_2) #f])

(define-metafunction occur-lang
  subset-fh : fh fh -> boolean
  [(subset-fh ((ph_1+ ...) (ph_1- ...)) ((ph_2+ ...) (ph_2- ...)))
   ,(and (lset<= equal? (term (ph_1+ ...)) (term (ph_2+ ...)))
         (lset<= equal? (term (ph_1- ...)) (term (ph_2- ...))))])

(define-metafunction occur-lang
  subset-f : f f -> boolean
  [(subset-f ((p_1+ ...) (p_1- ...)) ((p_2+ ...) (p_2- ...)))
   ,(and (lset<= equal? (term (p_1+ ...)) (term (p_2+ ...)))
         (lset<= equal? (term (p_1- ...)) (term (p_2- ...))))])

(define-metafunction occur-lang
  sub-s : s s -> boolean
  [(sub-s s s) #t]
  [(sub-s s 0) #t]
  [(sub-s s_1 s_2) #f])

(define-metafunction occur-lang
  sub-sh : sh sh -> boolean
  [(sub-sh sh sh) #t]
  [(sub-sh sh 0) #t]
  [(sub-sh sh_1 sh_2) #f])

(define-metafunction occur-lang
  subst-n : (x e) ... e -> e
  [(subst-n (x_1 any_1) (x_2 any_2) ... any_3) (subst x_1 any_1 (subst-n (x_2 any_2) ... any_3))]
  [(subst-n any_3) any_3])

(define-metafunction occur-lang
  subst : x e e -> e
  ;; 1. x_1 bound, so don't continue in λ body
  [(subst x_1 any_1 (lambda ([x_2 : t_2] ... [x_1 : t_1] [x_3 : t_3] ...) any_2))
   (lambda ([x_2 : t_2] ... [x_1 : t_1] [x_3 : t_3] ...) any_2)
   (side-condition (not (member (term x_1) (term (x_2 ...)))))]
  ;; 2. general purpose capture avoiding case
  [(subst x_1 any_1 (lambda ([x_2 : t] ...) any_2))
   ,(term-let ([(x_new ...)
                (variables-not-in (term (x_1 any_1 any_2)) 
                                  (term (x_2 ...)))])
              (term 
               (lambda ([x_new : t] ...)
                 (subst x_1 any_1 (subst-vars (x_2 x_new) ... any_2)))))]
  ;; 3. replace x_1 with e_1
  [(subst x_1 any_1 x_1) any_1]
  ;; 4. x_1 and x_2 are different, so don't replace
  [(subst x_1 any_1 x_2) x_2]
  ;; if
  [(subst x_1 any_1 (if e_1 e_2 e_3))
   (if (subst x_1 any_1 e_1)
       (subst x_1 any_1 e_2)
       (subst x_1 any_1 e_3))]
  ;; constants (values that aren't lambda)
  [(subst x any_1 v_2) v_2]
  ;; app
  [(subst x_1 any_1 (e_1 ...))
   ((subst x_1 any_1 e_1) ...)])

;; dumb substitution
(define-metafunction occur-lang
  subst-vars : (x e) ... e -> e 
  [(subst-vars (x_1 e_1) (lambda ([x_2 : t_2] ...) e_2))
   (lambda ([x_2 : t_2] ...) (subst-vars (x_1 e_1) e_2))]  
  ;; 3. replace x_1 with e_1
  [(subst-vars (x_1 e_1) x_1) e_1]
  ;; 4. x_1 and x_2 are different, so don't replace
  [(subst-vars (x_1 e_1) x_2) x_2]
  ;; if
  [(subst-vars (x_1 e_0) (if e_1 e_2 e_3))
   (if (subst-vars (x_1 e_0) e_1)
       (subst-vars (x_1 e_0) e_2)
       (subst-vars (x_1 e_0) e_3))]
  ;; constants (values that aren't lambda)
  [(subst-vars (x_1 e_1) v_2) v_2]
  ;; app
  [(subst-vars (x_1 e_0) (e_1 ...))
   ((subst-vars (x_1 e_0) e_1) ...)]
  ;; multi-arg
  [(subst-vars (x_1 e_1) (x_2 e_2) ... e_t)
   (subst-vars (x_1 e_1) (subst-vars (x_2 e_2) ... e_t))])

(define-metafunction occur-lang
  U : t ... -> t
  [(U) (union)]
  [(U t) t]
  [(U t u) u (side-condition (term (t . <: . u)))]
  [(U t u) t (side-condition (term (u . <: . t)))]
  [(U t u) (union t u)]
  [(U t t_rest ...) (U t (U t_rest ...))])

(define value? (redex-match occur-lang v))

(define lambda? (redex-match occur-lang (lambda ([x_1 : t_1] ..._a) e_body)))
(define constant? (redex-match occur-lang c))


(define-metafunction occur-lang
  delta : e -> any
  [(delta (add1 number_1)) ,(+ 1 (term number_1))]
  [(delta (zero? 0)) #t]
  [(delta (zero? number_1)) #f]
  [(delta (not #t)) #f]
  [(delta (not #f)) #t]
  [(delta (car (cons v_1 v_2))) v_1]
  [(delta (cdr (cons v_1 v_2))) v_2]
  [(delta (cons? (cons v_1 v_2))) #t]
  [(delta (cons? v)) #f]
  [(delta (procedure? (lambda ([x : t] ...) e))) #t]
  [(delta (procedure? v)) #f]
  [(delta (number? number_1)) #t]
  [(delta (number? v_1)) #f]
  [(delta (boolean? boolean_1)) #t]
  [(delta (boolean? v_1)) #f]
  [(delta (c_1 v_1)) wrong])



(define reductions
  (reduction-relation 
   occur-lang
   [==> ((lambda ([x_1 : t_1] ..._a) e_body) v_arg ..._a)
        (subst-n (x_1 v_arg) ... e_body)
        E-Beta]
   [==> (if #f e_2 e_3)
        e_3
        E-IfFalse]
   [==> (if v_1 e_2 e_3)
        e_2
        E-IfTrue
        (side-condition (term v_1))]   
   [==> (c_op v_arg ...) (delta (c_op v_arg ...))
        E-Delta
        (side-condition (not (value? (term (c_op v_arg ...)))))]
   [==> (v_op v_arg ...) wrong
        E-WrongApp
        (side-condition (and (not (lambda? (term v_op)))
                             (not (constant? (term v_op)))))]
   [--> (in-hole E_1 wrong) wrong
        E-Wrong
        (side-condition (not (equal? (term wrong) (term (in-hole E_1 wrong)))))]
   with
   [(--> (in-hole E_1 a) (in-hole E_1 b)) (==> a b)]
   ))

(define (r t) (apply-reduction-relation reductions t))
(define (r* t) (apply-reduction-relation* reductions t))