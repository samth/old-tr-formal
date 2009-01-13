#lang scheme/base

(require mzlib/trace
         (except-in scheme/list flatten)
         (only-in srfi/1 lset= lset<=)
         redex/reduction-semantics
         "utils.ss"
         (for-syntax scheme/base))

(provide (all-defined-out))

(caching-enabled? #f)

(define T-Bot (make-parameter #t))
(define T-Not (make-parameter #t))
(define enable-T-IfAnd (make-parameter #t))
(define enable-T-IfOr (make-parameter #t))
(define enable-union-> (make-parameter #t))

;; JUNK - remove
(define enable-T-AbsPred (make-parameter #f))
(define enable-T-IfTrue (make-parameter #t))
(define enable-T-IfFalse (make-parameter #t))

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
  all : boolean ... -> boolean  
  [(all #t ...) #t]
  [(all any_1 ...) #f])

(define-metafunction occur-lang
  any : boolean ... -> boolean
  [(any #f ...) #f]
  [(any any_1 ...) #t])

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
   [--> (in-hole E_1 wrong) wrong
        E-Wrong
        (side-condition (not (equal? (term wrong) (term (in-hole E_1 wrong)))))]
   with
   [(--> (in-hole E_1 a) (in-hole E_1 b)) (==> a b)]
   ))

;; types only from here


(define-metafunction occur-lang
  delta-t : c -> t
  [(delta-t number?) (predty N ())]
  [(delta-t boolean?) (predty (U #t #f) ())]
  [(delta-t procedure?) (predty proctop ())]
  [(delta-t cons?) (predty (pr top top) ())]
  [(delta-t add1) (simplefun N N)]
  [(delta-t zero?) (simplefun N (U #t #f))]
  [(delta-t not) (simplefun (U #t #f) (U #t #f))])


(define-metafunction occur-lang
  simplefun : t t -> t
  [(simplefun t u) (t -> u : (() ()) : 0)])

(define-metafunction occur-lang
  predty : t pi -> t
  [(predty t pi)
   (top -> (U #t #f) : (((t pi)) ((! t pi))) : 0)])


(define-metafunction occur-lang
  abstract-filter : x f -> fh
  [(abstract-filter x ((p_1 ...) (p_2 ...)))
   ((flatten (abo x p_1) ...)
    (flatten (abo x p_2) ...))])

(define-metafunction occur-lang
  apply-filter : fh t s -> f
  [(apply-filter ((ph_+ ...) (ph_- ...)) t s)
   ((flatten (apo ph_+ t s) ...)
    (flatten (apo ph_- t s) ...))])

(define-metafunction occur-lang
  abo : x p -> (ph ...)
  [(abo x bot) (both)]
  [(abo x (t pi x)) ((t pi))]
  [(abo x (! t pi x)) ((! t pi))]
  [(abo x (t pi y)) () (side-condition (not (equal? (term x) (term y))))]
  [(abo x (! t pi y)) () (side-condition (not (equal? (term x) (term y))))])

(define-metafunction occur-lang
  apo : ph t s -> (p ...)  
  [(apo both t s) (bot)]
  [(apo (! t ()) u s) (bot) (side-condition (term (u . <: . t)))]
  [(apo (t ()) u s) (bot) (side-condition (term (no-overlap u t)))]
  [(apo ph u 0) ()]
  [(apo (t (pe_1 ...)) u ((pe_2 ...) x)) ((t (pe_1 ... pe_2 ...) x))]
  [(apo (! t (pe_1 ...)) u ((pe_2 ...) x)) ((! t (pe_1 ... pe_2 ...) x))])

(define-metafunction occur-lang
  flatten : any ... -> any  
  [(flatten (any_1 ...) ...) (any_1 ... ...)])

(define-metafunction occur-lang
  comb-filter : f f f -> f
  ;; silly student expansion
  ;; (if e #t #f)
  [(comb-filter f (any (any_1 ... bot any_2 ...)) ((any_3 ... bot any_4 ...) any_5)) f]

  ;; if we know the test is true or false
  ;; (if #t e2 e3)
  [(comb-filter (any (any_1 ... bot any_2 ...)) f_2 f_3) f_2]
  ;; (if #f e2 e3)
  [(comb-filter ((any_1 ... bot any_2 ...) any) f_2 f_3) f_3]
  
  ;; and (if e1 e2 #f)
  [(comb-filter ((p_1+ ...) (p_1- ...)) ((p_2+ ...) (p_2- ...)) ((any_2 ... bot any_3 ...) any_1))
   ((p_1+ ... p_2+ ...) ())
   (side-condition (enable-T-IfAnd))]
  
  ;; or (if (number? x) #t (boolean? x))
  [(comb-filter (((t_1 pi x) p_1+ ...) ((! t_1 pi_1 x_1) p_1- ...)) (any_1 (any_2 ... bot any_3 ...)) (((t_3 pi_3 x_3) p_3+ ...) ((! t_3 pi x) p_3- ...)))
   ,(*term-let occur-lang
               ([((p_r+ ...) (p_r- ...))
                 (term (comb-filter ((p_1+ ...) (p_1- ...))
                                    (any_1 (any_2 ... bot any_3 ...))
                                    ((p_3+ ...) (p_3- ...))))])
               (term ((((U t_1 t_3) pi x) p_r+ ...) ((! (U t_1 t_3) pi x) p_r- ...))))
   (side-condition (enable-T-IfOr))]
  
  ;; or (if e1 #t e3)
  [(comb-filter ((p_1+ ...) (p_1- ...)) (any_1 (any_2 ... bot any_3 ...)) ((p_3+ ...) (p_3- ...)))
   (() (p_1- ... p_3- ...))
   (side-condition (enable-T-IfOr))]
  
  ;; not sure if this is ever useful
  ;; (if e1 e e)
  [(comb-filter f_tst f_1 f_2) 
   f_1
   (side-condition (lset= equal? (term f_1) (term f_2)))]
  
  [(comb-filter f_1 f_2 f_3) (() ())])

(define-metafunction occur-lang
  restrict : t t -> t
  [(restrict t u) (U) (side-condition (term (no-overlap t u)))]
  [(restrict (union t ...) u) (union (restrict t u) ...)]
  [(restrict t u) t (side-condition (term (t . <: . u)))]
  [(restrict t u) u])

(define-metafunction occur-lang
  remove : t t -> t
  [(remove t u) (U) (side-condition (term (t . <: . u)))]
  [(remove (union t ...) u) (union (remove t u) ...)]
  [(remove t u) t])

(define no-overlap-recur (make-parameter #t))

(define-metafunction occur-lang
  no-overlap : t t -> any
  [(no-overlap top t) #f]
  [(no-overlap t top) #f]
  [(no-overlap N #t) #t]
  [(no-overlap N #f) #t]
  [(no-overlap N (pr t_1 t_2)) #t]
  [(no-overlap #t (pr t_1 t_2)) #t]
  [(no-overlap #f (pr t_1 t_2)) #t]
  [(no-overlap N (t ... -> u : fh ... : sh)) #t]
  [(no-overlap #t (t ... -> u : fh ... : sh)) #t]
  [(no-overlap #f (t ... -> u : fh ... : sh)) #t]
  [(no-overlap (pr t_1 t_2) (t ... -> u : fh ... : sh)) #t]
  [(no-overlap (union t ...) u) (all (no-overlap t u) ...)]
  [(no-overlap t u) 
   #t
   (side-condition (and (no-overlap-recur)
                        (parameterize ([no-overlap-recur #f]) (term (no-overlap u t)))))]
  [(no-overlap t u) #f])

(define-metafunction occur-lang
  update : t ph -> t
  [(update (pr t_1 t_2) (u (car pe ...)))
   (pr (update t_1 (u (pe ...))) t_2)]
  [(update (pr t_1 t_2) (u (cdr pe ...)))
   (pr t_1 (update t_2 (u (pe ...))))]
  [(update (pr t_1 t_2) (! u (car pe ...)))
   (pr (update t_1 (! u (pe ...))) t_2)]
  [(update (pr t_1 t_2) (! u (cdr pe ...)))
   (pr t_1 (update t_2 (! u (pe ...))))]
  [(update t (u ())) (restrict t u)]
  [(update t (! u ())) (remove t u)])

(define-metafunction occur-lang
  env+ : G (p ...) -> G
  [(env+ G ()) G]
  [(env+ ((x_1 t_1) ... (x_t t_t) (x_2 t_2) ...) ((t pi x_t) p_rest ...))
   (env+ ((x_1 t_1) ...
          (x_t (update t_t (t pi)))
          (x_2 t_2) ...)
         (p_rest ...))]
  [(env+ ((x_1 t_1) ... (x_t t_t) (x_2 t_2) ...) ((! t pi x_t) p_rest ...))
   (env+ ((x_1 t_1) ...
          (x_t (update t_t (! t pi)))
          (x_2 t_2) ...)
         (p_rest ...))]
  [(env+ ((x t) ...) (bot p_rest ...)) ([x_fresh (union)] (x (union)) ...)
                                       (where x_fresh ,(gensym))]
  ;; the relevant variable not in G
  [(env+ G (p p_rest ...)) (env+ G (p_rest ...))])

(define-metafunction occur-lang
  lookup : G x -> t
  [(lookup ((x_1 t_1) ... (x t) (x_2 t_2) ...) x) t]
  [(lookup G x) ,(error "variable not found in env" (term G) (term x))])


(define (find x l) (if (null? l) #f
                       (if (equal? x (car l)) 
                           0
                           (cond [(find x (cdr l)) => add1]
                                 [else #f]))))


(define-metafunction occur-lang
  proctype? : t -> boolean
  [(proctype? (t_f ... -> t_r : ((ph_f+ ...) (ph_f- ...)) ... : sh_f)) #t]
  [(proctype? any) #f])

;; the type rules!
(define-metafunction occur-lang
  tc : G e -> (t f s)
  ;; T-Bot
  [(tc (any_1 ... (x (union)) any_2 ...) e)
   ((U) (() ()) 0)
   (side-condition (T-Bot))]
  ;; T-Var
  [(tc G x) ((lookup G x) (((! #f () x)) ((#f () x))) (() x))]
  ;; T-Const
  [(tc G c) ((delta-t c) (() (bot)) 0)]
  ;; T-Num
  [(tc G number) (N (() (bot)) 0)]
  ;; T-True
  [(tc G #t) (#t (() (bot)) 0)]
  ;; T-False
  [(tc G #f) (#f ((bot) ()) 0)]
  ;; T-Cons
  [(tc G (cons e_1 e_2))
   ,(*term-let occur-lang
               ([(t_1 f_1 s_1) (term (tc G e_1))]
                [(t_2 f_2 s_2) (term (tc G e_2))])
               (term ((pr t_1 t_2) (() (bot)) 0)))]
  ;; T-Car
  [(tc G (car e_1))
   ,(*term-let occur-lang
               ([((pr t_1 t_2) f s) (term (tc G e_1))]
                [s_r (match/redex occur-lang s
                       [((pe ...) x) (term ((car pe ...) x))]
                       [any (term 0)])]
                [f_r (term (apply-filter (((! #f (car))) ((#f (car)))) (pr t_1 t_2) s))])
               (term (t_1 f_r s_r)))]
  ;; T-Car
  [(tc G (cdr e_1))
   ,(*term-let occur-lang
               ([((pr t_1 t_2) f s) (term (tc G e_1))]
                [s_r (match/redex occur-lang s
                       [((pe ...) x) (term ((cdr pe ...) x))]
                       [any (term 0)])]
                [f_r (term (apply-filter (((! #f (cdr))) ((#f (cdr)))) (pr t_1 t_2) s))])
               (term (t_2 f_r s_r)))]
  ;; T-Not
  [(tc G (not e))
   ,(*term-let occur-lang
               ([(t ((p_+ ...) (p_- ...)) s) (term (tc G e))])
               (term ((U #t #f) ((p_- ...) (p_+ ...)) 0)))
   (side-condition (T-Not))]
  ;; T-Abs
  [(tc G (lambda ([x : u] ...) e))
   ,(*term-let occur-lang
               ([(t ((p_+ ...) (p_- ...)) s) (term (tc ((x u) ... . G) e))]
                [f (term ((p_+ ...) (p_- ...)))]
                [sh_new (match/redex occur-lang s
                          [0 (term 0)]
                          [(pi x_i) (match/redex occur-lang ,(find (term x_i) (term (x ...)))
                                      [n (term (pi n))]
                                      [#f 0])])]
                [(fh ...)
                 (term ((abstract-filter x f) ...))])
               (term ((u ... -> t : fh ... : sh_new) (() (bot)) 0)))]
  ;; T-App
  [(tc G (e_op e_args ...))
   ,(*term-let occur-lang
               ([(t_op ((p_op+ ...) (p_op- ...)) s_op) (term (tc G e_op))]
                [((t_a ((p_a+ ...) (p_a- ...)) s_a) ...) (term ((tc G e_args) ...))])
      (define-metafunction occur-lang
        tc/one : t -> (t f s)
        [(tc/one (t_f ... -> t_r : fh_f ... : sh_f))
         ,(*term-let occur-lang 
            ([boolean_subs? (term (all (t_a . <: . t_f) ...))]
             [any (unless (term boolean_subs?)
                    (error 'tc "not all subtypes: ~a ~a" (term (t_a ...)) (term (t_f ...))))]
             [(((p_+ ...) (p_- ...)) ...) (term ((apply-filter fh_f t_a s_a) ...))]                                
             [s_r (match/redex occur-lang sh_f
                    [((pe_* ...) i) (match/redex occur-lang ,(list-ref (term (s_a ...)) (term i))
                                      [((pe ...) x) (term ((pe_* ... pe ...) x))]
                                      [any 0])]
                    [any 0])])
            (term (t_r ((p_+ ... ...) (p_- ... ...)) s_r)))])
      (match/redex occur-lang t_op
        [(side-condition t (term (proctype? t)))
         (term (tc/one t))]
        [(side-condition (union t ...) (enable-union->))
         (*term-let occur-lang
           ([((t_r f_r s_r) ...) (term ((tc/one t) ...))])
           (term ((U t_r ...) (() ()) 0)))]
        [any (error 'tc "~a not a proc type in ~a" (term t_op) (term e_op))]))]
  ;; T-If
  [(tc G (if e_tst e_thn e_els))
   ,(*term-let occur-lang
               ([(t_tst f_tst s_tst) (term (tc G e_tst))]
                [((p_tst+ ...) (p_tst- ...)) (term f_tst)]
                [(t_thn f_thn s_thn) (term (tc (env+ G (p_tst+ ...)) e_thn))]
                [(t_els f_els s_els) (term (tc (env+ G (p_tst- ...)) e_els))]
                [f (term (comb-filter f_tst f_thn f_els))])
               (term ((U t_thn t_els) f 0)))] 
  )


(define (tc-fun ex [env '()])
  (unless (redex-match occur-lang e ex)
    (error 'tc-fun "not an expression"))
  (term (tc ,env ,ex)))


(define-metafunction occur-lang 
  check-sub : any any -> boolean
  ;; the first term failed, so everything's ok
  [(check-sub #f any) #t]
  ;; the second term failed, so we have an error:
  [(check-sub any #f) #f]
  ;; the real case
  [(check-sub (t f s) ((t_s f_s s_s) ...))
   (all (t_s . <: . t) ...
        (subset-f f_s f) ...
        (sub-s s_s s) ...)])