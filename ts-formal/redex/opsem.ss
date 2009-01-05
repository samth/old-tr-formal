#lang scheme/base

(require mzlib/trace
         (except-in scheme/list flatten)
         (only-in srfi/1 lset=)
         scheme/match 
         scheme/class
         mred/mred
         redex
         "utils.ss"
         (for-syntax scheme/base))

(provide (all-defined-out))

(define T-Bot (make-parameter #t))
(define T-Not (make-parameter #t))

(define-language occur-lang
  ;; expressions
  [e x
     (e e ...) 
     (if e e e)
     wrong
     v]
  ;; values
  [v (lambda ([x : t] ...) e) number #t #f c (cons v v)]
  [boolean #t #f]
  ;; constants
  [c add1 number? boolean? zero? not cons car cdr cons? procedure?]
  ;; variables
  [(x y) (variable-except lambda add1 if number? boolean? zero? not cons car cdr cons? procedure?)]

  ;; contexts
  [E (v ... E e ...) (if E e e) hole]

  ;; types
  [(t u) N proctop top #t #f (t ... -> t : fh ... : sh) (pr t t) (union t ...)]
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
  [((t_a ... -> t_r : ph_1 ... : sh_1) . <: . (u_a ... -> u_r : ph_2 ... : sh_2))
   #t
   (side-condition (term (t_r . <: . u_r)))
   (side-condition (term (all (u_a . <: . t_a) ...)))
   (side-condition (or (equal? (term sh_1) (term sh_2))
                       (equal? (term sh_2) (term 0))))
   (side-condition (term (all (subset ph_1 ph_2) ...)))]
  ;; otherwise
  [(t_1 . <: . t_2) #f])

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

(define reductions
  (reduction-relation 
   occur-lang
   [==> ((lambda ([x_1 : t_1] ...) e_body) v_arg ...)
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


(define-metafunction occur-lang
  abstract-filter : x f -> fh
  [(abstract-filter x ((p_1 ...) (p_2 ...)))
   ((flatten (abo x p_1) ...)
    (flatten (abo x p_2) ...))])

(define-metafunction occur-lang
  apply-filter : fh t s -> f
  [(apply-filter ((ph_+ ...) (ph_- ...)) t s)
   ((flatten (apo ph_+ t s) ...)
    (flatten (apo ph_- t s) ...))
   #;
   (side-condition
    (begin 
      (printf "in apply-filter \n~a \n~a \n~a\n~a~n"
              (term (ph_+ ...)) (term (ph_- ...)) (term t) (term s))
      (display (term ((apo ph_+ t s) ...)))
      (newline)
      (display (term ((apo ph_- t s) ...)))
      (newline)
      (term 1)))])

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

;; conservative
(define-metafunction occur-lang
  comb-filter : f f f -> f
  #;
  [(comb-filter any_1 any_2 any_3) 
   #f
   (side-condition
    (and (printf "~a~n" `(comb-filter  ,(term any_1) ,(term any_2) ,(term any_3))) #f))]
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
   ((p_1+ ... p_2+ ...) ())]
  
  ;; or (if (number? x) #t (boolean? x))
  [(comb-filter (((t_1 pi x) p_1+ ...) ((! t_1 pi_1 x_1) p_1- ...)) (any_1 (any_2 ... bot any_3 ...)) (((t_3 pi_3 x_3) p_3+ ...) ((! t_3 pi x) p_3- ...)))
   ,(*term-let occur-lang
               ([((p_r+ ...) (p_r- ...))
                 (term (comb-filter ((p_1+ ...) (p_1- ...))
                                    (any_1 (any_2 ... bot any_3 ...))
                                    ((p_3+ ...) (p_3- ...))))])
               (term ((((U t_1 t_3) pi x) p_r+ ...) ((! (U t_1 t_3) pi x) p_r- ...))))]
  
  ;; or (if e1 #t e3)
  [(comb-filter ((p_1+ ...) (p_1- ...)) (any_1 (any_2 ... bot any_3 ...)) ((p_3+ ...) (p_3- ...)))
   (() (p_1- ... p_3- ...))]
  
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
  [(update (pr t_1 t_2) (u (car pi)))
   (pr (update t_1 (u pi)) t_2)]
  [(update (pr t_1 t_2) (u (cdr pi)))
   (pr t_1 (update t_2 (u pi)))]
  [(update (pr t_1 t_2) (! u (car pi)))
   (pr (update t_1 (! u pi)) t_2)]
  [(update (pr t_1 t_2) (! u (cdr pi)))
   (pr t_1 (update t_2 (! u pi)))]
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
  [(env+ ((x t) ...) (bot p_rest ...)) ((x (union)) ...)]
  ;; the relevant variable not in G
  [(env+ G (p p_rest ...)) (env+ G (p_rest ...))])

(define-metafunction occur-lang
  lookup : G x -> t
  [(lookup ((x_1 t_1) ... (x t) (x_2 t_2) ...) x) t]
  [(lookup G x) ,(error "variable not found in env" (term G) (term x))])

;; the type rules!

(define (find x l) (if (null? l) #f
                       (if (equal? x (car l)) 
                           0
                           (cond [(find x (cdr l)) => add1]
                                 [else #f]))))


(define-metafunction occur-lang
  proctype? : t -> boolean
  [(proctype? (t_f ... -> t_r : ((ph_f+ ...) (ph_f- ...)) ... : sh_f)) #t]
  [(proctype? any) #f])

(define-metafunction occur-lang
  tc : G e -> (t ((p ...) (p ...)) s)
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
                [s_r (match (term s)
                       [(list pi x) (term (,(cons 'car pi) ,x))]
                       [_ (term 0)])]
                [f_r (term (apply-filter (((! #f (car))) ((#f (car)))) (pr t_1 t_2) s))])
               (term (t_1 f_r s_r)))]
  ;; T-Car
  [(tc G (cdr e_1))
   ,(*term-let occur-lang
               ([((pr t_1 t_2) f s) (term (tc G e_1))]
                [s_r (match (term s)
                       [(list pi x) (term (,(cons 'cdr pi) ,x))]
                       [_ (term 0)])]
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
                [sh_new (match (term s)
                          [0 (term 0)]
                          [(list pi x_i) 
                           (let ([idx (find x_i (term (x ...)))])
                             (if idx
                                 (list pi idx)
                                 0))])]
                [(fh ...)
                 (term ((abstract-filter x f) ...))])
               (term ((u ... -> t : fh ... : sh_new) (() (bot)) 0)))]
  ;; T-App
  [(tc G (e_op e_args ...))
   ,(*term-let occur-lang
               ([(t_op ((p_op+ ...) (p_op- ...)) s_op) (term (tc G e_op))]
                [((t_a ((p_a+ ...) (p_a- ...)) s_a) ...) (term ((tc G e_args) ...))]                
                [any (unless (term (proctype? t_op))
                       (error 'tc "~a not a proc type in ~a" (term t_op) (term e_op)))]
                [(t_f ... -> t_r : fh_f ... : sh_f) (term t_op)]
                [#t (term (all (t_a . <: . t_f) ...))]                
                [(((p_+ ...) (p_- ...)) ...) (term ((apply-filter fh_f t_a s_a) ...))]                                
                [s_r (match (term sh_f)                       
                       [(list pi* i)
                        (match (list-ref (term (s_a ...)) i)
                          [(list pi x) (list (append pi* pi) x)]
                          [_ 0])]
                       [_ 0])])
               (term (t_r ((p_+ ... ...) (p_- ... ...)) s_r)))]
  ;; T-If
  [(tc G (if e_tst e_thn e_els))
   ,(*term-let occur-lang
               ([(t_tst f_tst s_tst) (term (tc G e_tst))]
                [((p_tst+ ...) (p_tst- ...)) (term f_tst)]
                [(t_thn f_thn s_thn) (term (tc (env+ G (p_tst+ ...)) e_thn))]
                [(t_els f_els s_els) (term (tc (env+ G (p_tst- ...)) e_els))]
                [f (term (comb-filter f_tst f_thn f_els))])
               (term ((U t_thn t_els) f 0)))]  
  ;; T-Bot
  [(tc (any_1 ... (x (union)) any_2 ...) e)
   (term ((U) (() ()) 0))
   (side-condition (T-Bot))]
  )
(define (mk-result t #:then [thn null] #:else [els null] #:s [s 0])
  (term (,t (,thn ,els) ,s)))

(define (var-res t var #:path [p null])
  (mk-result t 
             #:then (list (term (! #f ,p ,var)))
             #:else (list (term (#f ,p ,var)))
             #:s (term (,p ,var))))

(define (type-res t var #:path [p null])
  (mk-result (term (U #t #f))
             #:then (list (term (,t ,p ,var)))
             #:else (list (term (! ,t ,p ,var)))))

(define (*and a b)
  (term (if ,a ,b #f)))

(define (*or a b)
  (term (if ,a #t ,b)))

(define-syntax-rule (truety t)
  (term (,t (() (bot)) 0)))

(define-syntax predtype
  (syntax-rules ()
    [(_ ty in p) (term (,in -> (U #t #f) : (((,ty ,p)) ((! ,ty ,p))) : 0))]
    [(_ ty in) (predtype ty in (term ()))]
    [(_ ty) (predtype ty (term top))]))

(test--> reductions (if #t 1 2) 1)
(test-equal (term (no-overlap #t (U #t #f))) #f)

(test-equal (term (tc ([x top]) x))
            (var-res (term top) (term x)))

(test-equal (term (tc ([x (pr top top)]) (car x)))
            (var-res (term top) (term x) #:path (term (car))))

(test-equal (term (tc ([x top]) (number? x)))
            (type-res (term N) (term x)))

(test-equal (term (tc ([x (pr top top)]) (number? (car x))))
            (type-res (term N) (term x) #:path (list 'car)))

(test-equal (term (tc () #f))
            (term (#f ((bot) ()) 0)))

(test-equal (term (tc () 3))
            (term (N (() (bot)) 0)))

(test-equal (term (tc () #t))
            (term (#t (() (bot)) 0)))

(test-equal (term (tc ([x top] [y top])
                      ,(*and (term (number? x)) (term (boolean? y)))))
            (term ((U #t #f) (((N () x) ((U #t #f) () y)) ()) 0)))

(test-equal (term (tc ([x top] [y top])
                      ,(*or (term (number? x)) (term (boolean? y)))))
            (term ((U #t #f) (() ((! N () x) (! (U #t #f) () y))) 0)))

(test-equal (term (tc ([x top])
                      ,(*and (term (number? x)) (term (boolean? x)))))
            (term ((U #t #f) (((N () x) ((U #t #f) () x)) ()) 0)))

(test-equal (term (tc ([x top])
                      ,(*or (term (number? x)) (term (boolean? x)))))
            (type-res (term (U N #t #f)) (term x)))


(test-equal (term (tc () (lambda ([x : top]) x)))
            (truety (term (top -> top : (((! #f ())) ((#f ()))) : (() 0)))))

(test-equal (term (tc () number?))
            (truety (predtype (term N))))

(test-equal (term (tc () (lambda ([x : top]) (number? x))))
            (truety (predtype (term N))))

(test-equal (term (tc () (cons 1 2)))
            (truety (term (pr N N))))

(test-equal (term (tc () (lambda ([x : (pr top top)]) (number? (car x)))))
            (truety (predtype (term N) (term (pr top top)) (term (car)))))

(test-equal (term (tc () (lambda ([x : (pr top top)]) (number? (cdr x)))))
            (truety (predtype (term N) (term (pr top top)) (term (cdr)))))

(test-equal (term (tc () (lambda ([x : (pr top top)]) (not (number? (car x))))))
            (truety (term ((pr top top) -> (U #t #f) : (((! N (car))) ((N (car)))) : 0))))

(test-equal (term (tc () (lambda ([x : top]) #f)))
            (truety (term (top -> #f : ((both) ()) : 0))))

(test-equal (term (tc () (lambda ([x : top] [y : top]) (number? x))))
            (truety (term (top top -> (U #t #f) : (((N ())) ((! N ()))) (() ()) : 0))))

(test-results)