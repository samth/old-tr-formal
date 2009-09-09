#lang scheme/base

(require mzlib/trace
         (except-in scheme/list flatten #;lookup)
         scheme/match 
         scheme/class
         mred/mred
         redex
         #;
         "utils.ss"
         (for-syntax scheme/base)
         #;
         (planet cobbe/environment:3/environment))

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
  [boolean #t #f]
  ;; constants
  [c add1 number? boolean? zero? not cons car cdr cons? procedure?]
  ;; variables
  [x (variable-except lambda add1 if number? boolean? zero? not cons car cdr cons? procedure?)]

  ;; contexts
  [E (v ... E e ...) (if E e e) hole]

  ;; types
  [(t u) N proctop top #t #f (t ... -> t : fh ... : sh) (pr t t) (U t ...)]
  ;; effects
  [f ((p ...) (p ...))]
  [fh ((ph ...) (ph ...))]
  [p (t pi x) (! t pi x) bot]
  
  [ph (t pi) (! t pi) both]
  
  [s 0 (pi x)]
  [sh 0 (pi i)]
  
  [pi (pe ...)]
  [pe car cdr]
  
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
  [((U t_1 ...) . <: . t_2)
   #t
   (side-condition (term (all (t_1 . <: . t_2) ...)))]
  ;; S-UnionSuper
  [(t_2 . <: . (U t_1 ...))
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
  u : (x ...) ... -> (x ...)
  [(u) ()]
  [(u (x_1 ...)) (x_1 ...)]
  [(u (x_1 ...) (x_2 ...)) (x_1 ... x_2 ...)]
  [(u (x_1 ...) any_2 ...) (u (x_1 ...) (u any_2 ...))])

;; free-vars : e -> (listof x)
(define-metafunction occur-lang
  free-vars : e -> (x ...)
  [(free-vars (e_1 e_2)) (u (free-vars e_1) (free-vars e_2))]
  [(free-vars x_1) (x_1)]
  [(free-vars (if e_1 e_2 e_3)) (u (free-vars e_1) (free-vars e_2) (free-vars e_3))]
  [(free-vars (lambda ([x_1 : t] ...) e_1))
   (var- (x_1 ...) (free-vars e_1))]
  [(free-vars v_1) ()])

(define-metafunction occur-lang
  var- : (x ...) (x ...) -> (x ...)
  [(var- any_1 any_2) ,(remq* (term any_1) (term any_2))])

(define (closed e) (equal? (term (free-vars ,e)) null))

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
   (where any (begin (display (term ((apo ph_+ t s) ...)))
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
  [(apo any_1 any_2 any_3) 
   #f                           
   (side-condition (and (printf "args: ~a\n" (term (any_1 any_2 any_3))) #f))]
  [(apo both t s) (bot)]
  [(apo (! t pi) u s) (bot) (side-condition (term (u . <: . t)))]
  [(apo (t pi) u s) (bot) (side-condition (and (printf "in no-overlap~n")(term (no-overlap u t))))]
  [(apo ph u 0) ()]
  [(apo (t (pe_1 ...)) u ((pe_2 ...) x)) ((t (pe_1 ... pe_2 ...) x))]
  [(apo (! t (pe_1 ...)) u ((pe_2 ...) x)) ((! t (pe_1 ... pe_2 ...) x))])

(define-metafunction occur-lang
  flatten : any ... -> any  
  [(flatten (any_1 ...) ...) (any_1 ... ...)])

;; conservative
(define-metafunction occur-lang
  comb-filter : f f f -> f
  [(comb-filter f_1 f_2 f_3) (() ())])

(define-metafunction occur-lang
  restrict : t t -> t
  [(restrict t u) (U) (side-condition (term (no-overlap t u)))]
  [(restrict (U t ...) u) (U (restrict t u) ...)]
  [(restrict t u) t (side-condition (term (t . <: . u)))]
  [(restrict t u) u])

(define-metafunction occur-lang
  remove : t t -> t
  [(remove t u) (U) (side-condition (term (t . <: . u)))]
  [(remove (U t ...) u) (U (remove t u) ...)]
  [(remove t u) t])

(define no-overlap-recur (make-parameter #t))

(define-metafunction occur-lang
  no-overlap : t t -> any
  [(no-overlap N #t) #t]
  [(no-overlap N #f) #t]
  [(no-overlap N (pr t_1 t_2)) #t]
  [(no-overlap #t (pr t_1 t_2)) #t]
  [(no-overlap #f (pr t_1 t_2)) #t]
  [(no-overlap N (t ... -> u : fh ... : sh)) #t]
  [(no-overlap #t (t ... -> u : fh ... : sh)) #t]
  [(no-overlap #f (t ... -> u : fh ... : sh)) #t]
  [(no-overlap (pr t_1 t_2) (t ... -> u : fh ... : sh)) #t]
  [(no-overlap (U t ...) u) (all (no-overlap t u) ...)]
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
  [(env+ ((x_1 t_1) ... (x t_t) (x_2 t_2) ...) ((t pi x_t) p_rest ...))
   (env+ ((x_1 t_1) ...
          (x_t (update t_t (t pi)))
          (x_2 t_2) ...)
         (p_rest ...))]
  [(env+ ((x_1 t_1) ... (x t_t) (x_2 t_2) ...) ((! t pi x_t) p_rest ...))
   (env+ ((x_1 t_1) ...
          (x_t (update t_t (! t pi)))
          (x_2 t_2) ...)
         (p_rest ...))]
  [(env+ ((x t) ...) (bot p_rest)) ((x (U)) ...)]
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


(define-syntax term-let*
  (syntax-rules ()
    [(term-let* () . e) (term-let () . e)]
    [(term-let* (cl . rest) . e) (term-let (cl) (term-let* rest . e))]))

(define-syntax (*term-let-one stx)
  (syntax-case stx ()
    [(_ lang ([pat rhs]) . body)
     (with-syntax ([(mf-name) (generate-temporaries (list 'mf))])
       (quasisyntax/loc stx
         (let ([r rhs])
           (define-metafunction lang 
             mf-name : any -> any
             [(mf-name pat) ,(begin . body)]
             [(mf-name any) ,#,(syntax/loc stx (error 'term-let "term ~a did not match pattern ~a" r 'pat))])
           (term (mf-name ,r)))))]))

(define-syntax *term-let
  (syntax-rules ()
    [(*term-let lang () . e) (term-let () . e)]
    [(*term-let lang (cl . rest) . e) (*term-let-one lang (cl) (*term-let lang rest . e))]))

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
               ([any (printf "started\n")]
                [(t_op ((p_op+ ...) (p_op- ...)) s_op) (term (tc G e_op))]
                [((t_a ((p_a+ ...) (p_a- ...)) s_a) ...) (term ((tc G e_args) ...))]
                [any (display (term t_op))]
                [any (unless (term (proctype? t_op))
                       (error 'tc "~a not a proc type in ~a" (term t_op) (term e_op)))]
                [(t_f ... -> t_r : fh_f ... : sh_f) (term t_op)]
                [#t (term (all (t_a . <: . t_f) ...))]
                [any (display "got here 1")]
                [(((p_+ ...) (p_- ...)) ...) (term ((apply-filter fh_f t_a s_a) ...))]                
                [any (display "got here 4\n")]
                [s_r (match (term sh_f)                       
                       [(list pi* i)
                        (match (list-ref (term (s_a ...)) i)
                          [(list pi x) (list (append pi* pi) x)]
                          [_ 0])]
                       [_ 0])]
                [any (display "got here 5\n")])
               (term (t_r ((p_+ ... ...) (p_- ... ...)) s_r)))]
  #;
  ;; T-If
  [(tc G (if e_tst e_thn e_els)
       ,(*term-let occur-lang
                   ([(t_tst f_tst s_tst) (term (tc G e_tst))]
                    [((p_tst+ ...) (p_tst- ...)) (term f_tst)]
                    [(t_thn f_thn s_thn) (term (tc (env+ G (p_tst+ ...) e_thn)))]
                    [(t_els f_els s_els) (term (tc (env+ G (p_tst- ...) e_els)))]
                    [f (term (comb-filter f_tst f_thn f_els))])
                   (term ((U t_thn t_els) f 0))))]
  )