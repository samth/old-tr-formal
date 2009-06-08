#lang scheme

(require redex mzlib/trace)

(define-language
  env-lang
  [(d e f) x (λ x e) (e e) (bind ρ e) v (if e e e)]
  [t (ρ e)]
  [x variable-not-otherwise-mentioned]
  [v (close ρ (λ x e)) number #t #f]
  [E hole
     (if E e e)
     (v E)
     (E e)]
  [F (ρ E)]
  [(ρ env) ((x v) ...)])

(define e? (redex-match env-lang e))

(define-metafunction env-lang
  lookup : x ρ -> v
  [(lookup x ((x_1 v_1) ... (x v) (x_2 v_2) ...)) 
   v
   (side-condition (not (memq (term x) (term (x_1 ...)))))])

(define R
  (reduction-relation
   env-lang
   #:domain t
   #:arrow -->
   [==> ((close ρ (λ x e_body)) v_arg)
        (bind ((x v_arg) . ρ) e_body)
        E-Fun]
   [==> (if #f e_2 e_3)
        e_3
        E-IfFalse]
   [==> (if v_1 e_2 e_3)
        e_2
        E-IfTrue
        (side-condition (term v_1))]   
   [--> (ρ (in-hole E_1 x))
        (ρ (lookup x ρ))
        E-Var]
   [--> (ρ (in-hole E_1 (λ x e)))
        (ρ (in-hole E_1 (close ρ (λ x e))))
        E-Close]
   [==> (bind ρ e_1)
        (bind ρ e_2)
        (side-condition (step-R (term ρ) (term e_1)))
        (where (ρ_2 e_2) ,(step-R (term ρ) (term e_1)))
        E-Bind]   
   [==> (bind ρ v)
        v        
        E-BindVal]   
   with
   [(--> (in-hole F_1 a) (in-hole F_1 b)) (==> a b)]))

(define (step-R env trm)
  (match (apply-reduction-relation R (term (,env ,trm)))
    [(list) #f]
    [(list e) e]
    [_ (error "too many results")]))

(define (run e)
  (traces R (term (() ,e))))

(define e1 (term ((λ x x) 1)))
(define e2 (term ((λ x ((λ x x) x)) 0)))
(define e3 (term ((λ x (((λ x x) (λ x x)) x)) 0)))