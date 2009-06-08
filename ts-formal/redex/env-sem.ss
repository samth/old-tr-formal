#lang scheme

(require redex)

(define-language
  env-lang
  [(d e f) x (λ x e) (e e) (bind ρ e) v (if e e e)]
  [t (ρ e)]
  [x variable-not-otherwise-mentioned]
  [v (close ρ (λ x e)) number]
  [E hole
     (if E e e)
     (v E)
     (E e)
     (bind ρ E)]
  [F (ρ E)]
  [(ρ env) ((x v) ...)])

(define e? (redex-match env-lang e))

(define-metafunction env-lang
  lookup : x ρ -> v
  [(lookup x ((x_1 v_1) ... (x v) (x_2 v_2) ...)) v])

(define R
  (reduction-relation
   env-lang
   #:domain t
   #:arrow -->
   [==> ((close ρ (λ x e_body)) v_arg)
        (bind ((x v) . ρ) e_body)
        E-Fun]
   [==> (if #f e_2 e_3)
        e_3
        E-IfFalse]
   [==> (if v_1 e_2 e_3)
        e_2
        E-IfTrue
        (side-condition (term v_1))]   
   [--> (ρ (in-hole E_1 x))
        (lookup x ρ)
        E-Var]
   [--> (ρ (in-hole E_1 (λ x e)))
        (ρ (in-hole E_1 (close ρ (λ x e))))
        E-Close]
   [==> (bind ρ e_1)
        e_2
        (side-condition (step-R (term ρ) (term e_1)))
        (where (ρ_2 e_2) ,(step-R (term ρ) (term e_1)))
        E-Bind]
   with
   [(--> (in-hole F_1 a) (in-hole F_1 b)) (==> a b)]))

(define (step-R env trm)
  (match (apply-reduction-relation R (term (,env ,trm)))
    [(list) #f]
    [(list (list _ trm*)) (list env trm*)]
    [_ (error "too many results")]))