theory New
imports Main

begin


datatype pe = CarPE | CdrPE
types 
  name = "string"
  path = "pe list"
  obj = "(path * name) option"

datatype ty =
  Any ("A") |
  N |
  True | False |
  PairTy "ty" "ty" | 
  Union "ty list" |
  Arr name "ty" "ty" "(prp * prp)" "obj"

and tprp = TF "ty" | FF "ty" 

and prp = 
  Bot | Top | FP tprp path name | Conj prp prp ("_ \<and> _")
  | Imp prp prp ("_ \<supset> _") | Disj prp prp ("_ \<or> _")

types env = "prp list"

datatype const = ADD1 | ZEROP | NUMP | BOOLP | PROCP | NOT  | CONSP | CAR | CDR 
datatype expr = Var name | App "expr" "expr" | Iff "expr" "expr" "expr" 
  | CONS "expr" "expr" | Const const | Bool bool | Number int | Lam "name" "ty" "expr"

abbreviation
  "lam" :: "name \<Rightarrow> ty \<Rightarrow> expr \<Rightarrow> expr" ("Lam [_:_]._" [100,100,100] 100) where
  "Lam[x:T].b \<equiv> expr.Lam x T b"

datatype val = vCONS val val | vConst const | vBool bool | vNumber int | vClos "(name ~=> val)" name ty expr

types valenv = "(name ~=> val)"

consts restrict :: "ty \<Rightarrow> ty \<Rightarrow> ty"
remove :: "ty \<Rightarrow> ty \<Rightarrow> ty"
del :: "const \<Rightarrow> val \<Rightarrow> val option"
delt :: "const \<Rightarrow> ty"

fun update :: "ty \<Rightarrow> tprp \<Rightarrow> path \<Rightarrow> ty" where
  "update (PairTy T S) tp (CarPE#ps) = PairTy (update T tp ps) S"
  | "update (PairTy T S) tp (CdrPE#ps) = PairTy T (update S tp ps)"
  | "update T (TF S) [] = restrict T S"
  | "update T (FF S) [] = remove T S"


abbreviation
  "vClos" :: "valenv \<Rightarrow> name \<Rightarrow> ty \<Rightarrow> expr \<Rightarrow> val" ("[_, Lam [_:_]._]" [100,100,100,100] 100) where
  "[\<rho>, Lam[x:T].b] \<equiv> val.vClos \<rho> x T b"


inductive eval :: "valenv \<Rightarrow> expr \<Rightarrow> val \<Rightarrow> bool" ("_ \<turnstile> _ \<Down> _" [100,100,100]   100) where
  b_var[intro]: "\<rho> x = Some v \<Longrightarrow> \<rho>\<turnstile>Var x \<Down> v"
  | b_const[intro]: "\<rho>\<turnstile>Const c \<Down> vConst c"
  | b_num[intro]: "\<rho>\<turnstile>Number c \<Down> vNumber c"
  | b_bool[intro]: "\<rho>\<turnstile>Bool c \<Down> vBool c"
  | b_abs[intro]: "\<rho> \<turnstile> (Lam [x:T].body)  \<Down> [\<rho>, Lam [x:T].body]"
  | b_delta[intro]: "\<lbrakk>\<rho>\<turnstile>e \<Down> (vConst c); \<rho>\<turnstile>e' \<Down> v ; del c v = Some v' \<rbrakk> \<Longrightarrow>  \<rho>\<turnstile>(App e e) \<Down> v'"
  | b_beta[intro]: "\<lbrakk>\<rho> \<turnstile> e \<Down> [\<rho>',Lam [x:T].body]; \<rho> \<turnstile> e' \<Down> v ;  \<rho>'(x \<mapsto> v)\<turnstile> body\<Down> v' \<rbrakk> \<Longrightarrow>  \<rho>\<turnstile>(App e e) \<Down> v'"
  | b_cons[intro]: "\<lbrakk>\<rho>\<turnstile>e1 \<Down> v1 ;  \<rho>\<turnstile>e2 \<Down> v2 \<rbrakk> \<Longrightarrow> \<rho> \<turnstile> (CONS e1 e2)  \<Down> vCONS v1 v2"
  | b_if_true[intro]: "\<lbrakk>\<rho>\<turnstile>e1 \<Down> v1 ; v1 \<noteq> vBool false ; \<rho>\<turnstile>e2 \<Down> v\<rbrakk> \<Longrightarrow> \<rho>\<turnstile> (Iff e1 e2 e3)  \<Down> v"
  | b_if_false[intro]: "\<lbrakk>\<rho>\<turnstile>e1 \<Down> (vBool false)  ; \<rho>\<turnstile>e3 \<Down> v\<rbrakk> \<Longrightarrow> \<rho>\<turnstile> (Iff e1 e2 e3)  \<Down> v"

inductive proves :: "env \<Rightarrow> prp \<Rightarrow> bool" ("_ \<turnstile> _" 100) where
  l_atom[intro]: "p : set G \<Longrightarrow> G \<turnstile> p"
  | l_top[intro]: "\<Gamma> \<turnstile> Top"
  | l_bot[intro]: "G \<turnstile> Bot \<Longrightarrow> G \<turnstile> p"
  | l_imp_i[intro]: "(P#G) \<turnstile> P' \<Longrightarrow> G \<turnstile> Imp P P'"
  | l_imp_e[intro]: "G \<turnstile> Imp P P' \<Longrightarrow> G \<turnstile> P \<Longrightarrow> G \<turnstile> P'"
  | l_or_e[intro]: "\<lbrakk>G \<turnstile> P \<and> P'; (P#G) \<turnstile> Q ; (P'#G) \<turnstile> Q\<rbrakk> \<Longrightarrow> G \<turnstile> Q"
  | l_or_i1[intro]: "(G \<turnstile> P) \<or> (G \<turnstile> P') \<Longrightarrow> G \<turnstile> (P \<or> P')"
  | l_and_i[intro]: "\<lbrakk>G \<turnstile> P' ; G \<turnstile> P\<rbrakk> \<Longrightarrow> G \<turnstile> P \<and> P'"
  | l_and_e1[intro]: "G \<turnstile> Conj P P' \<Longrightarrow> G \<turnstile> P"
  | l_and_e2[intro]: "G \<turnstile> Conj P P' \<Longrightarrow> G \<turnstile> P'"
  | l_update[intro]: "\<lbrakk>G \<turnstile> FP (TF T) (pi@pi') x; G \<turnstile> FP tp pi' x\<rbrakk> 
  \<Longrightarrow> G \<turnstile> FP (TF (update T tp pi)) pi' x"

inductive subtype :: "ty \<Rightarrow> ty \<Rightarrow> bool" ("\<turnstile> _ <: _" 100) where
  s_refl[intro]: "\<turnstile> T <: T"
  | s_top[intro]: "\<turnstile> T <: A"
  | s_pair[intro]: "\<lbrakk> \<turnstile> T <: S; \<turnstile> T' <: S'\<rbrakk> \<Longrightarrow> \<turnstile> PairTy T T' <: PairTy S S'" 
  | s_fun[intro]: "\<lbrakk> \<turnstile> T <: S; \<turnstile> T' <: S' ; (obj = obj') | (obj' = None) ; [F1] \<turnstile> F1' ; [F2] \<turnstile> F2' \<rbrakk> \<Longrightarrow> \<turnstile> Arr x T S' (F1,F2) obj <: Arr x S T' (F1',F2') obj'"
  | s_union_super[intro]: "\<lbrakk>\<turnstile> T <: S; S : set ts\<rbrakk> \<Longrightarrow> \<turnstile> T <: Union ts"
  | s_union_sub[intro]: "\<lbrakk>S : set ts \<Longrightarrow> \<turnstile> S <: T\<rbrakk> \<Longrightarrow> \<turnstile> Union ts <: T"

lemma s_trans: "\<lbrakk>\<turnstile> S <: T; \<turnstile> T <: U\<rbrakk> \<Longrightarrow> \<turnstile> S <: U" sorry

lemma empty_is_bot: "\<turnstile> Union [] <: T" by auto

function subs_obj :: "obj \<Rightarrow> obj \<Rightarrow> name \<Rightarrow> obj" ("_[_/_]" 100) where
  "subs_obj None ob n = None"
  |"x \<noteq> z \<Longrightarrow> subs_obj (Some (pi,x)) ob z = Some (pi, x)"
  |"x = z \<Longrightarrow> subs_obj (Some (pi,x)) None z = None"
  |"x = z \<Longrightarrow> subs_obj (Some (pi,x)) (Some (pi',y)) z = Some ((pi@pi'),y)"
by (auto, atomize_elim, auto)

function subs_prop :: "prp \<Rightarrow> obj \<Rightarrow> name \<Rightarrow> prp" ("_[_/_]" 100) and
  (*subs_prop_set :: "prp * prp \<Rightarrow> obj \<Rightarrow> name \<Rightarrow> prp * prp" ("_[_/_]" 100) and *)
  subs_tprop :: "tprp \<Rightarrow> obj \<Rightarrow> name \<Rightarrow> tprp" and
  subs_ty :: "ty \<Rightarrow> obj \<Rightarrow> name \<Rightarrow> ty" ("_[_/_]" 100) where
"subs_prop Top ob n = Top"
  | "subs_prop Bot ob n = Bot"
  | "subs_prop (Imp p1 p2) ob n = Imp (subs_prop p1 ob n) (subs_prop p2 ob n)"
  | "subs_prop (Conj p1 p2) ob n = Conj (subs_prop p1 ob n) (subs_prop p2 ob n)"
  | "subs_prop (Disj p1 p2) ob n = Disj (subs_prop p1 ob n) (subs_prop p2 ob n)"
  | "subs_prop (FP f pi x) None z = (if x = z then Top else FP (subs_tprop f None z) pi x)"
  | "subs_prop (FP f pi x) (Some (pi',y)) z = (if x = z then FP (subs_tprop f (Some (pi',y)) z) (pi@pi') y else FP (subs_tprop f (Some (pi',y)) z) pi x)"

  | "subs_tprop (TF t) ob n = TF (subs_ty t ob n)"
  | "subs_tprop (FF t) ob n = FF (subs_ty t ob n)"

  |"subs_ty (Union ts) ob n = Union (map (\<lambda> t. subs_ty t ob n) ts)"
  | "subs_ty (PairTy t1 t2) ob n = (PairTy (subs_ty t1 ob n) (subs_ty t2 ob n))"
  | "subs_ty (Arr m t1 t2 (f1,f2) ob') ob n = 
  (if (m = n) then (Arr m t1 t2 (f1,f2) ob') else
  (Arr m (subs_ty t1 ob n) (subs_ty t2 ob n) (subs_prop f1 ob n,subs_prop f2 ob n) (subs_obj ob' ob n)))"
  | "subs_ty t ob n = t"
  sorry
termination sorry
