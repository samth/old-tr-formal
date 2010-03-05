theory New
imports Main

begin


datatype pe = CarPE | CdrPE
types 
  name = "string"
  path = "pe list"
  lobj = "path option"
  obj = "(path * name) option"

datatype ty =
  Any ("A") |
  N |
  True | False |
  PairTy "ty" "ty" | 
  Union "ty list" |
  Arr "ty" "ty" "(lprp list * lprp list)" "lobj"

and tprp = TF "ty" "path" | FF "ty" "path"

and lprp = 
  LBot | LTop | LFP tprp | FP tprp name | LConj lprp lprp ("_ \<and> _")
  | LImp lprp lprp ("_ \<supset> _") | LDisj lprp lprp ("_ \<or> _")

datatype prp =
  Bot | Top | FP tprp name | Conj prp prp ("_ \<and> _")
  | Imp prp prp ("_ \<supset> _")  | Disj prp prp( "_ \<or> _")

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

fun update :: "ty \<Rightarrow> tprp \<Rightarrow> ty" where
  "update (PairTy T S) (TF T' (CarPE#ps)) = PairTy (update T (TF T' ps)) S"
  |"update (PairTy T S) (FF T' (CarPE#ps)) = PairTy (update T (FF T' ps)) S"
  |"update (PairTy S T) (TF T' (CdrPE#ps)) = PairTy S (update T (TF T' ps))"
  |"update (PairTy S T) (FF T' (CdrPE#ps)) = PairTy S (update T (FF T' ps))"
  | "update T (TF S []) = restrict T S"
  | "update T (FF S []) = remove T S"

fun del :: "const \<Rightarrow> val \<Rightarrow> val option"
  where
  "del x y = None"

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

inductive subtype :: "ty \<Rightarrow> ty \<Rightarrow> bool" ("\<turnstile> _ <: _" 100) where
  s_refl[intro]: "\<turnstile> T <: T"
  | s_top[intro]: "\<turnstile> T <: A"
  | s_pair[intro]: "\<lbrakk> \<turnstile> T <: S; \<turnstile> T' <: S'\<rbrakk> \<Longrightarrow> \<turnstile> PairTy T T' <: PairTy S S'" 
  | s_fun[intro]: "\<lbrakk> \<turnstile> T <: S; \<turnstile> T' <: S'\<rbrakk> \<Longrightarrow> \<turnstile> Arr T S' LFS LO <: Arr S T' LFS LO"
  | s_union_super[intro]: "\<lbrakk>\<turnstile> T <: S; S : set ts\<rbrakk> \<Longrightarrow> \<turnstile> T <: Union ts"
  | s_union_sub[intro]: "\<lbrakk>S : set ts \<Longrightarrow> \<turnstile> S <: T\<rbrakk> \<Longrightarrow> \<turnstile> Union ts <: T"

lemma s_trans: "\<lbrakk>\<turnstile> S <: T; \<turnstile> T <: U\<rbrakk> \<Longrightarrow> \<turnstile> S <: U" sorry

lemma empty_is_bot: "\<turnstile> Union [] <: T" by auto

inductive proves :: "env \<Rightarrow> prp \<Rightarrow> bool" ("_ \<turnstile> _" 100) where
  e_atom[intro]: "p : set G \<Longrightarrow> G \<turnstile> p"
  | e_bot[intro]: "G \<turnstile> Bot \<Longrightarrow> G \<turnstile> p"
  | e_imp_i[intro]: "(P#G) \<turnstile> P' \<Longrightarrow> G \<turnstile> Imp P P'"
  | e_imp_e[intro]: "G \<turnstile> Imp P P' \<Longrightarrow> G \<turnstile> P \<Longrightarrow> G \<turnstile> P'"
  | e_or_e[intro]: "\<lbrakk>G \<turnstile> Disj P P'; (P#G) \<turnstile> Q ; (P'#G) \<turnstile> Q\<rbrakk> \<Longrightarrow> G \<turnstile> Q"
  | e_or_i1[intro]: "G \<turnstile> P \<Longrightarrow> G \<turnstile> Disj P P'"
  | e_or_i2[intro]: "G \<turnstile> P' \<Longrightarrow> G \<turnstile> Disj P P'"
  | e_and_i[intro]: "G \<turnstile> P' \<Longrightarrow> G \<turnstile> P \<Longrightarrow> G \<turnstile> Conj P P'"
  | e_and_e1[intro]: "G \<turnstile> Conj P P' \<Longrightarrow> G \<turnstile> P"
  | e_and_e2[intro]: "G \<turnstile> Conj P P' \<Longrightarrow> G \<turnstile> P'"
  | e_update[intro]: "\<lbrakk>G \<turnstile> FP (TF T pi') x; G \<turnstile> FP (TF T' (pi@pi')) x\<rbrakk> 
  \<Longrightarrow> G \<turnstile> FP (TF (update T (TF T' pi)) pi') x"
  | e_updatenot[intro]: "\<lbrakk>G \<turnstile> FP (TF T pi) x; G \<turnstile> FP (FF T' (pi@pi')) x\<rbrakk> 
  \<Longrightarrow> G \<turnstile> FP (TF (update T (FF T' pi)) pi') x"

fun apo :: "name \<Rightarrow> prp \<Rightarrow> lprp option" where
"apo x Bot = Some LBot"
| "apo x (FP F pi x') = (if (x = x') then (Some (LFP F pi)) else None)"



