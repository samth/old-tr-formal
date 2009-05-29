(*
New Version
Started Jan 15, 2009

Using Isabelle repository snapshot 2eadbc24de8c (13-Jan-2009)

*)

theory TS
imports Nominal  AssocList

begin

section {* Datatypes *}

subsection {* Datatype definitions and infrastructure *}

atom_decl name

datatype pe = Car | Cdr

types
  sh =  "(pe list) option"
  s = "(pe list * name) option" 

datatype builtin = ADD1 | ZEROP| CAR | CDR | NOT | CONSP | NUMBERP | BOOLEANP | PROCEDUREP

(* Types *)
datatype ty =  
  Top | N | TT | FF | Pr "ty" "ty" ("<_,_>") | Arr "ty" "ty" "fh" "sh" ("_ \<rightarrow> _ : _ : _" [100,100] 100) | Union "ty list"  
(* Latent Filter Sets *)
and fh = FH "ph list"  "ph list"
(* Latent Filters *)
and ph = TEH "ty" "pe list" | NTEH "ty" "pe list" | BotH

constdefs B_def[simp]:"B ==  Union [TT, FF]"

primrec (unchecked perm_pe)
  "pi\<bullet>Car = Car"
  "pi\<bullet>Cdr = Cdr"



primrec (unchecked perm_bi)
  "pi\<bullet>NOT = NOT"
  "pi\<bullet>ADD1 = ADD1"
  "pi\<bullet>CAR = CAR"
  "pi\<bullet>CDR = CDR"
  "pi\<bullet>CONSP = CONSP"
  "pi\<bullet>ZEROP = ZEROP"
  "pi\<bullet>NUMBERP = NUMBERP"
  "pi\<bullet>BOOLEANP = BOOLEANP"
  "pi\<bullet>PROCEDUREP = PROCEDUREP"

primrec (unchecked perm_ty)
  "pi\<bullet>(ty.Top) = ty.Top"
  "pi\<bullet>(N) = N"
  "pi\<bullet>(TT) = TT"
  "pi\<bullet>(FF) = FF"
  "pi\<bullet>(\<tau> \<rightarrow> \<sigma> : F : S) = ((pi\<bullet>\<tau>) \<rightarrow> (pi\<bullet>\<sigma>) : (pi\<bullet>F) : (pi\<bullet>S))"
  "pi\<bullet><\<tau>,\<sigma>> = <pi\<bullet>\<tau>,pi\<bullet>\<sigma>>"
  "pi\<bullet>(Union l) = Union (pi\<bullet>l)" 

  "pi\<bullet>(FH l1 l2) = FH (pi\<bullet>l1)(pi\<bullet>l2)"

  "pi\<bullet>BotH = BotH"
  "pi\<bullet>(TEH t l) = TEH (pi\<bullet>t) (pi\<bullet>l)"
  "pi\<bullet>(NTEH t l) = NTEH (pi\<bullet>t) (pi\<bullet>l)"

declare perm_pe.simps[eqvt]
declare perm_ty.simps[eqvt]
declare perm_bi.simps[eqvt]

subsection {* Trivial theorems about nominal-ness of basic data *}

lemma perm_bi[simp]:
  fixes pi :: "name prm"
  and bi :: "builtin"
  shows "pi \<bullet> bi = bi"
  by (induct bi) auto

lemma perm_pe[simp]:
  fixes pi :: "name prm"
  and pe :: "pe"
  shows "pi \<bullet> pe = pe"
  by (induct pe) auto

lemma perm_pe_list[simp]:
  fixes pi :: "name prm"
  and pe :: "pe list"
  shows "pi \<bullet> pe = pe"
  by (induct pe) auto

lemma perm_sh[simp]:
  fixes pi :: "name prm"
  and pe :: "sh"
  shows "pi \<bullet> pe = pe"
  by (induct pe) auto
  
lemma perm_ty_F_ty_list[simp]:
  fixes pi ::"name prm"
  and   \<tau>  ::"ty"
  and   Ts ::"ty list"
  and   f  ::"fh"
  and   p  :: "ph"
  and ps :: "ph list"
  and ps2 :: "ph list"
  shows "pi\<bullet>\<tau> = \<tau>" and "pi\<bullet>f = f" and "pi\<bullet>p = p" and "pi\<bullet>Ts = Ts" and "pi\<bullet>ps = ps" and "pi\<bullet>ps2 = ps2"
  by (induct \<tau> and f and p rule: ty_fh_ph.inducts) simp_all

instance ty :: pt_name
by intro_classes auto

instance ty :: fs_name
by intro_classes (simp add: supp_def)

instance fh :: pt_name
by intro_classes auto

instance fh :: fs_name
by intro_classes (simp add: supp_def)

instance pe :: pt_name
by intro_classes auto

instance pe :: fs_name
by intro_classes (simp add: supp_def)

instance ph :: pt_name
by intro_classes auto

instance ph :: fs_name
by intro_classes (simp add: supp_def)

instance builtin :: pt_name
by intro_classes auto

instance builtin :: fs_name
by intro_classes (simp add: supp_def)


lemma fresh_data[simp]:
  fixes x  ::"name"
  and   \<tau>  ::"ty"
  and   f  ::"fh"
  and   p  :: "ph"
  and   bi :: builtin
  and   pe :: pe
  shows "x\<sharp>\<tau>" and "x\<sharp>f" and "x\<sharp>p" and "x\<sharp>pe" and "x\<sharp>bi"
  by (simp add: fresh_def supp_def)+


lemma supp_data[simp]:
  fixes \<tau>   ::"ty"
  and   f  ::"fh"
  and   p  :: "ph"
  and   bi :: builtin
  and   pe :: pe
  shows "supp \<tau> = ({}::name set)" 
  and "supp f = ({}::name set)"
  and "supp p = ({}::name set)"
  and "supp bi = ({}::name set)"
  and "supp pe = ({}::name set)"
  by (simp_all add: supp_def)

subsection {* Now we can define terms and filters *}

nominal_datatype p = Bot | TE "ty" "pe list" "name" | NTE "ty" "pe list" "name"


nominal_datatype trm = 
    Var "name"
  | App "trm" "trm"
  | Abs "\<guillemotleft>name\<guillemotright>trm" "ty"
  | Iff "trm" "trm" "trm"
  | Num "nat"
  | Bool "bool"
  | BI "builtin"
  | CONS "trm" "trm"

abbreviation
  "lam" :: "name \<Rightarrow> ty \<Rightarrow> trm \<Rightarrow> trm" ("Lam [_:_]._" [100,100,100] 100) where
  "Lam[x:T].b \<equiv> trm.Abs x b T"


instantiation trm :: size
begin

nominal_primrec
  size_trm :: "trm \<Rightarrow> nat"
  where
  "size_trm (Var x) = 1"
  | "size_trm (BI b) = 1"
  | "size_trm (Bool b) = 1"
  | "size_trm (Num b) = 1"
  | "size_trm (App t1 t2) = (max (size_trm t1) (size_trm t2)) + 1"
  | "size_trm (CONS t1 t2) = (max (size_trm t1) (size_trm t2)) + 1"
  | "size_trm (Iff t1 t2 t3) = (max (size_trm t1) (max (size_trm t2) (size_trm t3))) + 1"
  | "size_trm (Lam [a:T].e) = (size_trm e) + 1"
  by (auto simp add: fresh_nat, finite_guess+, fresh_guess+)

instance proof qed

end

instantiation trm :: ord
begin

definition
"less_eq_trm (t1 :: trm) (t2 :: trm) == size t1 <= size t2"
definition
"less_trm (t1 :: trm) (t2 :: trm) == size t1 < size t2"

instance proof qed

end

declare less_trm_def[simp]
declare less_eq_trm_def[simp]


subsection {* complete induction on terms *}

lemma trm_comp_induct[consumes 0, case_names Var App Lam BI Num Bool Iff CONS]:
  fixes P::"'a::fs_name \<Rightarrow> trm \<Rightarrow> bool"
  and t::"trm"
  and x::"'a::fs_name"
  assumes a1:"!! n z. (!! x t. (t < Var n) \<Longrightarrow> P x t) \<Longrightarrow> P z (Var n)"
  and a2:"!! t1 t2 z. (!! x t. (t < App t1 t2) \<Longrightarrow> P x t) \<Longrightarrow> (!! x. P x t1) \<Longrightarrow> (!! x . P x t2)
  \<Longrightarrow> P z (App t1 t2)"
  and a3:"!! a b z T. \<lbrakk>a \<sharp> z ; (!! x t. (t < Lam[a:T].b)  \<Longrightarrow> P x t)\<rbrakk> \<Longrightarrow> (!! x . P x b) \<Longrightarrow> P z (Lam[a:T].b)"
  and a4:"!! b z. (!! x t. (t < BI b) \<Longrightarrow> P x t) \<Longrightarrow> P z (BI b)"
  and a5:"!! n z. (!! x t. (t < Num n)  \<Longrightarrow> P x t) \<Longrightarrow> P z (Num n)"
  and a6:"!! b z. (!! x t. (t < Bool b) \<Longrightarrow> P x t) \<Longrightarrow> P z (Bool b)"
  and a7:"!! t1 t2 t3 z. (!! x t. t < (Iff t1 t2 t3) \<Longrightarrow> P x t) 
  \<Longrightarrow> (!! x. P x t1) \<Longrightarrow> (!! x . P x t2) \<Longrightarrow> (!! x. P x t3) \<Longrightarrow> P z (Iff t1 t2 t3)"
  and a8:"!! t1 t2 z. (!! x t. (t < CONS t1 t2) \<Longrightarrow> P x t) \<Longrightarrow> (!! x. P x t1) \<Longrightarrow> (!! x . P x t2)
  \<Longrightarrow> P z (CONS t1 t2)"
  shows "P x t"
proof (induct t arbitrary: x taking:"(% t :: trm. size t)" rule: measure_induct_rule)
  case (less s x) thus ?case using a1 a2 a3 a4 a5 a6 a7 a8
    by (nominal_induct s avoiding: x rule: trm.strong_induct) auto 
qed  

section {* Free Variables and Closed Terms *}

subsection {* closed terms *}

constdefs
  fv :: "trm \<Rightarrow> name set"
  fv_def[simp]:"fv e == ((supp e):: name set)"

  closed :: "trm \<Rightarrow> bool"
  closed_def: "closed e == (fv e = {})"

lemma closed_lam: -- "A statement about the free variables of lam bodies"
  assumes "closed (Lam[x:T].b)" (is "closed ?e")
  shows "fv b <= {x}"
proof -
  have "(supp ([x].b)::name set) = supp b - {x}" 
    using fs_name_class.axioms abs_fun_supp[of b x] pt_name_inst at_name_inst by auto
  hence "supp ?e = ((((supp b):: name set) - {x}) :: name set)" using  trm.supp by simp
  thus ?thesis using prems closed_def by auto 
qed

lemma closed_eqvt[eqvt]:
  fixes pi::"name prm"
  shows "closed e \<Longrightarrow> closed (pi\<bullet>e)"
proof -
  assume c:"closed e"
  have A:"(pi\<bullet>fv e) = fv (pi\<bullet>e)" using pt_perm_supp[of pi e] at_name_inst pt_name_inst by auto
  hence "fv e = {}" using closed_def c by simp
  hence "(pi\<bullet>fv e) = {}" using empty_eqvt[of pi] by auto
  hence "closed (pi\<bullet>e)" using A closed_def by auto
  thus ?thesis .
qed    

section {* Values *}

inductive values :: "trm \<Rightarrow> bool" ("_ : values" [80])
where
  abs_value[simp]: "Lam[x:t].b : values"
|  bi_value[simp]: "BI c : values"
|  num_value[simp]: "Num n : values"
|  bool_value[simp]: "Bool b : values"
|  cons_value[simp]: "\<lbrakk>v1 : values; v2 : values\<rbrakk> \<Longrightarrow> CONS v1 v2 : values"

equivariance values
nominal_inductive values by (simp add: abs_fresh)

abbreviation
  "in_values" :: "trm \<Rightarrow> bool" ("_ \<in> values" [100] 100) where
  "e \<in> values \<equiv> (e : values)"

abbreviation
  "not_in_values" :: "trm \<Rightarrow> bool" ("_ \<notin>  values" [100] 100) where
  "e \<notin> values \<equiv> (~ e : values)"


section {* Operational Semantics *}

subsection {* Substitution *}

nominal_primrec
  subst :: "trm \<Rightarrow> name \<Rightarrow> trm \<Rightarrow> trm" ("_[_::=_]")
  where
 "(Var x)[y::=t'] = (if x=y then t' else (Var x))"
 |"(App t1 t2)[y::=t'] = App (t1[y::=t']) (t2[y::=t'])"
 |"x\<sharp>(y,t',T) \<Longrightarrow> (Lam[x:T].t)[y::=t'] = Lam[x:T].(t[y::=t'])"
 |"(Iff tst thn els)[y::=t'] = (Iff (tst[y::=t']) (thn[y::=t']) (els[y::=t']))"
 |"(BI c)[y::=t'] = (BI c)"
 |"(Num c)[y::=t'] = (Num c)"
 |"(Bool c)[y::=t'] = (Bool c)"
 |"(CONS a b)[y::=t'] = (CONS (a[y::=t']) (b[y::=t']))"
  by (finite_guess+, auto simp add: abs_fresh, fresh_guess+)

lemma subst_eqvt[simp, eqvt]:
  fixes pi:: "name prm"
  and   t1:: "trm"
  and   t2:: "trm"
  and   a :: "name"
  shows "pi\<bullet>(t1[b::=t2]) = (pi\<bullet>t1)[(pi\<bullet>b)::=(pi\<bullet>t2)]"
by (nominal_induct t1 avoiding: b t2 rule: trm.strong_induct)
   (auto simp add: perm_bij fresh_prod fresh_atm fresh_bij)

subsection {* Variables, Substitution and Reduction *}

lemma subst_rename[rule_format]: 
  shows "c\<sharp>t1 \<longrightarrow> (t1[a::=t2] = ([(c,a)]\<bullet>t1)[c::=t2])"
by (nominal_induct t1 avoiding: a c t2 rule: trm.strong_induct)
   (auto simp add: calc_atm fresh_atm abs_fresh fresh_nat trm.inject perm_nat_def perm_bool)

lemma forget: 
  assumes a: "a\<sharp>t1"
  shows "t1[a::=t2] = t1"
  using a
by (nominal_induct t1 avoiding: a t2 rule: trm.strong_induct)
   (auto simp add: abs_fresh fresh_atm)

lemma fresh_fact: 
  fixes a::"name"
  assumes a: "a\<sharp>t1" "a\<sharp>t2"
  shows "a\<sharp>t1[b::=t2]"
using a
by (nominal_induct t1 avoiding: a b t2 rule: trm.strong_induct)
   (auto simp add: abs_fresh fresh_atm)

lemma fresh_fact':
  fixes a::"name"
  assumes a: "a\<sharp>t2"
  shows "a\<sharp>t1[a::=t2]"
  using a 
  by (nominal_induct t1 avoiding: a t2 rule: trm.strong_induct)
     (auto simp add: abs_fresh fresh_atm fresh_nat fresh_bool)  

lemma fv_lam:
  fixes name
  shows "fv (Lam[name:T].body) =  fv body - {name}"
proof -
  have sT:"supp T = ({} :: name set)" by auto
  have "fv (Lam[name:T].body) = (supp ([name].body):: name set) \<union> supp T" using trm.supp by auto
  also have "\<dots> = (supp ([name].body):: name set)" using sT by auto
  also have "\<dots> = supp body - ({name} :: name set)" 
    using  abs_fun_supp[of body name] at_name_inst pt_name_inst fs_name1[of body] by simp
  also have "\<dots> = fv body - {name}" by simp
  finally show "fv (Lam[name:T].body) = fv body - {name}" by simp
qed

lemma supp_elem_subst:
  fixes x :: name  and b :: name
  assumes a:"x : supp (t1[b::=t2]) "
  shows "x : (supp t1) \<or>  x : (supp t2)" 
  using fresh_fact  a 
  by (auto simp add: fresh_def) 

lemma subst_closed:
  assumes a:"e1[x::=e0] = e2" and "closed e0"
  shows "fv e2 <= fv e1"
  using prems supp_elem_subst[of _ e1 x e0] closed_def fv_def fresh_def by auto

lemma subst_only_var_closed:
  assumes "closed e0" and "fv e1 <= {x}"
  shows "closed (e1[x::=e0])" (is "closed ?e2")
proof -
  have "x \<sharp> ?e2" using prems fresh_def[of x e0] closed_def fresh_fact' by auto
  thus "closed ?e2" using prems subst_closed[of e1 x e0 ?e2] fresh_def[of x ?e2] closed_def by auto
qed


subsection {* Delta Function *}


nominal_primrec
  add1_fun :: "trm \<Rightarrow> trm option"
  where
  "add1_fun (Num n) = Some (Num (n+1))"
  |"add1_fun (Lam[x:ty].b) = None"
  |"add1_fun (Iff a b c) = None"
  |"add1_fun (App a b) = None"
  |"add1_fun (Bool a) = None"
  |"add1_fun (BI a) = None"
  |"add1_fun (Var a) = None"
  |"add1_fun (CONS a b) = None"
  by (auto, finite_guess+, fresh_guess+)

nominal_primrec
  zerop_fun :: "trm \<Rightarrow> trm option"
  where
  "zerop_fun (Num n) = Some (Bool (n=0))"
  |"zerop_fun (Lam[x:ty].b) = None"
  |"zerop_fun (Iff a b c) = None"
  |"zerop_fun (App a b) = None"
  |"zerop_fun (Bool a) = None"
  |"zerop_fun (BI a) = None"
  |"zerop_fun (Var a) = None"
  |"zerop_fun (CONS a b) = None"
  by (auto, finite_guess+, fresh_guess+)

nominal_primrec
  not_fun :: "trm \<Rightarrow> trm option"
  where
  "not_fun (Num n) = (Some (Bool False))"
  |"not_fun (Lam[x:ty].b) = (Some (Bool False))"
  |"not_fun (Iff a b c) = (Some (Bool False))"
  |"not_fun (App a b) = (Some (Bool False))"
  |"not_fun (Bool b) = Some (Bool (~b))"
  |"not_fun (BI a) = (Some (Bool False))"
  |"not_fun (Var a) = (Some (Bool False))"
  |"not_fun (CONS a b) = (Some (Bool False))"
  by (auto, finite_guess+, fresh_guess+)
  

nominal_primrec
  booleanp_fun :: "trm \<Rightarrow> bool"
  where
  "booleanp_fun (Bool b) = True"
  |"booleanp_fun (Num n) = False"
  |"booleanp_fun (Abs a b c) = False"
  |"booleanp_fun (App a b) = False"
  |"booleanp_fun (BI c) = False"
  |"booleanp_fun (Var v) = False"
  |"booleanp_fun (Iff a b c) = False"
  |"booleanp_fun (CONS a b) = False"
  by (auto, finite_guess+, fresh_guess+)

nominal_primrec
  procp_fun :: "trm \<Rightarrow> bool"
  where
  "procp_fun (Bool b) = False"
  |"procp_fun (Num n) = False"
  |"procp_fun (Abs a b c) = True"
  |"procp_fun (App a b) = False"
  |"procp_fun (BI c) = True"
  |"procp_fun (Var v) = False"
  |"procp_fun (Iff a b c) = False"
  |"procp_fun (CONS a b) = False"
  by (auto, finite_guess+, fresh_guess+)

nominal_primrec
  numberp_fun :: "trm \<Rightarrow> bool"
  where
  "numberp_fun (Bool b) = False"
  |"numberp_fun (Num n) = True"
  |"numberp_fun (Abs a b c) = False"
  |"numberp_fun (App a b) = False"
  |"numberp_fun (BI c) = False"
  |"numberp_fun (Var v) = False"
  |"numberp_fun (Iff a b c) = False"
  |"numberp_fun (CONS a b) = False"
  by (auto, finite_guess+, fresh_guess+)

nominal_primrec
  consp_fun :: "trm \<Rightarrow> bool"
  where
  "consp_fun (Bool b) = False"
  |"consp_fun (Num n) = False"
  |"consp_fun (Abs a b c) = False"
  |"consp_fun (App a b) = False"
  |"consp_fun (BI c) = False"
  |"consp_fun (Var v) = False"
  |"consp_fun (Iff a b c) = False"
  |"consp_fun (CONS a b) = True"
  by (auto, finite_guess+, fresh_guess+)

nominal_primrec
  car_fun :: "trm \<Rightarrow> trm option"
  where
  "car_fun (Bool b) = None"
  |"car_fun (Num n) = None"
  |"car_fun (Abs a b c) = None"
  |"car_fun (App a b) = None"
  |"car_fun (BI c) = None"
  |"car_fun (Var v) = None"
  |"car_fun (Iff a b c) = None"
  |"car_fun (CONS a b) = Some a"
  by (auto, finite_guess+, fresh_guess+)

nominal_primrec
  cdr_fun :: "trm \<Rightarrow> trm option"
  where
  "cdr_fun (Bool b) = None"
  |"cdr_fun (Num n) = None"
  |"cdr_fun (Abs a b c) = None"
  |"cdr_fun (App a b) = None"
  |"cdr_fun (BI c) = None"
  |"cdr_fun (Var v) = None"
  |"cdr_fun (Iff a b c) = None"
  |"cdr_fun (CONS a b) = Some b"
  by (auto, finite_guess+, fresh_guess+)

fun
  \<Delta>  :: "builtin \<Rightarrow> trm \<Rightarrow> trm option"
  where
  "\<Delta> ADD1 t = add1_fun t"
  |"\<Delta> NOT t = not_fun t"
  |"\<Delta> ZEROP t = zerop_fun t"
  |"\<Delta> BOOLEANP t = Some (Bool (booleanp_fun t))"
  |"\<Delta> NUMBERP t = Some (Bool (numberp_fun t))"
  |"\<Delta> PROCEDUREP t = Some (Bool (procp_fun t))"
  |"\<Delta> CONSP t = Some (Bool (consp_fun t))"
  |"\<Delta> CAR t = car_fun t"
  |"\<Delta> CDR t = cdr_fun t"

declare perm_nat_def[simp] perm_bool[simp] supp_nat[simp] supp_bool[simp]

lemma delta_eqvt[eqvt]:
  fixes pi :: "name prm"
  and   b :: builtin
  and   t  :: "trm"
  shows "(pi\<bullet>(\<Delta> b t)) = \<Delta> (pi\<bullet>b) (pi\<bullet>t)"
  by (induct b) (nominal_induct t rule: trm.strong_induct, auto)+

lemma delta_closed:
  fixes b :: builtin and t::trm
  assumes a:"\<Delta> b t = Some v" and b:"closed t"
  shows "closed v"
  using a b
proof (induct b) 
  qed (nominal_induct t rule: trm.strong_induct, auto simp add: closed_def trm.supp)+

lemma delta_value:
  fixes b :: builtin and t::trm
  assumes a:"\<Delta> b t = Some v" and tv:"t : values"
  shows "v : values"
  using tv a
  proof (induct b)
    qed (induct t rule: values.induct, auto)+

subsection {* Evaluation contexts *}

inductive_set ctxt :: "(trm \<Rightarrow> trm) set"
where
  C_Hole[simp, intro]: "(%t. t) \<in> ctxt"
|  C_App1[simp, intro]: "E : ctxt \<Longrightarrow> (%t .  (App (E t) u)) : ctxt"
|  C_App2[simp, intro]: "E : ctxt \<Longrightarrow> v : values \<Longrightarrow> (%t . (App v (E t))) : ctxt"
|  C_Cons1[simp, intro]: "E : ctxt \<Longrightarrow> (%t .  (CONS (E t) u)) : ctxt"
|  C_Cons2[simp, intro]: "E : ctxt \<Longrightarrow> v : values \<Longrightarrow> (%t . (CONS v (E t))) : ctxt"
|  C_Iff[simp, intro]: "E : ctxt \<Longrightarrow> (%t . (Iff (E t) thn els)) : ctxt"

lemma ctxt_compose:
  assumes a:"E1 : ctxt" and b:"E2 : ctxt"
  shows "(%t. E1 (E2 t)) : ctxt"
  using a b
  by (induct E1) auto

constdefs
  closed_ctxt :: "(trm \<Rightarrow> trm) \<Rightarrow> bool"
  closed_ctxt_def[simp]:"closed_ctxt C == (C : ctxt \<and> (\<forall> e. closed e = closed (C e)))" --"3 is a trivially closed term"

lemma ctxt_closed:
  assumes "closed_ctxt C" 
  shows "closed (C e) = closed e"
  using prems by auto
 
lemma closed_in_ctxt:
  assumes "closed (C L)"
  and "C : ctxt"
  shows "closed L"
  using `C : ctxt` `closed (C L)`
  by (induct C) (auto simp add: closed_def trm.supp)

lemma closed_in_ctxt_closed_ctxt:
  assumes "closed e" and a:"C : ctxt" and "e = C L"
  shows "closed L \<and> closed_ctxt C"
proof -
  have b:"closed (C L)" using prems by simp
  have A:"closed_ctxt C" using a b
    by (induct C) (auto simp add: closed_def trm.supp)
  have B:"closed L" using closed_in_ctxt[of C L] prems by auto
  from A and B show ?thesis by simp
qed

subsection {* Reduction *}

inductive reduce :: "trm \<Rightarrow> trm \<Rightarrow> bool" ("_ \<hookrightarrow> _" [200,200] 200)
  where
  e_beta[simp]: "v : values \<Longrightarrow> x \<sharp> v \<Longrightarrow> (App (Lam[x:t].b) v) \<hookrightarrow> (b[x::=v])"
  | e_if_false[simp]: "Iff (Bool False) e1 e2 \<hookrightarrow> e2"
  | e_if_true[simp]: "v ~= Bool False \<Longrightarrow> v : values \<Longrightarrow> Iff v e1 e2 \<hookrightarrow> e1"
  | e_delta[simp]: "\<lbrakk>v : values; \<Delta> p v = Some e\<rbrakk> \<Longrightarrow> App (BI p) v \<hookrightarrow> e"

equivariance reduce

nominal_inductive reduce
  by (simp_all add: abs_fresh fresh_fact')

inductive
  "step" :: "trm\<Rightarrow>trm\<Rightarrow>bool" (" _ \<longrightarrow> _" [80,80]80)
where
  step_one[intro]:"\<lbrakk>E : ctxt; L \<hookrightarrow> R\<rbrakk> \<Longrightarrow> E L \<longrightarrow> E R"

inductive
step_multi :: "trm \<Rightarrow> trm \<Rightarrow> bool" (" _ \<longrightarrow>\<^sup>* _" [80,80] 80)
where 
  sm_refl:"a \<longrightarrow>\<^sup>* a"
| sm_trans:"a \<longrightarrow> b \<Longrightarrow> b \<longrightarrow>\<^sup>* c \<Longrightarrow> a \<longrightarrow>\<^sup>* c"

(* doesn't work *)
(* equivariance step *)
(* needs this lemma:
lemma context_red_eqv:"(pi \<bullet> E) (pi \<bullet> L) \<longrightarrow> (pi \<bullet> E) (pi \<bullet> R)"


lemma context_red_eqv:
  fixes E :: "trm \<Rightarrow> trm"
  assumes "E : ctxt" and "L \<hookrightarrow> R"
  shows "((pi \<bullet> E) (pi \<bullet> L)) \<longrightarrow> ((pi \<bullet> E) (pi \<bullet> R))"
  using prems
  sorry

*)



constdefs
reduce_forever :: "trm \<Rightarrow> bool"
"reduce_forever e == \<forall>e' . (e \<longrightarrow>\<^sup>* e') \<longrightarrow> (EX e''. e' \<longrightarrow> e'')"

subsection {* Reduction Closedness *}

lemma beta_closed_closed:
  assumes "closed (Lam[x:T].b)" and "closed v"
  shows "closed (b[x::=v])"
  using prems closed_lam subst_only_var_closed
  by auto

lemma reduce_closed:
  assumes "closed L" and "L \<hookrightarrow> R"
  shows "closed R"
  using `L \<hookrightarrow> R` `closed L` delta_closed beta_closed_closed
  by (induct rule: reduce.induct) (auto simp add: closed_def trm.supp)


lemma step_closed:
  assumes A:"closed e" and B:"(e :: trm) \<longrightarrow> e'"
  shows "closed e'"
proof - 
  from B obtain E L R where C:"E : ctxt"  "e = E L"  "L \<hookrightarrow> R"  "e' = E R" by induct auto
  also hence D:"closed L" "closed_ctxt E" using A closed_in_ctxt_closed_ctxt[of e E L] by auto
  ultimately show ?thesis using reduce_closed[of L R] ctxt_closed[of E R] by auto
qed


lemma multi_step_closed:
  assumes A:"closed e" and B:"e \<longrightarrow>\<^sup>* e'"
  shows "closed e'"
  using B A step_closed
  by induct auto



section {* Typing Constants *}

constdefs
predty :: "ty \<Rightarrow> ty"
[simp]:"predty t == (Top \<rightarrow> B : (FH [(TEH t [])] [(NTEH t [])]) : None)"
simplefun :: "ty \<Rightarrow> ty \<Rightarrow> ty" ("_ \<rightarrow>s _" 999)
[simp]:"simplefun t u == (t \<rightarrow> u : FH [] [] : None)"
proctop :: "ty"
[simp]:"proctop == Union [] \<rightarrow>s Top"


fun
  \<Delta>\<^isub>\<tau> :: "builtin \<Rightarrow> ty"
  where
  "\<Delta>\<^isub>\<tau> NUMBERP = predty N"
  |"\<Delta>\<^isub>\<tau> BOOLEANP = predty B"
  |"\<Delta>\<^isub>\<tau> PROCEDUREP = predty proctop"
  |"\<Delta>\<^isub>\<tau> CONSP = predty <Top,Top>"
  |"\<Delta>\<^isub>\<tau> ADD1 = (N \<rightarrow>s N)"
  |"\<Delta>\<^isub>\<tau> NOT = (Top \<rightarrow>s B)"
  |"\<Delta>\<^isub>\<tau> ZEROP = (N \<rightarrow>s B)"

lemma delta_t_eqvt[eqvt]:
  fixes pi :: "name prm"
  shows "pi \<bullet> \<Delta>\<^isub>\<tau> b = \<Delta>\<^isub>\<tau> (pi \<bullet> b)"
  by (induct b) auto

section {* Subtyping *}

subsection {* Subsubject *}

constdefs
sub_subjh :: "sh \<Rightarrow> sh \<Rightarrow> bool" ("\<turnstile> _ <sh: _")
where
"sub_subjh sh1 sh2 == sh2 = None \<or> sh1 = sh2"

lemma sub_subjh_eqvt[eqvt]:
  fixes pi :: "name prm"
  shows "pi \<bullet> sub_subjh sh1 sh2 = sub_subjh (pi \<bullet> sh1) (pi \<bullet> sh2)"
 by auto

lemma sub_subjh_trans[intro]:
  assumes 1:"\<turnstile> sh1 <sh: sh2" and 2:"\<turnstile> sh2 <sh: sh3"
  shows "\<turnstile> sh1 <sh: sh3" using 1 2
  by (auto simp add: sub_subjh_def)

subsection {* Subfilter *}

fun
  sub_fh :: "fh \<Rightarrow> fh \<Rightarrow> bool" ("\<turnstile> _ <fh: _")
  where
sub_fh_d:"sub_fh (FH l1 l2) (FH l3 l4) = (set l3 <= set l1 \<and> set l4 <= set l2)"

lemma sub_fh_trans[intro]:
  assumes 1:"\<turnstile> fh1 <fh: fh2" and 2:"\<turnstile> fh2 <fh: fh3"
  shows "\<turnstile> fh1 <fh: fh3" using 1 2
  by (cases fh1, cases fh2, cases fh3) (auto simp add: sub_fh_d)

lemma sub_fh_eqvt[eqvt]:
  fixes pi :: "name prm"
  shows "pi \<bullet> sub_fh sh1 sh2 = sub_fh (pi \<bullet> sh1) (pi \<bullet> sh2)"
 by auto

subsection {* Subtyping Relation *}  

inductive
  subtype :: "ty \<Rightarrow> ty \<Rightarrow> bool" ("\<turnstile> _ <: _" [60,60] 60)
where
  S_Refl[intro]: "\<turnstile> T <: T"
| S_Fun[intro]: "\<lbrakk>\<turnstile> S1 <: T1 ; \<turnstile> T2 <: S2 ; \<turnstile> fh <fh: fh' ; \<turnstile> sh <sh: sh'\<rbrakk> \<Longrightarrow> 
  \<turnstile> (T1 \<rightarrow> T2 : fh : sh) <: (S1 \<rightarrow> S2 : fh' : sh')"
| S_Top[simp]: "\<turnstile> T <: Top"
| S_Pair[intro]: "\<lbrakk>\<turnstile> T1 <: T2 ; \<turnstile> S1 <: S2\<rbrakk> \<Longrightarrow> \<turnstile> <T1,S1> <: <T2,S2>"
| S_UnionSuper[intro]: "\<lbrakk>T : set Ts ; \<turnstile> S <: T\<rbrakk> \<Longrightarrow> \<turnstile> S <: Union Ts"
| S_UnionSub[intro]: "\<lbrakk>!! T.( T : set Ts \<Longrightarrow> \<turnstile> T <: S)\<rbrakk> \<Longrightarrow> \<turnstile> Union Ts <: S"

equivariance subtype

nominal_inductive subtype done

lemma S_TopE:
  assumes a: "\<turnstile> Top <: T"
  shows "T = Top \<or> (EX Ts T'. T = Union Ts \<and> T' : set Ts \<and> \<turnstile> Top <: T')"
using a by (cases, auto)

lemma S_Bot[simp]:
  shows "\<turnstile> Union [] <: T"
  by auto

lemma funty_below_proctop:
  fixes S T :: ty
  and    fh :: fh
  and    sh :: sh
  shows "\<turnstile> T \<rightarrow> S : fh : sh <: proctop"
  using S_Fun by (cases fh) (auto simp add: sub_fh_d sub_subjh_def)

lemma union_size_ty:
  assumes "T : set Ts"
  shows "size T < size (Union Ts)"
  using prems 
  by (induct Ts) auto


fun size_ty3 :: "ty*ty*ty \<Rightarrow> nat"
where 
[simp]:"size_ty3 (a,b,c) = size a + size b + size c"

inductive_cases union_sub_cases[consumes 1, case_names 1 2 3 4]:"\<turnstile> Union Ts <: S"

lemma union_sub_elim: 
  assumes A:"\<turnstile> Union Ts <: T " (is "\<turnstile> ?S <: T") 
  and B:" T1 : set Ts "
  shows "\<turnstile> T1 <: T"
  using prems
proof (induct "X"=="(T1,?S,T)"  arbitrary: T1 Ts T taking: "size_ty3" rule: measure_induct_rule)
  case (less X)
  show " \<turnstile> T1 <: T" using `\<turnstile>  Union Ts <: T` less 
  proof (induct rule: union_sub_cases)
    case (3 T' Ts')
    have X_inst:"X = (T1, ty.Union Ts, T)" by fact
    have "size T' < size T" using 3 union_size_ty by auto
    hence "\<turnstile> T1 <: T'" using X_inst 3(4)[OF _ ` \<turnstile> ty.Union Ts <: T'` `T1 : set Ts`] by auto
    thus ?case using 3 by auto
  qed (auto)
qed

declare S_Refl[simp]

lemma sh_refl[simp]:
  "\<turnstile> sh <sh: sh"
  by (auto simp add: sub_subjh_def)

lemma fh_refl[simp]:
  "\<turnstile> fh <fh: fh"
  by (cases fh) (auto)

lemma S_ArrowE_left':
  fixes fh :: fh and sh :: sh and S\<^isub>1 S\<^isub>2 :: ty
  and T :: ty
  assumes a: "\<turnstile> (S\<^isub>1 \<rightarrow> S\<^isub>2 : fh : sh) <: T" (is "\<turnstile> ?S <: T")
  obtains
  "T = Top \<or> 
  (EX T\<^isub>1 T\<^isub>2 fh' sh' . T = ((T\<^isub>1 \<rightarrow> T\<^isub>2  : fh' : sh') :: ty) & \<turnstile> T\<^isub>1 <: S\<^isub>1 & \<turnstile> S\<^isub>2 <: T\<^isub>2
                  & \<turnstile> fh <fh: fh' & \<turnstile> sh <sh: sh')  \<or> 
  (EX Ts T\<^isub>1 . T = Union Ts & T\<^isub>1 : set Ts & \<turnstile> ?S <: T\<^isub>1)"
  using a by cases (auto simp add: ty.inject)

lemma S_UnionE_left:
  fixes S\<^isub>1 S\<^isub>2 T :: ty
  assumes a: "\<turnstile> <S\<^isub>1, S\<^isub>2> <: T" (is "\<turnstile> ?S <: T")
  obtains
  (top) "T = Top" |
  (fn) T\<^isub>1 T\<^isub>2  where "T = <T\<^isub>1, T\<^isub>2>" and "\<turnstile> S\<^isub>1 <: T\<^isub>1" and "\<turnstile> S\<^isub>2 <: T\<^isub>2" |
  (union) Ts T\<^isub>1 where "T = Union Ts" and "T\<^isub>1 : set Ts" and "\<turnstile> ?S <: T\<^isub>1"
using a by cases auto

lemma S_ArrowE_left[case_names Top Fun Union]:
  fixes fh :: fh and sh :: sh and S\<^isub>1 S\<^isub>2 :: ty
  and T :: ty
  assumes a: "\<turnstile> (S\<^isub>1 \<rightarrow> S\<^isub>2 : fh : sh) <: T" (is "\<turnstile> ?S <: T")
  obtains
  (top) "T = Top" |
  (fn) T\<^isub>1 T\<^isub>2 fh' sh' where "T = ((T\<^isub>1 \<rightarrow> T\<^isub>2  : fh' : sh') :: ty)" and "\<turnstile> T\<^isub>1 <: S\<^isub>1" and "\<turnstile> S\<^isub>2 <: T\<^isub>2" 
                 and "\<turnstile> fh <fh: fh'" and "\<turnstile> sh <sh: sh'" |
  (union) Ts T\<^isub>1 where "T = Union Ts" and "T\<^isub>1 : set Ts" and "\<turnstile> ?S <: T\<^isub>1"
  using a
proof (cases,simp_all add: ty.inject)
  fix Ta
  assume
    X:"\<And>T\<^isub>1 T\<^isub>2 fh' sh'. \<lbrakk>Ta = T\<^isub>1 \<rightarrow> T\<^isub>2 : fh' : sh'; \<turnstile> T\<^isub>1 <: S\<^isub>1; \<turnstile> S\<^isub>2 <: T\<^isub>2; \<turnstile> fh <fh: fh'; \<turnstile> sh <sh: sh'\<rbrakk> \<Longrightarrow> thesis"
    and "S\<^isub>1 \<rightarrow> S\<^isub>2 : fh : sh = Ta" and  "T = Ta"
  thus ?thesis using X[of S\<^isub>1 S\<^isub>2 fh sh] by (auto simp add: ty.inject)
next
  fix S1 T1 T2 S2 fha fh' sha sh'
  assume 
    X:"\<And>T\<^isub>1 T\<^isub>2 fh'a sh'a.
    \<lbrakk>S1 = T\<^isub>1 \<and> S2 = T\<^isub>2 \<and> fh' = fh'a \<and> sh' = sh'a; \<turnstile> T\<^isub>1 <: T1; \<turnstile> T2 <: T\<^isub>2; \<turnstile> fha <fh: fh'a; \<turnstile> sha <sh: sh'a\<rbrakk>
    \<Longrightarrow> thesis" and 
    "\<turnstile> S1 <: T1" and "\<turnstile> T2 <: S2" and " \<turnstile> fha <fh: fh'" and " \<turnstile> sha <sh: sh'"
  thus ?thesis by auto
qed

lemma S_Trans[intro]:
  assumes "\<turnstile>S<:Q" and " \<turnstile>Q<:T"
  shows "\<turnstile>S<:T" 
  using prems
proof (induct "X"=="(S,Q,T)"  arbitrary: S Q T taking: "size_ty3" rule: measure_induct_rule)
  case (less X S Q T)
  show " \<turnstile> S <: T" using `\<turnstile> S <: Q` less 
  proof (induct  S Q\<equiv>Q rule: subtype.induct) 
    case S_Refl thus ?case by auto
  next
    case (S_Top A)
    have X_inst:"X = (A,Q,T)" by fact
    show ?case using S_Top  
    proof -
      {
	assume "EX Ts T'. T = Union Ts \<and> T' : set Ts \<and> \<turnstile> Q <: T'"
	then obtain Ts T' where "T = Union Ts "" T' : set Ts "" \<turnstile> Q <: T'" by auto
	hence "size T' < size T" using union_size_ty by auto
	hence "size_ty3 (A,Q,T') < size_ty3 (A,Q,T)" by auto
	hence "\<turnstile> A <: T'" using `\<turnstile> A <: Q` `\<turnstile> Q <: T'` using less(1)[of "(A,Q,T')" A Q T'] X_inst by auto
	hence ?thesis using S_Top prems by auto
      }
      thus ?thesis using S_TopE S_Top by blast
    qed
  next
    case (S_Fun Q1 S1 S2 Q2 F F' S S') 
    hence rh_drv: " \<turnstile> Q1 \<rightarrow> Q2 : F' : S' <: T" by simp
    let ?S = "S1 \<rightarrow> S2 : F : S"
    have X_inst:"X = (S1 \<rightarrow> S2 : F : S, Q1 \<rightarrow> Q2 : F' : S', T)" using S_Fun by auto
    note `Q1 \<rightarrow> Q2 : F' : S' = Q`  
    hence Q12_less: "size Q1 < size Q" "size Q2 < size Q"  by auto
    have lh_drv_prm1: " \<turnstile> Q1 <: S1" by fact
    have lh_drv_prm2: " \<turnstile> S2 <: Q2" by fact
    show " \<turnstile> S1 \<rightarrow> S2 : F : S <: T"
    proof (induct rule: S_ArrowE_left[OF rh_drv])
      case 1 thus ?case by simp
    next
      case (2 T1 T2 fh' sh')
      have T_inst: "T = T1 \<rightarrow> T2 : fh' : sh'"
	and  rh_drv_prm1: " \<turnstile> T1 <: Q1"
	and  rh_drv_prm2: " \<turnstile> Q2 <: T2"
        and  C:"\<turnstile> F' <fh: fh'" and D:"\<turnstile> S' <sh: sh'" by fact+
      from X_inst T_inst have X_inst':"X = (S1 \<rightarrow> S2 : F : S, Q1 \<rightarrow> Q2 : F' : S', T1 \<rightarrow> T2 : fh' : sh')" by simp
      from X_inst' lh_drv_prm1  rh_drv_prm1 have  A:" \<turnstile> T1 <: S1" using S_Fun.prems(1)[of _ T1 Q1 S1] by auto
      from X_inst' lh_drv_prm2  rh_drv_prm2 have B:" \<turnstile> S2 <: T2" using S_Fun.prems(1)[of _ S2 Q2 T2] by auto
      have " \<turnstile> S1 \<rightarrow> S2 : F : S <: T1 \<rightarrow> T2 : fh' : sh'" using A B C D `\<turnstile> F <fh: F'``\<turnstile> S <sh: S'` by auto
      thus " \<turnstile> S1 \<rightarrow> S2 : F : S <: T" using T_inst by auto
    next
      case (3 Ts T1)
      have T_inst: "T = Union Ts"
	and  elem: "T1 : set Ts"
	and  sub:"\<turnstile> Q1 \<rightarrow> Q2 : F' : S' <: T1" by fact+
      have sub':"\<turnstile> S1 \<rightarrow> S2 : F : S <:  Q1 \<rightarrow> Q2 : F' : S'" using S_Fun by simp
      have sz:"size T1 < size T" using T_inst elem union_size_ty by auto
      from X_inst T_inst have X_inst':"X = (S1 \<rightarrow> S2 : F : S, Q1 \<rightarrow> Q2 : F' : S', Union Ts)" by simp
      from sub sub' X_inst' 
      have " \<turnstile> S1 \<rightarrow> S2 : F : S <: T1"  using S_Fun.prems(1)[OF _ sub' sub] sz T_inst by auto
      thus " \<turnstile> S1 \<rightarrow> S2 : F : S <: T" using T_inst elem by auto     
    qed
  next
    case (S_UnionSuper T1 Ts S)
    have sub1:"\<turnstile> S <: T1" by fact
    hence sub2:"\<turnstile> T1 <: T" using S_UnionSuper union_sub_elim[of Ts T T1] by auto
    have sz:"size T1 < size Q" using S_UnionSuper union_size_ty by auto
    hence "\<turnstile> S <: T" using S_UnionSuper(4)[OF _ sub1 sub2] sz S_UnionSuper(7) by auto
    thus ?case .
  next
    case (S_UnionSub Ts S)
    have "!! T0. T0 : set Ts \<Longrightarrow> \<turnstile> T0 <: T"
    proof -
      fix T0
      assume "T0 : set Ts"
      hence sz:"size T0 < size (Union Ts)" using union_size_ty by auto
      have s1:"\<turnstile> T0 <: S" using S_UnionSub `T0 : set Ts` by auto
      have s2:"\<turnstile> S <: T" using S_UnionSub by auto
      note S_UnionSub(6)
      thus "\<turnstile> T0 <: T" using S_UnionSub(3)[OF _ s1 s2] sz `S = Q` by auto
    qed
    thus ?case ..
  next
    case (S_Pair S1 Q1 S2 Q2)
    hence rh_drv: " \<turnstile> <Q1, Q2> <: T" by simp
    have X_inst:"X = (<S1,S2>, <Q1, Q2>, T)" (is "X = (?S,?Q,T)") using S_Pair by auto
    note `?Q = Q`  
    hence Q12_less: "size Q1 < size Q" "size Q2 < size Q"  by auto
    have lh_drv_prm1: " \<turnstile> S1 <: Q1" by fact
    have lh_drv_prm2: " \<turnstile> S2 <: Q2" by fact
    show ?case
    proof (induct rule: S_UnionE_left[OF rh_drv])
      case 1 thus ?case by simp
    next
      case (2 T1 T2)
      note S_Pair.prems(1)[OF _ `\<turnstile> S1 <: Q1` `\<turnstile> Q1 <: T1`] S_Pair.prems(1)[OF _ `\<turnstile> S2 <: Q2` `\<turnstile> Q2 <: T2`]
      hence "\<turnstile> S1 <: T1" "\<turnstile> S2 <: T2" using X_inst 2 by auto
      thus ?case using `T = <T1,T2>` by auto
    next
      case (3 Ts T1)      
      have sub':"\<turnstile> <S1,S2> <:  <Q1, Q2>" using S_Pair by simp
      have sz:"size T1 < size T" using 3 union_size_ty by auto
      from X_inst 3 have X_inst':"X = (?S, ?Q, Union Ts)" by simp
      from 3 sub'
      have " \<turnstile> ?S <: T1"  using S_Pair.prems(1)[of _ "?S" "?Q" T1] sz 3 S_Pair by simp
      thus " \<turnstile> ?S <: T" using 3 by auto     
    qed
  qed
qed


section {* type environments *}

types varEnv = "(name*ty) list"

text {* valid contexts *}
inductive
  valid :: "varEnv \<Rightarrow> bool"
where
    v1[intro]: "valid []"
  | v2[intro]: "\<lbrakk>valid \<Gamma>;a\<sharp>\<Gamma>\<rbrakk>\<Longrightarrow> valid ((a,\<sigma>)#\<Gamma>)"

equivariance valid

nominal_inductive valid done

lemma fresh_context[rule_format]: 
  fixes  \<Gamma> :: "(name\<times>ty)list"
  and    a :: "name"
  assumes a: "a\<sharp>\<Gamma>"
  shows "\<not>(\<exists>\<tau>::ty. (a,\<tau>)\<in>set \<Gamma>)"
using a
by (induct \<Gamma>)
   (auto simp add: fresh_prod fresh_list_cons fresh_atm)

lemma valid_elim: 
  fixes  \<Gamma> :: "(name\<times>ty)list"
  and    pi:: "name prm"
  and    a :: "name"
  and    \<tau> :: "ty"
  shows "valid ((a,\<tau>)#\<Gamma>) \<Longrightarrow> valid \<Gamma> \<and> a\<sharp>\<Gamma>"
  by (ind_cases "valid ((a,\<tau>)#\<Gamma>)") simp

lemma valid_unicity[rule_format]: 
  assumes a: "valid \<Gamma>"
  and     b: "(c,\<sigma>)\<in>set \<Gamma>"
  and     c: "(c,\<tau>)\<in>set \<Gamma>"
  shows "\<sigma>=\<tau>" 
  using a b c
  by (induct \<Gamma>) (auto dest!: valid_elim fresh_context)

declare fresh_list_cons[simp]
declare fresh_list_nil[simp]

subsection {* no-overlap metafunction *}

subsubsection {* definition *}

fun
  no_overlap :: "ty \<Rightarrow> ty \<Rightarrow> bool"
where
"no_overlap t s = False"

lemma no_overlap_eqvt[eqvt]:
  "pi \<bullet> (no_overlap t s) = no_overlap (pi \<bullet> t) (pi \<bullet> s)"
  by (auto)

subsubsection {* Soundness theorem *}

lemma no_overlap_soundness1:
  assumes "no_overlap T U"
  and "\<turnstile> t <: T"
  shows "~ \<turnstile> t <: U"
  using prems by simp
  

constdefs
  unionp :: "ty \<Rightarrow> bool"
[simp]:"unionp T == EX ls. T = Union ls"

lemma unionp_eqvt[eqvt]:
  "pi \<bullet> (unionp s) = unionp (pi \<bullet> s)"
  by (cases s) auto


function
  restrict :: "ty \<Rightarrow> ty \<Rightarrow> ty"
where
  restrict_no_overlap: "no_overlap t s \<Longrightarrow> restrict t s = Union []"
| restrict_subtype':"~no_overlap t s \<Longrightarrow> \<turnstile> t <: s \<Longrightarrow> restrict t s = t"
| restrict_union': "~no_overlap t (Union ls) \<Longrightarrow> unionp (Union ls) \<Longrightarrow> ~(\<turnstile> t <: (Union ls)) \<Longrightarrow> restrict t (Union ls) = Union (map (restrict t) ls)"
| restrict_other:"~no_overlap t s \<Longrightarrow>~(\<turnstile> t <: s) \<Longrightarrow> ~unionp s \<Longrightarrow> restrict t s = s"

proof (atomize_elim, simp_all)
  fix x:: "ty * ty"
  obtain t s where X:"x = (t,s)" by (cases x)
  {
    assume "\<turnstile> t <: s"
    hence "\<exists>t s. \<turnstile> t <: s \<and> x = (t, s)" using X by simp
  }
  moreover
  {
    assume "~ \<turnstile> t <: s" and "unionp s"
    then obtain ls where "s = Union ls" by (cases s) auto
    hence "(\<exists>t ls. \<not> \<turnstile> t <: ty.Union ls \<and> x = (t, ty.Union ls))" using prems X by auto
  }
  moreover
  {
    assume "~ \<turnstile> t <: s" and "~ unionp s"
    hence "\<exists>t s. \<not> \<turnstile> t <: s \<and> (\<forall>ls. s \<noteq> ty.Union ls) \<and> x = (t, s)" using X by auto
  }
  ultimately show "(\<exists>t s. \<turnstile> t <: s \<and> x = (t, s)) \<or>
        (\<exists>t ls. \<not> \<turnstile> t <: ty.Union ls \<and> x = (t, ty.Union ls)) \<or> (\<exists>t s. \<not> \<turnstile> t <: s \<and> (\<forall>ls. s \<noteq> ty.Union ls) \<and> x = (t, s))"
    by auto
next
  fix t ls ta s
  show "\<lbrakk>\<not> \<turnstile> ta <: s; \<not> unionp s; t = ta \<and> ty.Union ls = s\<rbrakk> \<Longrightarrow> ty.Union (map (\<lambda>x1. restrict_sumC (ta, x1)) ls) = s"
    by (cases s) auto
qed (auto)

termination by lexicographic_order

lemma restrict_eqvt[eqvt]:
  fixes pi::"name prm"
  shows "pi\<bullet>(restrict T1 T2) = restrict (pi\<bullet>T1) (pi\<bullet>T2)"
by (induct T2) (auto)

lemma restrict_subtype:
  assumes "\<turnstile> t <: s"
  shows "restrict t s = t"
  using prems restrict_subtype' no_overlap_soundness1 by auto

lemma restrict_union:
  assumes "\<not> no_overlap t (ty.Union ls)" and  "\<not> \<turnstile> t <: ty.Union ls"
  shows "restrict t (ty.Union ls) = ty.Union (map (restrict t) ls)"
  using prems restrict_union' by auto


lemma ty_cases[consumes 0, case_names Top N TT FF Arr Union Pair]:
  fixes P :: "ty \<Rightarrow> bool"
  and T :: ty
  assumes a1:"P Top"
  and a2:"P N"
  and a3:"P TT"
  and a3':"P FF"
  and a4:"!! t1 t2 f s. P (t1 \<rightarrow> t2 : f : s)"
  and a5:"!! Ts . P (Union Ts)"
  and a6:"!! T1 T2 . P <T1,T2>"
  shows "P T"
  using  prems
  by (cases T) auto

inductive_cases top_below: "\<turnstile> Top <: T"
inductive_cases top_below_pair: "\<turnstile> Top <: <T,S>"
inductive_cases top_below_fn: "\<turnstile> Top <: T \<rightarrow> S : F : sh"

lemma restrict_soundness:
  assumes A:"\<turnstile> T0 <: T"
  and B:"\<turnstile> T0 <: S"
  and nu:"~ unionp T0"
  shows "\<turnstile> T0 <: restrict S T"
  using prems
proof (induct T arbitrary: S T0 taking: size rule: measure_induct_rule)
  case (less T S T0)
  have C:"~no_overlap S T" using A B no_overlap_soundness1 by auto
  from less C show ?case
  proof (induct T==T rule: ty_cases)
    case Arr thus ?case by (cases "\<turnstile> S <: T", auto)
  next
    case Top thus ?case by (cases "\<turnstile> S <: T", auto)
  next
    case N thus ?case by (cases "\<turnstile> S <: T", auto)
  next
    case TT thus ?case by (cases "\<turnstile> S <: T", auto)
  next
    case FF thus ?case by (cases "\<turnstile> S <: T", auto)
  next
    case Pair thus ?case by (cases "\<turnstile> S <: T", auto)
  next
    case (Union Ts) thus ?case
    proof (cases "\<turnstile> S <: T")
      case False
      hence r:"restrict S T = Union (map (restrict S) Ts)" 
	using prems restrict_union[of S Ts] C by auto
      have T:"\<turnstile> T0 <: Union Ts" using prems by simp
      have "?this \<Longrightarrow> ?thesis"
      proof (ind_cases "\<turnstile> T0 <: Union Ts")
	assume 0:"Union Ts = T0" thus ?thesis using `~ unionp T0` by auto
      next
	fix Ts'
	assume "T0 = ty.Union Ts'" thus ?thesis using `~ unionp T0` by auto
      next
	fix T'
	assume "T' : set Ts" "\<turnstile> T0 <: T'"
	have 1:"\<turnstile> T0 <: restrict S T'" using union_size_ty prems by auto
	have 2:"set (map (restrict S) Ts) =  (restrict S) ` set Ts" by auto
	have 3:"T' : set Ts" using prems by auto
	have 4:"restrict S T' : set (map (restrict S) Ts)" using 2 3 by auto
	hence "\<turnstile> T0 <: Union (map (restrict S) Ts)" using subtype.S_UnionSuper[OF 4 1] by auto
	thus ?thesis using r by auto
      qed
      thus ?thesis using T by simp
    qed (auto)
  qed
qed

function
  remove :: "ty \<Rightarrow> ty \<Rightarrow> ty"
where
  remove_subtype:"\<turnstile> t <: s \<Longrightarrow>                         remove t s          = Union []"
| remove_union:"~(\<turnstile> (Union ls) <: s) \<Longrightarrow>               remove (Union ls) s = Union (map (% t. remove t s) ls)"
| remove_other:"~(\<turnstile> t <: s) \<Longrightarrow>          ~unionp t \<Longrightarrow> remove t s          = t"
by (atomize_elim, auto)

termination by lexicographic_order

lemma remove_soundness:
  assumes A:"\<turnstile> T0 <: T" and B:"~ (\<turnstile> T0 <: S)" and C:"~ unionp T0"
  shows "\<turnstile> T0 <: remove T S"
  using prems
proof (induct T arbitrary: S T0 taking:"size" rule: measure_induct_rule)
  case (less T S T0)
  thus ?case
  proof (induct T==T rule: ty_cases)
   case (Union Ts) thus ?case
    proof (cases "\<turnstile> T <: S")
      case True thus ?thesis using remove_subtype[of T S] prems by auto
    next
      case False
      hence req:"remove T S =  Union (map (% t. remove t S) Ts)" using Union by auto
      have T:"\<turnstile> T0 <: Union Ts" using prems by simp
      have "?this \<Longrightarrow> ?thesis"
      proof (ind_cases "\<turnstile> T0 <: Union Ts")
	assume 0:"Union Ts = T0" thus ?thesis using `~ unionp T0` by auto
      next
	fix Ts'
	assume "T0 = ty.Union Ts'"
	thus ?thesis using `~ unionp T0` by auto
      next
	fix T'
	assume "T' : set Ts" "\<turnstile> T0 <: T'"
	have 1:"\<turnstile> T0 <: remove T' S" using union_size_ty[of T' Ts] prems(4)[of T'] prems by simp 
	have 2:"set (map (% t. remove t S) Ts) =  (% t. remove t S) ` set Ts" by auto
	have 3:"T' : set Ts" using prems by auto
	have 4:"remove T' S : set (map (% t. remove t S) Ts)" using 2 3 by auto
	hence "\<turnstile> T0 <: Union (map (% t. remove t S) Ts)" using subtype.S_UnionSuper[OF 4 1] by auto
	thus ?thesis using req by auto
      qed
      thus ?thesis using T by simp
    qed      
 next
   case Top thus ?case using S_Trans[of T0 T S]
     by (cases "\<turnstile> T <: S") auto
  next
    case N thus ?case by (cases "\<turnstile> T <: S", auto)
  next
    case TT thus ?case by (cases "\<turnstile> T <: S", auto)
  next
    case FF thus ?case by (cases "\<turnstile> T <: S", auto)
  next
    case Arr thus ?case by (cases "\<turnstile> T <: S", auto)
  next
    case Pair thus ?case by (cases "\<turnstile> T <: S", auto)
  qed
qed

fun lookup :: "varEnv \<Rightarrow> name => ty option"
where 
"lookup [] x = None"
| "lookup ((y,t)#G) x = (if x = y then Some t else lookup G x)"

fun update :: "ty \<Rightarrow> (bool * ty * pe list) \<Rightarrow> ty"
where
 "update T (True,  U, []) = restrict T U"
| "update T (False, U, []) = remove T U"
| "update <T,S> (b, U, Car # pi) = <(update T (b, U, pi)), S>"
| "update <T,S> (b, U, Cdr # pi) = <T, (update S (b, U, pi))>"
| "update T _ = undefined"

fun do_update :: "varEnv \<Rightarrow> name \<Rightarrow> (bool * ty * pe list) \<Rightarrow> varEnv"
where
"do_update G x f = (case (lookup G x) of None \<Rightarrow> G | (Some T) \<Rightarrow> AssocList.update x (update T f) G)"

function env_plus :: "varEnv \<Rightarrow> p list \<Rightarrow> varEnv"
where
  "env_plus G ((TE t pi x)  # Fs) = (env_plus (do_update G x (True,  t, pi)) Fs)"
| "env_plus G ((NTE t pi x) # Fs) = (env_plus (do_update G x (False, t, pi)) Fs)"
| "env_plus G (Bot # Fs) = map (% (x,t). (x,Union [])) G"
| "env_plus G [] = G"
proof (atomize_elim, auto simp add: p.inject)
  fix b
  assume "\<forall>t pi x Fs. b \<noteq> TE t pi x # Fs"" \<forall>t pi x Fs. b \<noteq> NTE t pi x # Fs"" b \<noteq> []"
  thus "\<exists>Fs. b = Bot # Fs"
  proof (induct b)
    case (Cons F Fs) thus ?case  by (induct F rule: p.induct) (auto)
  qed (auto)
qed

termination by lexicographic_order

datatype f = F "p list" "p list"

primrec (unchecked perm_f)
"pi \<bullet> (F ps1 ps2) = F (pi \<bullet> ps1) (pi \<bullet> ps2)"

declare perm_f.simps[eqvt]

fun combfilter :: "f \<Rightarrow> f \<Rightarrow> f \<Rightarrow> f"
where
"combfilter _ _ _ = F [] []"

function apo :: "ph \<Rightarrow> ty \<Rightarrow> s \<Rightarrow> (p option)"
where
"apo BotH S s = Some Bot"

| "~no_overlap S T \<Longrightarrow> apo (TEH  T pi) S None = None"
| "~\<turnstile> S <: T       \<Longrightarrow> apo (NTEH T pi) S None = None"

| "no_overlap S T \<Longrightarrow> apo (TEH  T (pe#pi')) S None = None"
| "\<turnstile> S <: T       \<Longrightarrow> apo (NTEH T (pe#pi')) S None = None"


| "no_overlap S T  \<Longrightarrow> apo (TEH T [])       S s              = Some Bot"
| "no_overlap S T  \<Longrightarrow> apo (TEH T (pe#pi')) S (Some (pi, x)) = Some (TE T ((pe#pi')@pi) x)"    
| "~no_overlap S T \<Longrightarrow> apo (TEH T pi')      S (Some (pi, x)) = Some (TE T (pi'@pi) x)"    

| "\<turnstile> S <: T  \<Longrightarrow> apo (NTEH T [])       S s              = Some Bot"
| "\<turnstile> S <: T  \<Longrightarrow> apo (NTEH T (pe#pi')) S (Some (pi, x)) = Some (NTE T ((pe#pi')@pi) x)"    
| "~\<turnstile> S <: T \<Longrightarrow> apo (NTEH T pi')      S (Some (pi, x)) = Some (NTE T (pi'@pi)      x)"
proof (atomize_elim, simp_all)
  fix x :: "ph \<times> ty \<times> (pe list \<times> name) option"
  show "(\<exists>S s. x = (BotH, S, s)) \<or>
        (\<exists>S T pi. x = (TEH T pi, S, None)) \<or>
        (\<exists>S T. \<not> \<turnstile> S <: T \<and> (\<exists>pi. x = (NTEH T pi, S, None))) \<or>
        (\<exists>S T. \<turnstile> S <: T \<and> (\<exists>pe pi'. x = (NTEH T (pe # pi'), S, None))) \<or>
        (\<exists>S T pi' pi xa. x = (TEH T pi', S, Some (pi, xa))) \<or>
        (\<exists>S T. \<turnstile> S <: T \<and> (\<exists>s. x = (NTEH T [], S, s))) \<or>
        (\<exists>S T. \<turnstile> S <: T \<and> (\<exists>pe pi' pi xa. x = (NTEH T (pe # pi'), S, Some (pi, xa)))) \<or>
        (\<exists>S T. \<not> \<turnstile> S <: T \<and> (\<exists>pi' pi xa. x = (NTEH T pi', S, Some (pi, xa))))"
  proof (cases x)
    fix a b c
    assume A: "x = (a, b, c)"
    thus ?thesis
    proof (cases a)
      case BotH thus ?thesis using A by auto
    next
      case (TEH T pi) thus ?thesis using A TEH by (cases c) auto
    next
      case (NTEH T pi) thus ?thesis using A NTEH by (cases c) (cases "\<turnstile> b <: T ", cases pi, auto)+
    qed
  qed
qed

termination by lexicographic_order

fun applyfilter :: "fh \<Rightarrow> ty \<Rightarrow> s \<Rightarrow> f"
where
"applyfilter (FH ph_plus ph_minus) t s = 
  F (filtermap (% ph. apo ph t s) ph_plus) (filtermap (% ph. apo ph t s) ph_minus)"

function abo :: "name \<Rightarrow> p \<Rightarrow> ph option"
where
  abo_bot:"abo x Bot = Some BotH"
| abo_te: "abo x (TE  T pi y) = (if x = y then Some (TEH  T pi) else None)"
| abo_nte:"abo x (NTE T pi y) = (if x = y then Some (NTEH T pi) else None)"
proof (atomize_elim, auto simp add: p.inject)
  fix b
  assume "b \<noteq> Bot"and" \<forall>T pi y. b \<noteq> NTE T pi y"
  thus "\<exists>T pi y. b = TE T pi y"
  by (induct b rule: p.induct) (auto simp add: p.inject)
qed
  
termination by lexicographic_order


fun abstractfilter :: "name \<Rightarrow> f \<Rightarrow> fh"
where
"abstractfilter x (F p1 p2) = FH (filtermap (abo x) p1) (filtermap (abo x) p2)"

lemma apo_abo_id:
  fixes ph :: ph and p :: p 
  assumes A:"abo x p = Some ph"
  shows "apo ph Top (Some ([], x)) = Some p \<or> (EX t. ph = NTEH t [] \<and> \<turnstile> Top <: t \<and> apo ph Top (Some ([], x)) = Some Bot)"
  using A
proof (cases ph)
  case BotH
  hence "p = Bot" using A
  proof (induct p rule: p.induct)
    case (TE _ _ n) thus ?case by (cases "x = n") auto
  next
    case (NTE _ _ n) thus ?case by (cases "x = n") auto
  qed (auto)
  thus ?thesis using A by auto
next
  case (TEH t l)
  hence "p = TE t l x" using A
  proof (induct p rule: p.induct)
    case (TE _ _ n) thus ?case by (cases "x = n") auto
  next
    case (NTE _ _ n) thus ?case by (cases "x = n") auto
  qed (auto)
  thus ?thesis using A by auto
next
  case (NTEH t l)
  hence "p = NTE t l x" using A
  proof (induct p rule: p.induct) 
    case (TE _ _ n) thus ?case by (cases "x = n") auto
  next
    case (NTE _ _ n) thus ?case by (cases "x = n") auto
  qed (auto)
  thus ?thesis using A
  proof (cases "\<turnstile> Top <: t")
    case True thus ?thesis using NTEH A `p = NTE t l x`
    by (cases l) (auto)
  qed (auto)
qed


-- "NOT TRUE"
lemma "applyfilter (abstractfilter x f) Top (Some ([], x)) = f"
oops

lemma restrict_remove_soundness:
  assumes A:"\<turnstile> T0 <: T" and B:"~ unionp T0"
  shows
  "(\<turnstile> T0 <: S \<and> \<turnstile> T0 <: restrict S T) \<or> (~ (\<turnstile> T0 <: S) \<and> \<turnstile> T0 <: remove T S)"
using restrict_soundness[OF A _ B] remove_soundness[OF A _ B]
by auto

lemma al_update_fresh:
  fixes v::name and n::name
  assumes a:"v \<sharp> \<Gamma>"  and c:"valid \<Gamma>" and d:"lookup \<Gamma> n = Some t'"
  shows "v \<sharp> (AssocList.update n t \<Gamma>)"
  using a d c 
proof (induct \<Gamma>)
  case (Cons a G) thus ?case using valid_elim[of _ _ G] by (cases a) auto
qed (simp)

lemma do_update_fresh:
  fixes v::name
  assumes a:"v \<sharp> \<Gamma>"  and c:"valid \<Gamma>" 
  shows "v \<sharp> (do_update \<Gamma> n fh)"
  using a c al_update_fresh[OF a c]
proof (cases "EX x. lookup \<Gamma> n = Some x")
  case True
  then obtain t' where b:"lookup \<Gamma> n = Some t'" by auto
  thus ?thesis using al_update_fresh[OF a c b] by auto
next
  case False thus ?thesis using a by auto
qed

lemma al_update_valid:
  assumes a:"valid \<Gamma>" and d:"lookup \<Gamma> n = Some t'"
  shows "valid (AssocList.update n t \<Gamma>)"
  using  a d al_update_fresh
by (induct \<Gamma> rule: valid.induct) auto  

lemma do_update_valid:
  assumes "valid \<Gamma>"
  shows "valid (do_update \<Gamma> n fh)"
  using assms
proof (induct)
  case (v2 G a S)
  hence "valid ((a,S)#G)" (is "valid ?G'") by auto
  thus ?case using v2
  proof (cases "EX x. lookup ?G' n = Some x")
    case True 
    then obtain t' where "lookup ?G' n = Some t'" by auto
    thus ?thesis using v2 al_update_valid[OF `valid ?G'` `lookup ?G' n = Some t'`]
      by (cases "a = n") auto
  qed (auto)
qed (auto)

lemma map_fresh:
  assumes "v \<sharp> \<Gamma>" "v \<sharp> x"
  shows "v \<sharp> map (% (a,b). (a,x)) \<Gamma>"
  using prems by (induct \<Gamma>) auto

lemma map_valid:
  fixes x :: ty
  assumes a:"valid \<Gamma>" 
  shows "valid (map (% (a,b). (a,x)) \<Gamma>)"
  using prems
proof (induct \<Gamma> arbitrary: v rule: valid.induct)
  case (v2 G a S)
  thus ?case using fresh_data map_fresh[of a G x] by auto
qed (auto)
  
lemma env_plus_fresh:
  fixes v::name
  assumes a:"v \<sharp> \<Gamma>"  and c:"valid \<Gamma>" 
  shows "v \<sharp> (env_plus \<Gamma> ps)"
  using a c 
proof (induct ps arbitrary: \<Gamma>)
  case (Cons a ps) thus ?case 
    using map_fresh[OF `v \<sharp> \<Gamma>`, of "Union []"] do_update_valid do_update_fresh
    by (induct a rule: p.induct) (auto)
qed (auto)

lemma env_plus_nil[simp]:
  "env_plus [] ps = []"
proof (induct ps)
  case (Cons a ps') thus ?case
    by (induct a rule: p.induct) auto
qed (auto)

lemma env_plus_valid:
  assumes c:"valid G" 
  shows "valid (env_plus G ps)"
  using c map_valid do_update_valid
proof (induct ps arbitrary: G)
  case (Cons p ps') thus ?case by (induct p rule: p.induct) auto
qed auto


lemma do_update_forget:
  assumes "valid \<Gamma>" and "x \<sharp> \<Gamma>"
  shows "do_update \<Gamma> x t = \<Gamma>"
  using prems
proof -
  have "lookup \<Gamma> x = None" using prems
  proof (induct \<Gamma>)
    case (v2 G a S) thus ?case using fresh_list_cons fresh_atm[of x a] by auto
  qed auto
  thus ?thesis by auto
qed

lemma lookup_eqvt[eqvt]:
  fixes pi :: "name prm"
  shows "pi \<bullet> (lookup G x) = lookup (pi \<bullet> G) (pi \<bullet> x)"
  using at_bij[of pi] at_name_inst
  by (induct G) auto

lemma update_eqvt[eqvt]:
  fixes pi :: "name prm"
  shows "pi \<bullet> (update t f) = (update (pi \<bullet> t) (pi \<bullet> f))"
  by (cases f) auto

lemma al_update_eqvt[eqvt]:
  fixes pi :: "name prm" and k :: name
  shows "pi \<bullet> (AssocList.update k v L) = (AssocList.update (pi \<bullet> k) (pi \<bullet> v) (pi \<bullet> L))"
proof (induct L)
  case (Cons kv L') thus ?case
  proof (cases kv)
    case (Pair k' v')
    thus ?thesis using Cons 
    proof (cases "k' = k") 
      case False
      thus ?thesis using Cons Pair pt_name_inst at_name_inst pt_bij4[of pi k' k] by auto
    qed (auto)
  qed
qed auto  

lemma do_update_eqvt[eqvt]:
  fixes pi :: "name prm"
  shows "pi \<bullet> (update t f) = (update (pi \<bullet> t) (pi \<bullet> f))"
  by (cases f) auto

lemma map_eqvt[eqvt]:
  fixes pi :: "name prm"
  shows "pi \<bullet> (map (% (a,b). x) l) = (map (% (a,b). pi \<bullet> x) (pi \<bullet> l))"
  by (induct l) auto

(*
lemma env_plus_eqvt[eqvt]:
  fixes pi :: "name prm"
  assumes "valid G"
  shows "pi \<bullet> (env_plus G ps) = (env_plus (pi \<bullet> G) (pi \<bullet> ps))"
  proof (induct ps) 
    case Nil thus ?case by auto
  next
    case (Cons p ps)
    show ?case using `valid G` Cons
    proof (induct G rule: valid.induct)
      case v1 thus ?case by auto
    next
      case (v2 G a S) thus ?case
      apply (induct p rule: p.induct)
      apply (simp add: eqvt)
      apply (simp only: ty.perms map_eqvt)
  apply simp
  apply simp
  apply (cases G)
  apply auto


*)

abbreviation "tfil ==  F [] [Bot] "

inductive
  typing :: "varEnv \<Rightarrow> trm \<Rightarrow> ty \<Rightarrow> f \<Rightarrow> s \<Rightarrow> bool" (" _ \<turnstile> _ : _ ; _ ; _ " [60,60,60,60,60] 60) 
where
  T_True[intro]: "valid \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> Bool True : TT ; tfil ; None"
| T_False[intro]: "valid \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> Bool False : FF ; F [Bot] [] ; None"
| T_Const[intro]: "valid \<Gamma> \<Longrightarrow>  c \<noteq> CAR \<and> c \<noteq> CDR \<Longrightarrow> \<Gamma> \<turnstile> BI c : \<Delta>\<^isub>\<tau> c ; tfil ; None"
| T_Num[intro]: "valid \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> Num n : N ; tfil ; None"
| T_Var[intro]: "valid \<Gamma> \<Longrightarrow> lookup \<Gamma> v = Some T \<Longrightarrow> \<Gamma> \<turnstile> Var v : T ; F [NTE FF [] v] [TE FF [] v] ; Some ([],v)"
| T_Abs[intro]: "valid \<Gamma> \<Longrightarrow> (x,S)#\<Gamma> \<turnstile> e : T ; \<Phi> ; obj \<Longrightarrow> \<phi> = abstractfilter x \<Phi> \<Longrightarrow> 
  Obj = (case obj of None \<Rightarrow> None | Some (pi,x') \<Rightarrow> (if x = x' then Some pi else None)) \<Longrightarrow> 
  \<Gamma> \<turnstile> (Lam[x:S].e) : (S \<rightarrow> T : \<phi> : Obj) ; tfil ; None"
| T_App[intro]:
  "valid \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> e_op : t_op ; \<Phi>_op ; o_op \<Longrightarrow> \<Gamma> \<turnstile> e_a : t_a ; \<Phi>_a ; o_a \<Longrightarrow>
  \<turnstile> t_a <: t_f \<Longrightarrow> \<turnstile> t_op <: t_f \<rightarrow> t_r : \<phi>_f : O_f \<Longrightarrow>
  \<Phi>_r = applyfilter \<phi>_f t_a o_a \<Longrightarrow>
  o_r = (case O_f of None \<Rightarrow> None | Some pi' \<Rightarrow> (case o_a of None \<Rightarrow> None | Some (pi,x) \<Rightarrow> Some (pi' @ pi, x))) \<Longrightarrow>
  \<Gamma> \<turnstile> App e_op e_a : t_r ; \<Phi>_r ; o_r"
| T_If[intro]:
  "valid \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> e1 : t1 ; (F ps_p ps_m) ; o1 \<Longrightarrow>
  env_plus \<Gamma> ps_p \<turnstile> e2 : t2 ; f2 ; o2 \<Longrightarrow>
  env_plus \<Gamma> ps_m \<turnstile> e3 : t3 ; f3 ; o3 \<Longrightarrow> 
  \<turnstile> t2 <: t \<Longrightarrow> \<turnstile> t3 <: t \<Longrightarrow> f = combfilter (F ps_p ps_m) f2 f3 \<Longrightarrow>
  \<Gamma> \<turnstile> (Iff e1 e2 e3) : t ; f ; None"
| T_Cons[intro]:
  "valid \<Gamma> \<Longrightarrow>  \<Gamma> \<turnstile> e1 : t1 ; f1 ; o1 \<Longrightarrow>   \<Gamma> \<turnstile> e2 : t2 ; f2 ; o2 \<Longrightarrow>
   \<Gamma> \<turnstile> CONS e1 e2 : Pr t1 t2 ; tfil ; None"
| T_Car[intro]:
  "valid \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> e_a : t_a ; \<Phi>_a ; o_a \<Longrightarrow>
  \<turnstile> t_a <: Pr t1 t2 \<Longrightarrow>
  \<Phi>_r = applyfilter (FH [NTEH FF [Car]] [TEH FF [Car]]) t_a o_a \<Longrightarrow>
  o_r = (case o_a of None \<Rightarrow> None | Some (pi,x) \<Rightarrow> Some ([Car] @ pi, x)) \<Longrightarrow>
  \<Gamma> \<turnstile> App (BI CAR) e_a : t_1 ; \<Phi>_r ; o_r"

| T_Cdr[intro]:
  "valid \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> e_a : t_a ; \<Phi>_a ; o_a \<Longrightarrow>
  \<turnstile> t_a <: Pr t1 t2 \<Longrightarrow>
  \<Phi>_r = applyfilter (FH [NTEH FF [Cdr]] [TEH FF [Cdr]]) t_a o_a \<Longrightarrow>
  o_r = (case o_a of None \<Rightarrow> None | Some (pi,x) \<Rightarrow> Some ([Cdr] @ pi, x)) \<Longrightarrow>
  \<Gamma> \<turnstile> App (BI CDR) e_a : t_2 ; \<Phi>_r ; o_r"

| T_IfTrue[intro]:
  "valid \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> e1 : t1 ; (F ps_p [Bot]) ; o1 \<Longrightarrow>
  env_plus \<Gamma> ps_p \<turnstile> e2 : t2 ; f2 ; o2 \<Longrightarrow>
  \<turnstile> t2 <: t \<Longrightarrow> f = combfilter (F [] [Bot]) f2 (F [] []) \<Longrightarrow>
  \<Gamma> \<turnstile> (Iff e1 e2 e3) : t ; f ; None"
| T_IfFalse[intro]:
  "valid \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> e1 : t1 ; (F [Bot] ps_m) ; o1 \<Longrightarrow>
  env_plus \<Gamma> ps_m \<turnstile> e3 : t3 ; f3 ; o3 \<Longrightarrow> 
  \<turnstile> t3 <: t \<Longrightarrow> f = combfilter (F [Bot] []) (F [] []) f3 \<Longrightarrow>
  \<Gamma> \<turnstile> (Iff e1 e2 e3) : t ; f ; None"


inductive_cases lam_ty2: "G \<turnstile> Lam[x:T].e : T' ; fil ; obj"

lemma lam_ty: assumes a:"G \<turnstile> Lam[x:T].e : T' ; fil ; obj" shows b:"EX A B C D. T' = A \<rightarrow> B : C : D"
  using lam_ty2[OF a, of "\<exists>A B C D. T' = A \<rightarrow> B : C : D"] by auto

inductive_cases fun_sub_pair2: "\<turnstile> S \<rightarrow> T : A : b <: <T1,T2>"
inductive_cases sub_pair_cases: "\<turnstile> T <: <T1,T2>"

lemma fun_sub_pair: "\<turnstile> S \<rightarrow> T : A : b <: <T1,T2> \<Longrightarrow> False"
  using fun_sub_pair2 by auto

inductive_cases fun_sub_num: "\<turnstile> S \<rightarrow> T : A : b <: N"

lemma sub_pair:
  assumes a:"v : values" and b:"\<Gamma> \<turnstile> v : T ; f ; obj" and c:"\<turnstile> T <: <T1,T2>"
  shows "EX v1 v2. v = CONS v1 v2"
using b prems
proof (induct \<Gamma> v T f obj rule: typing.induct)
  case T_Abs thus ?case using fun_sub_pair2 by auto
next
  case (T_Var _ vv) thus ?case using values.cases[of "Var vv"] by auto
next
  case (T_App _ a _ _ _ b) thus ?case using values.cases[of "App a b"] by auto
next
  case (T_Car _ a _ _ _ b) thus ?case using values.cases[of "App (BI CAR) a"] by auto
next
  case (T_Cdr _ a _ _ _ b) thus ?case using values.cases[of "App (BI CDR) a"] by auto
next
  case T_If thus ?case using values.cases[OF T_If(11)] by auto
next
  case T_IfTrue thus ?case using values.cases[OF T_IfTrue(8)] by auto
next
  case T_IfFalse thus ?case using values.cases[OF T_IfFalse(8)] by auto
next
  case T_Cons thus ?case by auto
next
  case T_Num 
  have "\<turnstile> N <: <T1,T2> \<Longrightarrow> False" by (ind_cases "\<turnstile> N <: <T1,T2>")
  thus ?case using T_Num by auto
next
  case T_True 
  have "\<turnstile> TT <: <T1,T2> \<Longrightarrow> False" by (ind_cases "\<turnstile> TT <: <T1,T2>")
  thus ?case using T_True by auto
next
  case T_False
  have "\<turnstile> FF <: <T1,T2> \<Longrightarrow> False" by (ind_cases "\<turnstile> FF <: <T1,T2>")
  thus ?case using T_False by auto
next
  case (T_Const _ c)
  thus ?case using fun_sub_pair[of _ _ _ _ T1 T2] by (induct c) auto
qed


lemma sub_fun:
  fixes A B C D
  assumes a:"v : values" (is "?vv : values") and b:"\<Gamma> \<turnstile> v : T ; f ; obj" and c:"\<turnstile> T <: A \<rightarrow> B : C : D" (is "\<turnstile> _ <: ?TT")
  shows "(EX c. v = BI c) \<or> (EX x S e. v = Lam[x:S].e)"
using b prems
proof (induct \<Gamma> v T f obj rule: typing.induct)
  case T_Abs thus ?case by auto
next
  case (T_Var _ v) thus ?case using values.cases[of "Var v"] by auto
next
  case (T_App _ a _ _ _ b) thus ?case using values.cases[of "App a b"] by auto
next
  case (T_Car _ a _ _ _ b) thus ?case using values.cases[of "App (BI CAR) a"] by auto
next
  case (T_Cdr _ a _ _ _ b) thus ?case using values.cases[of "App (BI CDR) a"] by auto
next
  case T_If thus ?case using values.cases[OF T_If(11)] by auto
next
  case T_IfTrue thus ?case using values.cases[OF T_IfTrue(8)] by auto
next
  case T_IfFalse thus ?case using values.cases[OF T_IfFalse(8)] by auto
next
  case (T_Cons _ _ T1 _ _ _ T2) have "\<turnstile> <T1,T2> <: ?TT \<Longrightarrow> False" by (ind_cases "\<turnstile> <T1,T2> <: ?TT ") auto
  thus ?case using T_Cons by auto
next
  case T_Num 
  have "\<turnstile> N <: ?TT \<Longrightarrow> False" by (ind_cases "\<turnstile> N <: ?TT")
  thus ?case using T_Num by auto
next
  case T_True 
  have "\<turnstile> TT <: ?TT \<Longrightarrow> False" by (ind_cases "\<turnstile> TT <: ?TT")
  thus ?case using T_True by auto
next
  case T_False
  have "\<turnstile> FF <: ?TT \<Longrightarrow> False" by (ind_cases "\<turnstile> FF <: ?TT")
  thus ?case using T_False by auto
next
  case (T_Const _ c) thus ?case by auto
qed

inductive_cases add1_ty_cases: "G \<turnstile> BI ADD1 : t1 ; f1 ; o1"
inductive_cases zerop_ty_cases: "G \<turnstile> BI ZEROP : t1 ; f1 ; o1"
inductive_cases sub_n: "\<turnstile> T <: N"

lemma sub_num:
  fixes A v
  assumes a:"v : values" (is "?vv : values") and b:"\<Gamma> \<turnstile> v : T ; f ; obj" and c:"\<turnstile> T <: N" (is "\<turnstile> _ <: ?TT") 
  obtains c where "v = Num c"
using b prems
proof (induct \<Gamma> v T f obj rule: typing.induct)
  case (T_Var _ v) thus ?case using values.cases[of "Var v"] by auto
next
  case (T_App _ a _ _ _ b) thus ?case using values.cases[of "App a b"] by auto
next
  case (T_Car _ a _ _ _ b) thus ?case using values.cases[of "App (BI CAR) a"] by auto
next
  case (T_Cdr _ a _ _ _ b) thus ?case using values.cases[of "App (BI CDR) a"] by auto
next
  case T_If thus ?case using values.cases[OF T_If(12)] by auto
next
  case T_IfTrue thus ?case using values.cases[OF T_IfTrue(9)] by auto
next
  case T_IfFalse thus ?case using values.cases[OF T_IfFalse(9)] by auto
next
  case (T_Abs _ _ T1 _ T2 _ _ F1 Obj) have "(\<turnstile> (T1 \<rightarrow> T2 : F1 : Obj) <: N) \<Longrightarrow> False" 
    by (ind_cases "\<turnstile> (T1 \<rightarrow> T2 : F1 : Obj) <: N ") 
  thus ?case using T_Abs by auto
next
  case (T_Cons _ _ T1 _ _ _ T2) have "\<turnstile> <T1,T2> <: ?TT \<Longrightarrow> False" by (ind_cases "\<turnstile> <T1,T2> <: ?TT ") 
  thus ?case using T_Cons by auto
next
  case T_Num thus ?case by auto
next
  case T_True 
  have "\<turnstile> TT <: ?TT \<Longrightarrow> False" by (ind_cases "\<turnstile> TT <: ?TT")
  thus ?case using T_True by auto
next
  case T_False
  have "\<turnstile> FF <: ?TT \<Longrightarrow> False" by (ind_cases "\<turnstile> FF <: ?TT")
  thus ?case using T_False by auto
next
  case (T_Const _ c) 
  thus ?case using fun_sub_num by (induct c) auto
qed

lemma red_helper:
  fixes e e2
  assumes "e \<hookrightarrow> e'" (is "?trm \<hookrightarrow> e'")
  shows "e : values \<or> (EX E e' e''. e = E e' \<and> e' \<hookrightarrow> e'' \<and> E : ctxt)"
proof -
  have "?trm \<hookrightarrow> e'" by fact
  hence "?trm = (%x. x) ?trm \<and> ?trm \<hookrightarrow> e' \<and> (%x. x) \<in> ctxt"
    by auto
  hence "EX E. ?trm = E ?trm \<and> ?trm \<hookrightarrow> e' \<and> E \<in> ctxt" by auto
  thus ?thesis by auto
qed
  
lemma ctxt_helper:
  fixes E E' e1 e2 e
  assumes "e1 \<hookrightarrow> e2" (is "?trm \<hookrightarrow> e2")
  and "E (E' e1) = e" and "E : ctxt" and "E' : ctxt"
  shows "e : values \<or> (EX E0 e' e''. e = E0 e' \<and> e' \<hookrightarrow> e'' \<and> E0 : ctxt)"
proof -
  let ?E' = "(%t. E (E' t))"
  have B:"?E' : ctxt" using ctxt_compose prems by auto
  hence "EX E. e = E e1 \<and> e1 \<hookrightarrow> e2 \<and> E \<in> ctxt" using prems B by auto
  thus ?thesis by auto
qed
    
theorem progress:
  assumes a:"\<Gamma> \<turnstile> e : T ; \<Phi> ; obj" and b:"closed e"
  shows "e : values \<or> (EX E e' e''. e = E e' \<and> e' \<hookrightarrow> e'' \<and> E : ctxt)"
using a b
proof (induct _ e T \<Phi> obj)
  case T_Var thus ?case unfolding closed_def by (auto simp add: at_supp at_name_inst trm.supp)
next
  case T_Abs thus ?case by auto
next
  case T_Const thus ?case by auto
next
  case T_Num thus ?case by auto
next
  case T_True thus ?case by auto
next
  case T_False thus ?case by auto
next
  case (T_Car G e_a t_a f_a o_a t1 t2 o_r)
  {
    assume "e_a : values"    
    then obtain v1 v2 where "e_a = CONS v1 v2" using T_Car sub_pair by blast
    hence ?case using red_helper[of _ v1] `e_a : values` by auto
  }
  moreover
  {
    assume "~ (e_a : values)"    
    then obtain E e' e'' where A:"e_a = E e'" and B:"e' \<hookrightarrow> e''" and C:"E : ctxt" using T_Car
      unfolding closed_def fv_def trm.supp by blast
    hence ?case using ctxt_helper by auto
  }
  ultimately show ?case by auto
next
  case (T_Cdr G e_a t_a f_a o_a t1 t2 o_r)
  let ?trm = "App (BI CDR) e_a"
  {
    assume "e_a : values"    
    then obtain v1 v2 where "e_a = CONS v1 v2" using T_Cdr sub_pair by blast
    hence ?case using red_helper[of _ v2] `e_a : values` by auto
  }
  moreover
  {
    assume "~ (e_a : values)"    
    then obtain E e' e'' where "e_a = E e'" and A:"e' \<hookrightarrow> e''" and "E : ctxt" using T_Cdr
      unfolding closed_def fv_def trm.supp by blast
    hence ?case using ctxt_helper by auto
  }
  ultimately show ?case by auto
next
  case (T_If G e1 t1 f1p f1m o1 e2 t2 f2 o2 e3)  
  let ?trm = "Iff e1 e2 e3"
  {
    assume "~ (e1 : values)"    
    then obtain E e' e'' where "e1 = E e'" and A:"e' \<hookrightarrow> e''" and "E : ctxt" using T_If  
      unfolding closed_def fv_def trm.supp by blast
    hence ?case using ctxt_helper by auto
  }
  moreover
  {
    assume v:"e1 : values" and b:"e1 = Bool False"
    hence ?case using red_helper[of _ e3] by auto
  }
  moreover
  {
    assume v:"e1 : values" and b:"e1 \<noteq> Bool False"
    hence ?case using red_helper[of _ e2] by auto
  }
  ultimately show ?case by blast
next
  case (T_App G e1 t1 f1 o1 e2 t2 f2 o2 t_f t_r f_f O_f) 
  let ?trm = "App e1 e2"
  {
    assume "~ (e1 : values)"    
    then obtain E e' e'' where "e1 = E e'" and A:"e' \<hookrightarrow> e''" and "E : ctxt" using T_App
      unfolding closed_def fv_def trm.supp by blast
    hence ?case using ctxt_helper by auto
  }
  moreover
  {
    assume "e1 : values" and "~ e2 : values"
    then obtain E e' e'' where "e2 = E e'" and A:"e' \<hookrightarrow> e''" and "E : ctxt" using T_App
      unfolding closed_def fv_def trm.supp by blast
    hence ?case using ctxt_helper using `e1 : values` by auto
  }
  moreover
  {
    assume "e1 : values" and "e2 : values"
    {
      assume "\<exists>x S e. e1 = Lam [x:S].e"      
      then obtain x S body where e1def:"e1 = Lam[x:S].body" by auto
      have "closed e2" using T_App
	unfolding closed_def fv_def trm.supp by blast    
      hence "x \<sharp> e2" using closed_def fresh_def[of x e2] by auto
      hence ?case using red_helper[of ?trm "body[x::=e2]"] `e2 : values` e1def by auto
    }
    moreover 
    {
      assume "EX c. e1 = BI c"
      then obtain c where e1def:"e1 = BI c" by auto
      hence ?case using T_App
      proof (induct c)
	case CAR
	hence A:"G \<turnstile> BI CAR : t1 ; f1 ; o1" by simp
	have "G \<turnstile> BI CAR : t1 ; f1 ; o1 \<Longrightarrow> False"
	  by (ind_cases "G \<turnstile> BI CAR : t1 ; f1 ; o1") (simp add: trm.inject) 
	thus ?case using A by auto
      next
	case CDR
	hence A:"G \<turnstile> BI CDR : t1 ; f1 ; o1" by simp
	have "G \<turnstile> BI CDR : t1 ; f1 ; o1 \<Longrightarrow> False"
	  by (ind_cases "G \<turnstile> BI CDR : t1 ; f1 ; o1") (simp add: trm.inject) 
	thus ?case using A by auto
      next
	case NOT 
	{
	  assume "e2 = Bool False"
	  hence ?case using red_helper[of _ "Bool True"] using NOT by auto
	}
	moreover 
	{
	  assume "e2 \<noteq> Bool False" 
	  hence ?case using `e1 = BI NOT` `e2 : values` red_helper[of _ "Bool False"]
	    by (induct e2 rule: trm.induct) (auto simp add: trm.inject)
	}
	ultimately show ?case by auto
      next
	case CONSP
	{
	  assume "EX v1 v2. e2 = CONS v1 v2"
	  then obtain v1 v2 where "e2 = CONS v1 v2" by auto
	  hence ?case using red_helper[of _ "Bool True"] using CONSP `e2 : values` by auto
	}
	moreover 
	{
	  assume "~(EX v1 v2. e2 = CONS v1 v2)"
	  hence ?case using `e1 = BI CONSP` `e2 : values` red_helper[of _ "Bool False"]
	    by (induct e2 rule: trm.induct) (auto simp add: trm.inject)
	}
	ultimately show ?case by auto
      next
	case NUMBERP 
	{
	  assume "EX n. e2 = Num n"
	  then obtain n where "e2 = Num n" by auto
	  hence ?case using red_helper[of _ "Bool True"] using NUMBERP `e2 : values` by auto
	}
	moreover 
	{
	  assume "~(EX n. e2 = Num n)"
	  hence ?case using `e1 = BI NUMBERP` `e2 : values` red_helper[of _ "Bool False"]
	    by (induct e2 rule: trm.induct) (auto simp add: trm.inject)
	}
	ultimately show ?case by auto
      next
	case BOOLEANP
	{
	  assume "EX n. e2 = Bool n"
	  then obtain n where "e2 = Bool n" by auto
	  hence ?case using red_helper[of _ "Bool True"] using BOOLEANP `e2 : values` by auto
	}
	moreover 
	{
	  assume "~(EX n. e2 = Bool n)"
	  hence ?case using `e1 = BI BOOLEANP` `e2 : values` red_helper[of _ "Bool False"]
	    by (induct e2 rule: trm.induct) (auto simp add: trm.inject)
	}
	ultimately show ?case by auto

      next
	case PROCEDUREP
	{
	  assume "EX n. e2 = BI n"
	  then obtain n where "e2 = BI n" by auto
	  hence ?case using red_helper[of _ "Bool True"] using PROCEDUREP `e2 : values` by auto
	}
	moreover 
	{
	  assume "EX x S b. e2 = Lam[x:S].b"
	  then obtain x S b where "e2 = Lam[x:S].b" by auto
	  hence ?case using red_helper[of _ "Bool True"] using PROCEDUREP `e2 : values` by auto
	}
	moreover 
	{
	  assume "~(EX n. e2 = BI n)" and "~(EX x S b. e2 = Lam[x:S].b)"
	  hence ?case using `e1 = BI PROCEDUREP` `e2 : values` red_helper[of _ "Bool False"]
	    by (induct e2 rule: trm.induct) (auto simp add: trm.inject)
	}
	ultimately show ?case by auto

	-- "hard cases"
      next
	case ADD1
	have A:"G \<turnstile> BI ADD1 : t1 ; f1 ; o1" using ADD1 by simp
	note add1_ty_cases[OF A]
	hence B:"t1 = N \<rightarrow> N : FH [] [] : None" using trm.inject by auto	
	thm ADD1
	have "\<turnstile> N \<rightarrow> N : FH [] [] : None <: t_f \<rightarrow> t_r : f_f : O_f \<Longrightarrow> \<turnstile> t_f <: N"
	  by (ind_cases "\<turnstile> N \<rightarrow> N : FH [] [] : None <: t_f \<rightarrow> t_r : f_f : O_f")
	    auto
	hence "\<turnstile> t_f <: N" using ADD1(8) B by simp
	hence "\<turnstile> t2 <: N" using S_Trans ADD1 by blast
	then obtain n where "e2 = Num n" using sub_num[OF `e2 : values`] ADD1 by blast
	thus ?case using red_helper[of _ "Num (n + 1)"] using ADD1 by auto
      next
	case ZEROP 
	have A:"G \<turnstile> BI ZEROP : t1 ; f1 ; o1" using ZEROP by simp
	note zerop_ty_cases[OF A]
	hence B:"t1 = N \<rightarrow> B : FH [] [] : None" using trm.inject by auto	
	have "\<turnstile> N \<rightarrow> B : FH [] [] : None <: t_f \<rightarrow> t_r : f_f : O_f \<Longrightarrow> \<turnstile> t_f <: N"
	  by (ind_cases "\<turnstile> N \<rightarrow> B : FH [] [] : None <: t_f \<rightarrow> t_r : f_f : O_f")
	    auto
	hence "\<turnstile> t_f <: N" using ZEROP(8) B by simp
	hence "\<turnstile> t2 <: N" using S_Trans ZEROP by blast
	then obtain n where "e2 = Num n" using sub_num[OF `e2 : values`] ZEROP by blast
	thus ?case using red_helper[of _ "Bool (n = 0)"] using ZEROP by auto
      qed
    }
    ultimately have ?case using sub_fun[OF `e1 : values`  T_App(2) T_App(7)] by auto
  }
  ultimately show ?case by blast
next
  case (T_Cons G e1 t1 f1 o1 e2 t2 f2 o2) 
  let ?trm = "CONS e1 e2"
  {
    assume "~ (e1 : values)"    
    then obtain E e' e'' where "e1 = E e'" and A:"e' \<hookrightarrow> e''" and "E : ctxt" using T_Cons 
      unfolding closed_def fv_def trm.supp by blast
    hence ?case using ctxt_helper by auto
  }
  moreover
  {
    assume "e1 : values" and "~ e2 : values"
    then obtain E e' e'' where "e2 = E e'" and A:"e' \<hookrightarrow> e''" and "E : ctxt" using T_Cons
      unfolding closed_def fv_def trm.supp by blast
    hence ?case using ctxt_helper `e1 : values` by auto
  }
  moreover
  {
    assume "e1 : values" and "e2 : values"
    hence "?trm : values" by auto
    hence ?case by auto
  }
  ultimately show ?case by blast
next
  case (T_IfTrue G e1 t1 f1p f1m e2 _  t2 f2 o2 _ e3)  
  let ?trm = "Iff e1 e2 e3"
  {
    assume "~ (e1 : values)"    
    then obtain E e' e'' where "e1 = E e'" and A:"e' \<hookrightarrow> e''" and "E : ctxt" using T_IfTrue
      unfolding closed_def fv_def trm.supp by blast
    hence ?case using ctxt_helper by auto
  }
  moreover
  {
    assume v:"e1 : values" and b:"e1 = Bool False"
    hence ?case using red_helper[of _ e3] by auto
  }
  moreover
  {
    assume v:"e1 : values" and b:"e1 \<noteq> Bool False"
    hence ?case using red_helper[of _ e2] by auto
  }
  ultimately show ?case by blast
next
  case (T_IfFalse G e1 t1 f1p f1m e3 _  t2 f2 o2 _ e2)  
  let ?trm = "Iff e1 e2 e3"
  {
    assume "~ (e1 : values)"    
    then obtain E e' e'' where "e1 = E e'" and A:"e' \<hookrightarrow> e''" and "E : ctxt" using T_IfFalse
      unfolding closed_def fv_def trm.supp by blast
    hence ?case using ctxt_helper by auto
  }
  moreover
  {
    assume v:"e1 : values" and b:"e1 = Bool False"
    hence ?case using red_helper[of _ e3] by auto
  }
  moreover
  {
    assume v:"e1 : values" and b:"e1 \<noteq> Bool False"
    hence ?case using red_helper[of _ e2] by auto
  }
  ultimately show ?case by blast

qed


thm typing.induct

end