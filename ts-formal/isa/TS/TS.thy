(*
New Version
Started Jan 15, 2009

Using Isabelle repository snapshot 2eadbc24de8c (13-Jan-2009)

*)

theory TS
imports Nominal

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

nominal_datatype f = Bot | TE "ty" "pe list" "name" | NTE "ty" "pe list" "name"


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
  "zerop_fun (Num n) = Some (Bool True)"
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
  |"booleanp_fun (CONS a b) = True"
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
  |"procp_fun (CONS a b) = True"
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
simplefun :: "ty \<Rightarrow> ty \<Rightarrow> ty" ("_ \<rightarrow> _" 99)
[simp]:"simplefun t u == (t \<rightarrow> u : FH [] [] : None)"
proctop :: "ty"
[simp]:"proctop == Union [] \<rightarrow> Top"


fun
  \<Delta>\<^isub>\<tau> :: "builtin \<Rightarrow> ty"
  where
  "\<Delta>\<^isub>\<tau> NUMBERP = predty N"
  |"\<Delta>\<^isub>\<tau> BOOLEANP = predty B"
  |"\<Delta>\<^isub>\<tau> PROCEDUREP = predty proctop"
  |"\<Delta>\<^isub>\<tau> CONSP = predty <Top,Top>"
  |"\<Delta>\<^isub>\<tau> ADD1 = (N \<rightarrow> N)"
  |"\<Delta>\<^isub>\<tau> NOT = (Top \<rightarrow> B)"
  |"\<Delta>\<^isub>\<tau> ZEROP = (N \<rightarrow> B)"

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
    show ?case  
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
    have X_inst:"X = (S1 \<rightarrow> S2 : F : S, Q1 \<rightarrow> Q2 : F' : S', T)" using S_Fun by auto
    note `Q1 \<rightarrow> Q2 : F' : S' = Q`  
    hence Q12_less: "size Q1 < size Q" "size Q2 < size Q"  by auto
    have lh_drv_prm1: " \<turnstile> Q1 <: S1" by fact
    have lh_drv_prm2: " \<turnstile> S2 <: Q2" by fact      
    have "T=Top \<or> (\<exists>T1 T2 LL. T=T1\<rightarrow>T2 : LL \<and> \<turnstile>T1<:Q1 \<and> \<turnstile>Q2<:T2 \<and> LL = L') \<or> 
      (\<exists>T1 T2. T=T1\<rightarrow>T2 : latent_eff.NE \<and> \<turnstile>T1<:Q1 \<and> \<turnstile>Q2<:T2) \<or>
      (EX Ts T1. T = Union Ts \<and> T1 : set Ts \<and> \<turnstile> Q1 \<rightarrow> Q2 : L' <: T1)" 
      using S_ArrowE_left[OF rh_drv] by auto
    moreover
    { 
      assume "\<exists>T1 T2 LL. T=T1\<rightarrow>T2:LL \<and> \<turnstile>T1<:Q1 \<and> \<turnstile>Q2<:T2 \<and> LL = L'"
      then obtain T1 T2 LL
	where T_inst: "T = T1 \<rightarrow> T2 : L'" 
	and   rh_drv_prm1: " \<turnstile> T1 <: Q1"
	and   rh_drv_prm2: " \<turnstile> Q2 <: T2"
	and   LL': "LL = L'" by auto
      from X_inst T_inst have X_inst':"X = (S1 \<rightarrow> S2 : L, Q1 \<rightarrow> Q2 : L', T1 \<rightarrow> T2 : L')" by simp
      hence "size_ty3 (T1, Q1, S1) < size_ty3 X" using size_ty_pos by auto     
      from X_inst' lh_drv_prm1  rh_drv_prm1 have  " \<turnstile> T1 <: S1" using S_Fun(6)[of _ T1 Q1 S1] size_ty_pos by auto
      moreover
      from X_inst' lh_drv_prm2  rh_drv_prm2 have " \<turnstile> S2 <: T2" using S_Fun(6)[of _ S2 Q2   T2] size_ty_pos by auto
      ultimately have " \<turnstile> S1 \<rightarrow> S2 : L <: T1 \<rightarrow> T2 : LL" using LL' S_Fun by (simp add: subtype.S_Fun)
      hence " \<turnstile> S1 \<rightarrow> S2 : L <: T" using T_inst LL' by simp
    }
    moreover 
    { 
      assume "EX Ts T1. T = Union Ts \<and> T1 : set Ts \<and> \<turnstile> Q1 \<rightarrow> Q2 : L' <: T1"
      then obtain Ts T1
	where T_inst: "T = Union Ts"
	and elem: "T1 : set Ts"
	and sub:"\<turnstile> Q1 \<rightarrow> Q2 : L' <: T1"
	by auto
      have sub':"\<turnstile> S1 \<rightarrow> S2 : L <:  Q1 \<rightarrow> Q2 : L'" using S_Fun by simp
      have sz:"size T1 < size T" using T_inst elem union_size_ty by auto
      from X_inst T_inst have X_inst':"X = (S1 \<rightarrow> S2 : L, Q1 \<rightarrow> Q2 : L', Union Ts)" by simp
      from sub sub' X_inst' 
      have " \<turnstile> S1 \<rightarrow> S2 : L <: T1"  using S_Fun(6)[OF _ sub' sub]  sz T_inst by auto
      hence " \<turnstile> S1 \<rightarrow> S2 : L <: T"  using T_inst elem S_UnionAbove by auto      
    }
    moreover
    {
      assume "\<exists>T1 T2. T=T1\<rightarrow>T2:latent_eff.NE \<and> \<turnstile>T1<:Q1 \<and> \<turnstile>Q2<:T2 "
      then obtain T1 T2 LL
	where T_inst: "T = T1 \<rightarrow> T2 : latent_eff.NE" 
	and   rh_drv_prm1: " \<turnstile> T1 <: Q1"
	and   rh_drv_prm2: " \<turnstile> Q2 <: T2"
	 by auto
      from X_inst T_inst have X_inst':"X = (S1 \<rightarrow> S2 : L, Q1 \<rightarrow> Q2 : L', T1 \<rightarrow> T2 : latent_eff.NE)" by simp
      hence "size_ty3 (T1, Q1, S1) < size_ty3 X" using size_ty_pos by auto     
      from X_inst' lh_drv_prm1  rh_drv_prm1 have  " \<turnstile> T1 <: S1" using S_Fun(6)[of _ T1 Q1 S1] size_ty_pos by auto
      moreover
      from X_inst' lh_drv_prm2  rh_drv_prm2 have " \<turnstile> S2 <: T2" using S_Fun(6)[of _ S2 Q2   T2] size_ty_pos by auto
      ultimately have " \<turnstile> S1 \<rightarrow> S2 : L <: T1 \<rightarrow> T2 : latent_eff.NE" using  S_Fun by (simp add: subtype.S_Fun)
      hence " \<turnstile> S1 \<rightarrow> S2 : L <: T" using T_inst  by simp
    }
    ultimately show " \<turnstile> S1 \<rightarrow> S2 : L <: T" by blast
  next
    case (S_UnionAbove T1 Ts S)
    have sub1:"\<turnstile> S <: T1" by fact
    hence sub2:"\<turnstile> T1 <: T" using S_UnionAbove union_sub_elim[of Ts T T1] by auto
    have sz:"size T1 < size Q" using S_UnionAbove union_size_ty by auto
    hence "\<turnstile> S <: T" using S_UnionAbove(4)[OF _ sub1 sub2] sz S_UnionAbove(7) by auto
    thus ?case .
  next
    case (S_UnionBelow Ts S)
    have "!! T0. T0 : set Ts \<Longrightarrow> \<turnstile> T0 <: T"
      proof -
	fix T0
	assume "T0 : set Ts"
	hence sz:"size T0 < size (Union Ts)" using union_size_ty by auto
	have s1:"\<turnstile> T0 <: S" using S_UnionBelow `T0 : set Ts` by auto
	have s2:"\<turnstile> S <: T" using S_UnionBelow by auto
	note S_UnionBelow(6)
	thus "\<turnstile> T0 <: T" using S_UnionBelow(3)[OF _ s1 s2] sz `S = Q` by auto
      qed
    thus ?case ..
  qed
qed






end