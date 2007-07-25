theory TypedScheme
imports Nominal

begin


(* datatype definitions *)
atom_decl name

nominal_datatype latent_eff = NE | Latent ty

and ty = Top  | Int | Bool  |  Arr "ty" "ty" "latent_eff" ("_ \<rightarrow> _ : _" [100,100] 100)


nominal_datatype eff = NE | TE "ty" "name" | VE "name" | TT | FF


nominal_datatype builtin = Add1 | NumberP | BooleanP | Nott

nominal_datatype trm = 
    Var "name"
  | App "trm" "trm"
  | Abs "\<guillemotleft>name\<guillemotright>trm" "ty"
  | Iff "trm" "trm" "trm"
  | Num "nat"
  | Bool "bool"
  | BI "builtin"

abbreviation
  "lam" :: "name \<Rightarrow> ty \<Rightarrow> trm \<Rightarrow> trm" ("Lam [_:_]._" [100,100,100] 100) where
  "Lam[x:T].b \<equiv> trm.Abs x b T"

(* lemmas about names, types, effects *)

lemma trm_finite_supp:
  fixes x::"trm"
  shows "finite ((supp x)::name set)"
  using fs_name_class.axioms[of x] by simp

lemma eq_eqvt:
  fixes pi::"name prm"
  and   x::"'a::pt_name"
  shows "pi\<bullet>(x=y) = ((pi\<bullet>x)=(pi\<bullet>y))"
  by (simp add: perm_bool perm_bij)

lemma pt_trm_inst: "pt TYPE(trm) TYPE(name)" using pt_name_inst by auto

lemma fs_trm_inst: "fs TYPE(trm) TYPE(name)" using fs_name_inst by auto

lemma perm_ty_latent[simp]: 
  fixes T::"ty"
  and   le::"latent_eff"
  and   pi::"name prm"
  shows "pi\<bullet>le = le \<and> pi\<bullet>T = T"
  by (induct rule: latent_eff_ty.weak_induct) (simp_all)

lemma perm_builtin[simp]: 
  fixes e::"builtin"
  and   pi::"name prm"
  shows "pi\<bullet>e = e"
  by (induct rule: builtin.weak_induct) (simp_all)

lemma fresh_ty[simp]:
  fixes x::"name" 
  and   T::"ty"
  shows "x\<sharp>T"
  by (simp add: fresh_def supp_def)

lemma fresh_latent_eff[simp]:
  fixes x::"name" 
  and   T::"latent_eff"
  shows "x\<sharp>T"
  by (simp add: fresh_def supp_def)

lemma fresh_builtin[simp]:
  fixes x::"name" 
  and   b::"builtin"
  shows "x\<sharp>b"
  by (simp add: fresh_def supp_def)

lemma supp_latent_eff_ty:
  fixes T::ty and le::latent_eff
  shows " supp le = ({}::name set)  \<and> supp T = ({}::name set)"
  by (nominal_induct  rule: latent_eff_ty.induct) (auto simp add: latent_eff.supp ty.supp)



text {* size of a term *}

consts 
  size :: "trm \<Rightarrow> nat"

nominal_primrec
  "size (Var x) = 1"
  "size (BI b) = 1"
  "size (Bool b) = 1"
  "size (Num b) = 1"
  "size (App t1 t2) = (max (size t1) (size t2)) + 1"
  "size (Iff t1 t2 t3) = (max (size t1) (max (size t2) (size t3))) + 1"
  "size (Lam [a:T].t) = (size t) + 1"
  apply(finite_guess add: perm_nat_def)+
  apply(auto simp add: fresh_nat)
  apply(fresh_guess add: perm_nat_def)+
  done

constdefs 
smaller_than :: "(trm * trm) set" 
"smaller_than == measure size"


abbreviation
  "smaller_than_abb" :: "trm \<Rightarrow> trm \<Rightarrow> bool" ("_ \<guillemotleft> _" [80,80] 80)
where 
  "a \<guillemotleft> b == (a,b) : smaller_than"



lemma wf_st:"wf smaller_than" using wf_measure[of size] smaller_than_def by auto

text {* complete induction on terms *}

lemma trm_comp_induct1[consumes 0, case_names Var App Lam BI Num Bool Iff]:
  fixes P::"'a::fs_name \<Rightarrow> trm \<Rightarrow> bool"
  and t::"trm"
  and x::"'a::fs_name"
  assumes a1:"!! n z. (!! x t. (t,Var n) : smaller_than \<Longrightarrow> P x t) \<Longrightarrow> P z (Var n)"
  and a2:"!! t1 t2 z. (!! x t. (t,App t1 t2) : smaller_than \<Longrightarrow> P x t) \<Longrightarrow> P z (App t1 t2)"
  and a3:"!! a b z T. \<lbrakk>a \<sharp> z ; (!! x t. (t,Lam[a:T].b) : smaller_than \<Longrightarrow> P x t)\<rbrakk> \<Longrightarrow> P z (Lam[a:T].b)"
  and a4:"!! b z. (!! x t. (t,BI b) : smaller_than \<Longrightarrow> P x t) \<Longrightarrow> P z (BI b)"
  and a5:"!! n z. (!! x t. (t,Num n) : smaller_than \<Longrightarrow> P x t) \<Longrightarrow> P z (Num n)"
  and a6:"!! b z. (!! x t. (t,Bool b) : smaller_than \<Longrightarrow> P x t) \<Longrightarrow> P z (Bool b)"
  and a7:"!! t1 t2 t3 z. (!! x t. t \<guillemotleft> (Iff t1 t2 t3) \<Longrightarrow> P x t) \<Longrightarrow> P z (Iff t1 t2 t3)"
  shows "P x t"
proof (induct arbitrary: x rule: wf_induct[of smaller_than])
  case 1 thus ?case using wf_st by auto
next
  case (2 s x) thus ?case
    -- "This would go through automatically, but I'm skeptical of that sort of thing"
  proof (nominal_induct s avoiding: x rule: trm.induct)
    case (Var v) thus ?case using a1[of v x] by auto
  next
    case (App t1 t2) thus ?case using a2 by auto
  next
    case (Abs a b T) thus ?case using a3 by auto
  next
    case (Iff t1 t2 t3) thus ?case using a7 by auto
  next
    case (BI b) thus ?case using a4 by auto
  next
    case (Num n) thus ?case using a5 by auto
  next
    case (Bool b) thus ?case using a6 by auto    
  qed
qed

thm trm.induct

lemma trm_comp_induct[consumes 0, case_names Var App Lam BI Num Bool Iff]:
  fixes P::"'a::fs_name \<Rightarrow> trm \<Rightarrow> bool"
  and t::"trm"
  and x::"'a::fs_name"
  assumes a1:"!! n z. (!! x t. (t,Var n) : smaller_than \<Longrightarrow> P x t) \<Longrightarrow> P z (Var n)"
  and a2:"!! t1 t2 z. (!! x t. (t,App t1 t2) : smaller_than \<Longrightarrow> P x t) \<Longrightarrow> (!! x. P x t1) \<Longrightarrow> (!! x . P x t2)
  \<Longrightarrow> P z (App t1 t2)"
  and a3:"!! a b z T. \<lbrakk>a \<sharp> z ; (!! x t. (t,Lam[a:T].b) : smaller_than \<Longrightarrow> P x t)\<rbrakk> \<Longrightarrow> (!! x . P x b) \<Longrightarrow> P z (Lam[a:T].b)"
  and a4:"!! b z. (!! x t. (t,BI b) : smaller_than \<Longrightarrow> P x t) \<Longrightarrow> P z (BI b)"
  and a5:"!! n z. (!! x t. (t,Num n) : smaller_than \<Longrightarrow> P x t) \<Longrightarrow> P z (Num n)"
  and a6:"!! b z. (!! x t. (t,Bool b) : smaller_than \<Longrightarrow> P x t) \<Longrightarrow> P z (Bool b)"
  and a7:"!! t1 t2 t3 z. (!! x t. t \<guillemotleft> (Iff t1 t2 t3) \<Longrightarrow> P x t) 
  \<Longrightarrow> (!! x. P x t1) \<Longrightarrow> (!! x . P x t2) \<Longrightarrow> (!! x. P x t3) \<Longrightarrow> P z (Iff t1 t2 t3)"
  shows "P x t"
  proof (nominal_induct t avoiding: x rule: trm_comp_induct1)
    case App thus ?case using a2 
      by (auto simp add: smaller_than_def measure_def)
  next
    case Var thus ?case using a1
      by (auto simp add: smaller_than_def measure_def)
  next
    case Lam thus ?case using a3
      by (auto simp add: smaller_than_def measure_def)
  next
    case Bool thus ?case using a6
      by (auto simp add: smaller_than_def measure_def)
  next
    case Num thus ?case using a5
      by (auto simp add: smaller_than_def measure_def)
  next
    case BI thus ?case using a4
      by (auto simp add: smaller_than_def measure_def)
  next
    case Iff thus ?case using a7
      by (auto simp add: smaller_than_def measure_def)
  qed



text {* closed terms *}

constdefs
fv :: "trm \<Rightarrow> name set"
fv_def[simp]:"fv e == ((supp e):: name set)"

constdefs
  closed :: "trm \<Rightarrow> bool"
  closed_def: "closed e == (fv e = {})"


lemma closed_lam: --"A statement about the free variables of lam bodies"
  assumes "closed (Lam[x:T].b)" (is "closed ?e")
  shows "fv b <= {x}"
  proof -
    have "(supp ([x].b)::name set) = supp b - {x}" 
      using fs_name_class.axioms abs_fun_supp[of b x] pt_trm_inst at_name_inst by auto
    hence "supp ?e = ((((supp b):: name set) - {x}) :: name set)" using supp_latent_eff_ty trm.supp by simp
    thus ?thesis using prems closed_def by auto 
  qed

lemma closed_eqvt:
  fixes pi::"name prm"
  shows "closed e \<Longrightarrow> closed (pi\<bullet>e)"
proof -
  have A:"(pi\<bullet>fv e) = fv (pi\<bullet>e)" using pt_perm_supp[of pi e] at_name_inst pt_trm_inst by auto
  assume "closed e"
  hence "fv e = {}" using closed_def by simp
  hence "(pi\<bullet>fv e) = {}" using empty_eqvt[of pi] by auto
  hence "closed (pi\<bullet>e)" using A closed_def by auto
  thus ?thesis .
qed    


text {* capture-avoiding substitution *}

consts subst :: "trm \<Rightarrow> name \<Rightarrow> trm \<Rightarrow> trm" ("_[_::=_]" [100,100,100] 100)

nominal_primrec
 "(Var x)[y::=t'] = (if x=y then t' else (Var x))"
 "(App t1 t2)[y::=t'] = App (t1[y::=t']) (t2[y::=t'])"
 "x\<sharp>(y,t',T) \<Longrightarrow> (Lam[x:T].t)[y::=t'] = Lam[x:T].(t[y::=t'])"
 "(Iff tst thn els)[y::=t'] = (Iff (tst[y::=t']) (thn[y::=t']) (els[y::=t']))"
 "(BI c)[y::=t'] = (BI c)"
 "(Num c)[y::=t'] = (Num c)"
 "(Bool c)[y::=t'] = (Bool c)"
apply(finite_guess add: eq_eqvt if_eqvt fs_name1)+
apply(perm_full_simp)
apply(auto simp add: fs_name1 eq_eqvt abs_fresh)
apply(fresh_guess add: eq_eqvt fs_name1)+
done


lemma subst_eqvt[simp]:
  fixes pi:: "name prm"
  and   t1:: "trm"
  and   t2:: "trm"
  and   a :: "name"
  shows "pi\<bullet>(t1[b::=t2]) = (pi\<bullet>t1)[(pi\<bullet>b)::=(pi\<bullet>t2)]"
apply(nominal_induct t1 avoiding: b t2 rule: trm.induct)
apply(auto simp add: perm_bij fresh_prod fresh_atm fresh_bij)
done

lemma subst_rename[rule_format]: 
  shows "c\<sharp>t1 \<longrightarrow> (t1[a::=t2] = ([(c,a)]\<bullet>t1)[c::=t2])"
apply(nominal_induct t1 avoiding: a c t2 rule: trm.induct)
apply(auto simp add: calc_atm fresh_atm abs_fresh fresh_nat trm.inject perm_nat_def perm_bool)
done

lemma forget: 
  assumes a: "a\<sharp>t1"
  shows "t1[a::=t2] = t1"
  using a
apply (nominal_induct t1 avoiding: a t2 rule: trm.induct)
apply(auto simp add: abs_fresh fresh_atm)
done

lemma fresh_fact: 
  fixes a::"name"
  assumes a: "a\<sharp>t1"
  and     b: "a\<sharp>t2"
  shows "a\<sharp>(t1[b::=t2])"
using a b
apply(nominal_induct t1 avoiding: a b t2 rule: trm.induct)
apply(auto simp add: abs_fresh fresh_atm)
done

lemma subst_lemma:
  fixes N::trm
  assumes a: "x\<noteq>y"
  and     b: "x\<sharp>L"
  shows "M[x::=N][y::=L] = M[y::=L][x::=N[y::=L]]"
using a b
by (nominal_induct M avoiding: x y N L rule: trm.induct)
   (auto simp add: fresh_fact forget)

lemma id_subs: "t[x::=Var x] = t"
apply(nominal_induct t avoiding: x rule: trm.induct)
apply(simp_all add: fresh_atm)
done

lemma subst_removes_var:
  assumes "e1[x::=e0] = e2" and "x \<sharp> e0"
  shows "x \<sharp> e2"
  using prems
  proof (nominal_induct e1 avoiding: e0 x e2 rule: trm.induct)
    case (Var v e0' x' e2')
    thus ?case using at_fresh[of x' v] at_name_inst
      by (cases "x' = v") auto
  next
    case App thus ?case by auto
  next
    case Iff thus ?case by auto
  next
    case BI thus ?case by auto
  next
    case Num thus ?case by (auto simp add: fresh_nat)
  next
    case (Bool b) thus ?case 
      by (auto simp add: fresh_def supp_bool trm.supp)
  next
    case (Abs v e1' T e0' x' e2')
    let ?body = "(e1'[x'::=e0'])"
    have a:"finite ((supp ?body) :: name set)" using fs_name1 by auto
    have f:"x' \<sharp> (e1'[x'::=e0'])" using Abs by auto
    hence "v \<sharp> (x',e0',T)" using Abs by auto
    hence "(Abs v e1' T)[x'::=e0'] = Abs v (e1'[x'::=e0']) T" by auto
    hence "... = e2'" using Abs by auto
    have "v \<noteq> x'" using `v \<sharp> x'` at_fresh[of v x'] at_name_inst by auto
    hence "x' \<sharp> v" using  at_fresh[of x' v] at_name_inst by auto
    have "x' \<sharp> T" using fresh_def supp_latent_eff_ty by auto
    have "x' \<sharp> [v].(e1'[x'::=e0'])" using `v ~= x'` fresh_abs_funI1[of ?body x' v ] pt_trm_inst at_name_inst a f by auto
    hence "x' \<sharp>  Abs v (e1'[x'::=e0']) T" using f trm.fresh Abs by auto
    thus ?case using Abs  by auto
  qed
 

lemma fv_lam:
  "fv (Lam[name:T].body) =  fv body - {name}"
  proof -
    have sT:"supp T = ({} :: name set)" using supp_latent_eff_ty by auto
    have "fv (Lam[name:T].body) = (supp ([name].body):: name set) \<union> supp T" using trm.supp by auto
    also have "\<dots> = (supp ([name].body):: name set)" using sT by auto
    also have "\<dots> = supp body - ({name} :: name set)" 
      using  abs_fun_supp[of body name] at_name_inst pt_trm_inst fs_name1[of body] by simp
    also have "\<dots> = fv body - {name}" by simp
    finally show "fv (Lam[name:T].body) = fv body - {name}" by simp
  qed

lemma subst_closed:
  assumes "e1[x::=e0] = e2" and "closed e0"
  shows "fv e2 <= fv e1"
  using prems
  proof (nominal_induct e1 avoiding: e0 x e2 rule: trm.induct)
    case (Var v e0' x' e2')
    thus ?case using at_fresh[of x' v] at_name_inst closed_def
      by (cases "x' = v") auto
  next
    case (App rator rand e0' x' e2')
    let ?subrator = "rator[x'::=e0']"
    let ?subrand = "rand[x'::=e0']"
    have a:"e2' = App ?subrator ?subrand" using App by simp
    have s1:"fv ?subrator <= fv rator" using App by simp
    have s2:"fv ?subrand <= fv rand" using App by simp
    have b:"fv e2' = fv ?subrator \<union> fv ?subrand" using trm.supp App a by simp
    have d:"fv (App rator rand) = fv rator  \<union> fv rand" using trm.supp by simp
    show ?case using d s1 s2 b by auto
 next
    case BI thus ?case by auto
  next
    case Num thus ?case by (auto simp add: fresh_nat)
  next
    case (Bool b) thus ?case 
      by (auto simp add: fresh_def supp_bool trm.supp)
  next
    case (Iff tst thn els e0' x' e2')
    let ?subtst = "tst[x'::=e0']"
    let ?subthn = "thn[x'::=e0']"
    let ?subels = "els[x'::=e0']"
    have a:"e2' = Iff ?subtst ?subthn ?subels" using Iff by simp
    have s1:"fv ?subtst <= fv tst" using Iff by simp
    have s2:"fv ?subthn <= fv thn" using Iff by simp
    have s3:"fv ?subels <= fv els" using Iff by simp
    have b:"fv e2' = fv ?subtst \<union> fv ?subthn \<union> fv ?subels" using trm.supp Iff a by auto
    have d:"fv (Iff tst thn els) = fv tst  \<union> fv thn  \<union> fv els" using trm.supp by auto
    show ?case using d s1 s2 s3 b by auto
  next
    case (Abs name body T e0' x' e2')
    have aa:"fv (body[x'::=e0']) \<subseteq> fv body" using Abs by auto
    have a:"fv (Lam[name:T].body) = fv body - {name}" using fv_lam by simp
    have b:"fv (Lam[name:T].(body[x'::=e0'])) = fv (body[x'::=e0']) - {name}" using fv_lam by simp
    have "name \<sharp> (e0',T,x')" using Abs by auto
    hence c:"(Lam[name:T].(body[x'::=e0'])) = (Lam[name:T].(body))[x'::=e0']" by simp
    hence d:"fv e2' = fv (body[x'::=e0']) - {name}" using b Abs by auto
    thus ?case using a aa  by auto
  qed
  
 
lemma subst_only_var_closed:
  assumes "closed e0" and "fv e1 <= {x}"
  shows "closed (e1[x::=e0])"
  proof -
    let ?e2 = "(e1[x::=e0])"
    have a:"fv ?e2 <= {x}" using prems subst_closed[of e1 x e0 ?e2] by auto
    have "x \<sharp> e0" using prems fresh_def[of x e0] closed_def[of e0] by auto
    hence "x \<sharp> ?e2" using subst_removes_var[of e1 x e0 ?e2] by auto
    hence b:"x \<notin> fv ?e2" using fresh_def[of x ?e2] closed_def[of ?e2] by auto
    from a b have "fv ?e2 = {}" by auto
    thus ?thesis using closed_def by simp
  qed

lemma beta_closed_closed:
  assumes "closed (Lam[x:T].b)" and "closed v"
  shows "closed (b[x::=v])"
  using prems closed_lam subst_only_var_closed
  by auto


text {* values *}

consts 
  values :: "trm set"

inductive values
  intros
  abs_value[simp]: "Lam[x:t].b \<in> values"
  bi_value[simp]: "BI c \<in> values"
  num_value[simp]: "Num n \<in> values"
  bool_value[simp]: "Bool b \<in> values"

lemma values_eqvt:
  fixes pi :: "name prm"
  and   t  :: "trm"
  assumes a:"t : values"
  shows "(pi\<bullet>t) : values"
  using a by induct auto

lemma not_false_eqvt:
  fixes pi :: "name prm"
  and   t  :: "trm"
  assumes a:"t ~= trm.Bool False" and b:"t : values"
  shows "(pi\<bullet>t) ~= trm.Bool False"
  using b a
  by induct (auto simp add: perm_bool)

lemma values_induct[consumes 1, case_names bool_value num_value bi_value abs_value]:
  fixes  P :: "'a::fs_name\<Rightarrow>trm \<Rightarrow>bool"
  and    v :: "trm"
  and    x :: "'a::fs_name"
  assumes a: "v : values"
  and a1:    "\<And>b x. P x (Bool b)"
  and a2:    "\<And>n x. P x (Num n)"
  and a3:    "\<And>b x. P x (BI b)"
  and a4:    "\<And>a T b x. a\<sharp>x \<Longrightarrow> P x (Lam [a:T].b)"
  shows "P x v"
proof -
  from a have "\<And>(pi::name prm) x. P x (pi\<bullet>v)"
  proof (induct)
    case bool_value thus ?case using a1 perm_bool by auto
  next
    case num_value thus ?case using a2 perm_nat_def by auto
  next
    case bi_value thus ?case using a3 builtin.perm by auto
  next
    case (abs_value b T a pi x) thus ?case
    proof (simp add: values_eqvt)
      have f: "\<exists>c::name. c\<sharp>(pi\<bullet>a,pi\<bullet>b,pi\<bullet>T,x)"
	by (rule exists_fresh', simp add: fs_name1)
      then obtain c::"name" 
	where f1: "c\<noteq>(pi\<bullet>a)" and f2: "c\<sharp>x" and f3: "c\<sharp>(pi\<bullet>T)" and f4: "c\<sharp>(pi\<bullet>b)"
	by (force simp add: fresh_prod fresh_atm)
      have x: "P x (Lam [c:T].(([(c,pi\<bullet>a)]@pi)\<bullet>b))"
	using a4 f2 by (blast intro!: values_eqvt)
      have alpha1: "(Lam [c:T].([(c,pi\<bullet>a)]\<bullet>(pi\<bullet>b))) = (Lam [(pi\<bullet>a):T].(pi\<bullet>b))" using f1 f3
	by (simp add: trm.inject alpha)
      show "P x (Lam [(pi\<bullet>a):T].(pi\<bullet>b))"
	using x alpha1 by (simp only: pt_name2)
    qed
  qed
  hence "P x (([]::name prm)\<bullet>v)" by blast 
  thus ?thesis by simp
qed





text {* Typing Constants *}


consts
  \<Delta>\<^isub>\<tau> :: "builtin \<Rightarrow> ty"

nominal_primrec
  "\<Delta>\<^isub>\<tau> NumberP = (Top \<rightarrow> ty.Bool : Latent ty.Int)"
  "\<Delta>\<^isub>\<tau> BooleanP = (Top \<rightarrow> ty.Bool : Latent ty.Bool)"
  "\<Delta>\<^isub>\<tau> Add1 = (ty.Int \<rightarrow> ty.Int : latent_eff.NE)"
  "\<Delta>\<^isub>\<tau> Nott = (ty.Bool \<rightarrow> ty.Bool : latent_eff.NE)"
  by simp_all

(* Delta Function *)

consts
  \<Delta>  :: "builtin \<Rightarrow> trm \<Rightarrow> trm option"
  add1_fun :: "trm \<Rightarrow> trm option"
  nott_fun :: "trm \<Rightarrow> trm option"
  numberp_fun :: "trm \<Rightarrow> bool"
  booleanp_fun :: "trm \<Rightarrow> bool"

nominal_primrec
  "add1_fun (Num n) = Some (Num (n+1))"
  "add1_fun (Lam[x:ty].b) = None"
  "add1_fun (Iff a b c) = None"
  "add1_fun (App a b) = None"
  "add1_fun (Bool a) = None"
  "add1_fun (BI a) = None"
  "add1_fun (Var a) = None"
  apply auto
  apply(finite_guess add: eq_eqvt if_eqvt fs_name1 supp_none fresh_none fresh_set_empty supp_set_empty fresh_nat abs_fresh)+
  apply(auto simp add: fs_name1 eq_eqvt abs_fresh supp_none fresh_none fresh_set_empty supp_set_empty fresh_nat fresh_some ty.supp)
  apply(fresh_guess add: eq_eqvt if_eqvt fs_name1 supp_none fresh_none fresh_set_empty supp_set_empty fresh_nat fresh_some abs_fresh)+
  done

nominal_primrec
  "nott_fun (Num n) = None"
  "nott_fun (Lam[x:ty].b) = None"
  "nott_fun (Iff a b c) = None"
  "nott_fun (App a b) = None"
  "nott_fun (Bool b) = Some (Bool (~b))"
  "nott_fun (BI a) = None"
  "nott_fun (Var a) = None"
  apply auto
  apply(finite_guess add: eq_eqvt if_eqvt fs_name1 supp_none fresh_none fresh_set_empty supp_set_empty perm_bool abs_fresh)+
  apply(auto simp add: fs_name1 eq_eqvt abs_fresh supp_none fresh_none fresh_set_empty supp_set_empty perm_bool fresh_some ty.supp)
  apply(fresh_guess add: eq_eqvt if_eqvt fs_name1 supp_none fresh_none fresh_set_empty supp_set_empty perm_bool fresh_some abs_fresh)+
  done

nominal_primrec
  "booleanp_fun (Bool b) = True"
  "booleanp_fun (Num n) = False"
  "booleanp_fun (Abs a b c) = False"
  "booleanp_fun (App a b) = False"
  "booleanp_fun (BI c) = False"
  "booleanp_fun (Var v) = False"
  "booleanp_fun (Iff a b c) = False"
  apply auto
  apply(finite_guess add: eq_eqvt if_eqvt fs_name1 supp_none fresh_none fresh_set_empty supp_set_empty perm_bool abs_fresh)+
  apply(auto simp add: fs_name1 eq_eqvt abs_fresh supp_none fresh_none fresh_set_empty supp_set_empty perm_bool fresh_some ty.supp)
  apply(fresh_guess add: eq_eqvt if_eqvt fs_name1 supp_none fresh_none fresh_set_empty supp_set_empty perm_bool fresh_some abs_fresh)+
  done

nominal_primrec
  "numberp_fun (Bool b) = False"
  "numberp_fun (Num n) = True"
  "numberp_fun (Abs a b c) = False"
  "numberp_fun (App a b) = False"
  "numberp_fun (BI c) = False"
  "numberp_fun (Var v) = False"
  "numberp_fun (Iff a b c) = False"
  apply auto
  apply(finite_guess add: eq_eqvt if_eqvt fs_name1 supp_none fresh_none fresh_set_empty supp_set_empty perm_bool abs_fresh)+
  apply(auto simp add: fs_name1 eq_eqvt abs_fresh supp_none fresh_none fresh_set_empty supp_set_empty perm_bool fresh_some ty.supp)
  apply(fresh_guess add: eq_eqvt if_eqvt fs_name1 supp_none fresh_none fresh_set_empty supp_set_empty perm_bool fresh_some abs_fresh)+
  done

nominal_primrec
  "\<Delta> Add1 t = add1_fun t"
  "\<Delta> Nott t = nott_fun t"
  "\<Delta> BooleanP t = Some (Bool (booleanp_fun t))"
  "\<Delta> NumberP t = Some (Bool (numberp_fun t))"
by simp_all


lemma delta_eqvt:
  fixes pi :: "name prm"
  and   b :: builtin
  and   t  :: "trm"
  assumes a:"\<Delta> b t = Some v"
  shows "\<Delta> b (pi\<bullet>t) = Some (pi\<bullet>v)"
  using a
proof (nominal_induct rule: builtin.induct)
  case Add1
  thus ?case 
    by (nominal_induct t rule: trm.induct) (auto simp add: perm_nat_def)       
next
  case Nott
  thus ?case 
    by (nominal_induct t rule: trm.induct) (auto simp add: perm_bool)
next
  case BooleanP
  thus ?case 
    by (nominal_induct t rule: trm.induct) (auto simp add: perm_bool)
next
  case NumberP
  thus ?case 
    by (nominal_induct t rule: trm.induct) (auto simp add: perm_bool)
qed

lemma delta_closed:
  fixes b :: builtin and t::trm
  assumes "\<Delta> b t = Some v"
  shows "closed v"
  using prems
  proof (nominal_induct b rule: builtin.induct)
    case Add1
    thus ?case by (nominal_induct t rule: trm.induct) (auto simp add: supp_nat closed_def trm.supp)
  next
    case Nott
    thus ?case
      by (nominal_induct t rule: trm.induct)
         (auto simp add: supp_def perm_bool closed_def trm.supp)
  next
    case BooleanP
    thus ?case
      by (nominal_induct t rule: trm.induct)
         (auto simp add: supp_def perm_bool closed_def trm.supp)
  next
    case NumberP
    thus ?case
      by (nominal_induct t rule: trm.induct)
         (auto simp add: supp_def perm_bool closed_def trm.supp)
       qed

lemma delta_value:
  fixes b :: builtin and t::trm
  assumes "\<Delta> b t = Some v"
  shows "v : values"
  using prems
  proof (nominal_induct b rule: builtin.induct)
    case Add1
    thus ?case by (nominal_induct t rule: trm.induct) auto
  next
    case Nott
    thus ?case
      by (nominal_induct t rule: trm.induct) auto
  next
    case BooleanP
    thus ?case
      by (nominal_induct t rule: trm.induct) auto
  next
    case NumberP
    thus ?case
      by (nominal_induct t rule: trm.induct) auto
  qed

text {* Evaluation contexts *}

consts 
  ctxt :: "(trm \<Rightarrow> trm) set"
  frame :: "(trm \<Rightarrow> trm) set"

inductive ctxt
intros
  C_Hole[simp, intro]: "(%t. t) \<in> ctxt"
  C_App1[simp, intro]: "E : ctxt \<Longrightarrow> (%t .  (App (E t) u)) : ctxt"
  C_App2[simp, intro]: "E : ctxt \<Longrightarrow> v : values \<Longrightarrow> (%t . (App v (E t))) : ctxt"
  C_Iff[simp, intro]: "E : ctxt \<Longrightarrow> (%t . (Iff (E t) thn els)) : ctxt"

lemma ctxt_compose:
  assumes a:"E1 : ctxt" and b:"E2 : ctxt"
  shows "(%t. E1 (E2 t)) : ctxt"
  using a b
  by (induct E1) auto

constdefs
  closed_ctxt :: "(trm \<Rightarrow> trm) \<Rightarrow> bool"
  closed_ctxt_def[simp]:"closed_ctxt C == (C : ctxt \<and> closed (C (Num 3)))" --"3 is a trivially closed term"

lemma ctxt_closed:
  assumes "closed_ctxt C" 
  shows "closed (C e) = closed e"
  using prems
proof -
  have "C : ctxt" using prems by simp
  thus ?thesis using prems
    by (induct) (auto simp add: closed_def trm.supp)
qed  
 
lemma closed_in_ctxt_closed_ctxt:
  assumes "closed e" and a:"C : ctxt" and "e = C L"
  shows "closed L \<and> closed_ctxt C"
  using a prems 
  proof (induct C arbitrary: L e rule: ctxt.induct)
    case C_Hole
    thus ?case by (auto simp add: closed_def trm.supp supp_nat)
  next
    case (C_App1 E arg L' e')
    have IH:"!!e L. \<lbrakk>closed e; E \<in> ctxt; e = E L\<rbrakk> \<Longrightarrow> closed L \<and> closed_ctxt E" using prems by blast
    have cl:"closed (App (E L') arg)" using `e' = (App (E L') arg)` `closed e'` by simp
    from cl have "closed arg"by (auto simp add: closed_def trm.supp)
    from cl have "closed (E L')"  by (auto simp add: closed_def trm.supp)
    thus ?case using IH[of "(E L')" L'] `E : ctxt` `closed arg`
      by (auto simp add: trm.supp closed_def)
  next
    case (C_App2 E rator L' e')
    have IH:"!!e L. \<lbrakk>closed e; E \<in> ctxt; e = E L\<rbrakk> \<Longrightarrow> closed L \<and> closed_ctxt E" using prems by blast
    have cl:"closed (App rator (E L'))" using prems by blast
    from cl have "closed rator" by (auto simp add: closed_def trm.supp)
    from cl have "closed (E L')"  by (auto simp add: closed_def trm.supp)
    thus ?case using IH[of "(E L')" L'] `E : ctxt` `closed rator`
      by (auto simp add: trm.supp closed_def)
  next
    case (C_Iff E els thn L' e')
    let ?trm = "Iff (E L') thn els"
    have IH:"!!e L. \<lbrakk>closed e; E \<in> ctxt; e = E L\<rbrakk> \<Longrightarrow> closed L \<and> closed_ctxt E" using prems by blast
    have cl:"closed ?trm" using prems by blast
    from cl have "closed thn" and "closed els" by (auto simp add: closed_def trm.supp)
    from cl have "closed (E L')"  by (auto simp add: closed_def trm.supp)
    thus ?case using IH[of "(E L')" L'] `E : ctxt` `closed thn` `closed els`
      by (auto simp add: trm.supp closed_def)
  qed

lemma closed_in_ctxt:
  assumes "closed (C L)"
  and "C : ctxt"
  shows "closed L"
  using `C : ctxt` `closed (C L)`
  by (induct C) (auto simp add: closed_def trm.supp)



text{* Reduction *}


consts
  reduce :: "(trm * trm) set"

syntax
  reduce_syn :: "trm => trm => bool"  ("_ \<hookrightarrow> _" [200,200] 200)

translations
 "redex \<hookrightarrow> res"  \<rightleftharpoons> "(redex,res) \<in> reduce"


inductive reduce
  intros
e_beta[simp]: "v : values \<Longrightarrow> (App (Lam[x:t].b) v) \<hookrightarrow> (b[x::=v])"
e_if_false[simp]: "Iff (Bool False) e1 e2 \<hookrightarrow> e2"
e_if_true[simp]: "v ~= Bool False \<Longrightarrow> v : values \<Longrightarrow> Iff v e1 e2 \<hookrightarrow> e1"
e_delta[simp]: "\<lbrakk>v : values; \<Delta> p v = Some e\<rbrakk> \<Longrightarrow> App (BI p) v \<hookrightarrow> e"


inductive2
  "step" :: "trm\<Rightarrow>trm\<Rightarrow>bool" (" _ \<longrightarrow> _" [80,80]80)
where
  step_one[intro]:"\<lbrakk>E : ctxt; L \<hookrightarrow> R\<rbrakk> \<Longrightarrow> E L \<longrightarrow> E R"

(* constdefs
step_multi :: "trm \<Rightarrow> trm \<Rightarrow> bool" (" _ \<longrightarrow>\<^sup>* _" [80,80] 80)
"step_multi a b == step^*"
*)

(* reduction examples *)


lemma "(App (Lam [x:t].(Var x)) (Num 4)) \<hookrightarrow> Num 4"
  proof -
    have "Num 4 : values" by auto
    hence h:"(App (Lam [x:t].(Var x)) (Num 4)) \<hookrightarrow> ((Var x)[x::=(Num 4)])" by (rule e_beta)
    have "((Var x)[x::=(Num 4)]) = Num 4" by auto
    thus ?thesis using h  by auto
  qed

(* some lemmas about reduction *)

lemma if_val_reduces: 
  assumes a:"tst : values"
  shows "Iff tst thn els \<hookrightarrow> thn \<or> Iff tst thn els \<hookrightarrow> els"
  using a
proof (nominal_induct tst rule: trm.induct)
  case (Bool b) 
  thus ?case using e_if_true e_if_false
    by (cases b) (auto simp add: trm.inject)
qed (auto)

lemma ex_help: 
  assumes a:"e = E t \<and> E : ctxt \<and>  t \<hookrightarrow> t'"
  shows "\<exists>E t t' . e = E t \<and> E \<in> ctxt \<and> t \<hookrightarrow> t'"
  proof -
    from a have "\<exists>E . e = E t \<and> E \<in> ctxt \<and> t \<hookrightarrow> t'" by auto
    hence "\<exists>E t . e = E t \<and> E \<in> ctxt \<and> t \<hookrightarrow> t'" by auto
    thus "\<exists>E t t' . e = E t \<and> E \<in> ctxt \<and> t \<hookrightarrow> t'" by auto
  qed



lemma reduce_in_ctxt:
  fixes e :: trm
  assumes ct:"C : ctxt"
  and ih:"(EX E L R. e = E L \<and> E : ctxt \<and> L \<hookrightarrow> R)"
  shows "(EX E L R. C e = E L \<and> E : ctxt \<and> L \<hookrightarrow> R)"
proof -
  from ih ct obtain Enew tnew t'new where "e = Enew tnew" and  "Enew \<in> ctxt" and g1:"tnew \<hookrightarrow> t'new" by auto
  let ?E="(%t . C (Enew t))"
  have g2:"?E : ctxt" using  `Enew : ctxt` using ct ctxt_compose[of "(%t . C t)" Enew] by auto
  have g3:"?E tnew = C e" using `e = Enew tnew` by auto
  thus "\<exists>E t t' . C e = E t \<and> E \<in> ctxt \<and> t \<hookrightarrow> t'"
    using g1 g2 g3 ex_help[of "C e" ?E tnew] by auto
qed


lemma eqvt_reduce: 
  fixes pi :: "name prm"
  and   t  :: "trm"
  and   s  :: "trm"
  assumes a: "t  \<hookrightarrow> s"
  shows "(pi\<bullet>t) \<hookrightarrow> (pi\<bullet>s)"
  using a
  by induct (auto simp add: values_eqvt subst_eqvt not_false_eqvt delta_eqvt)


(* strengthend induction principle for reduction, taking into account freshness *)

lemma reduce_induct[consumes 1, case_names e_if_false e_if_true e_delta e_beta]:
  fixes  P :: "'a::fs_name\<Rightarrow>trm \<Rightarrow> trm \<Rightarrow>bool"
  and    t :: "trm"
  and    s :: "trm"
  and    x :: "'a::fs_name"
  assumes a: "t \<hookrightarrow> s"
  and a1:    "\<And>e1 e2 x. P x (Iff (trm.Bool False) e1 e2) e2"
  and a2:    "\<And>v e1 e2 x. \<lbrakk>v : values ; v \<noteq> trm.Bool False\<rbrakk> \<Longrightarrow> P x (Iff v e1 e2) e1"
  and a3:    "\<And>b v v' x. \<lbrakk>v : values ; \<Delta> b v = Some v'\<rbrakk> \<Longrightarrow> P x (App (BI b) v) v'"
  and a4:    "\<And>a t1 s1 ty x. a\<sharp>x \<Longrightarrow> P x (App (Lam [a:ty].t1) s1) (t1[a::=s1])"
  shows "P x t s"
proof -
  from a have "\<And>(pi::name prm) x. P x (pi\<bullet>t) (pi\<bullet>s)"
  proof (induct)
    case e_if_false thus ?case using a1 by simp
  next
    case (e_if_true thn els v) thus ?case using a2
      by (auto simp add: not_false_eqvt values_eqvt)
  next
    case (e_delta v' p v) thus ?case using a3 by (auto simp add: values_eqvt delta_eqvt)
  next
    case (e_beta s1 T s2 a _ x) thus ?case
    proof (simp add: subst_eqvt)
      have f: "\<exists>c::name. c\<sharp>(pi\<bullet>a,pi\<bullet>s1,pi\<bullet>s2,pi\<bullet>T,x)"
	by (rule exists_fresh', simp add: fs_name1)
      then obtain c::"name" 
	where f1: "c\<noteq>(pi\<bullet>a)" and f2: "c\<sharp>x" and f3: "c\<sharp>(pi\<bullet>T)" and f4: "c\<sharp>(pi\<bullet>s1)" and f5: "c\<sharp>(pi\<bullet>s2)"
	by (force simp add: fresh_prod fresh_atm)
      have x: "P x (App (Lam [c:T].(([(c,pi\<bullet>a)]@pi)\<bullet>s1)) (pi\<bullet>s2)) ((([(c,pi\<bullet>a)]@pi)\<bullet>s1)[c::=(pi\<bullet>s2)])"
	using a4 f2 by (blast intro!: eqvt_reduce)
      have alpha1: "(Lam [c:T].([(c,pi\<bullet>a)]\<bullet>(pi\<bullet>s1))) = (Lam [(pi\<bullet>a):T].(pi\<bullet>s1))" using f1 f3
	by (simp add: trm.inject alpha)
      have alpha2: "(([(c,pi\<bullet>a)]@pi)\<bullet>s1)[c::=(pi\<bullet>s2)] = (pi\<bullet>s1)[(pi\<bullet>a)::=(pi\<bullet>s2)]"
	using f4 by (simp only: subst_rename[symmetric] pt_name2)
      show "P x (App (Lam [(pi\<bullet>a):T].(pi\<bullet>s1)) (pi\<bullet>s2)) ((pi\<bullet>s1)[(pi\<bullet>a)::=(pi\<bullet>s2)])"
	using x alpha1 alpha2 by (simp only: pt_name2)
    qed
  qed
  hence "P x (([]::name prm)\<bullet>t) (([]::name prm)\<bullet>s)" by blast 
  thus ?thesis by simp
qed

inductive_cases iff_bi_red : "(Iff (Const (BI bi)) thn els) \<hookrightarrow> e"
inductive_cases iff_red : "(Iff tst thn els) \<hookrightarrow> e"


lemma reduce_closed:
  assumes "closed L" and "L \<hookrightarrow> R"
  shows "closed R"
  using `L \<hookrightarrow> R` `closed L`
  proof (induct)
    case (e_beta b t v x) 
    have a:"closed (Abs x b t)" using e_beta closed_def trm.supp by simp
    have b:"closed v" using e_beta closed_def trm.supp by simp
    from a b show ?case using e_beta beta_closed_closed by simp
  next
    case e_if_true thus ?case using closed_def trm.supp by auto
  next
    case e_if_false thus ?case using closed_def trm.supp by auto
  next
    case e_delta thus ?case using delta_closed by auto
  qed


text {* "partial order" (not really) between effects *}

inductive2
  subeff :: "eff \<Rightarrow> eff \<Rightarrow> bool"("\<turnstile> _ <e: _" [60,60] 60)
where
  SE_Refl[intro]: "\<turnstile> F <e: F"
| SE_FF[intro]: "F \<noteq> TT \<Longrightarrow> \<turnstile> FF <e: F"
| SE_TT[intro]: "F \<noteq> FF \<Longrightarrow> \<turnstile> TT <e: F"
| SE_VE[intro]: "\<turnstile> NE <e: VE x"
| SE_TE[intro]: "\<turnstile> NE <e: TE S x"

inductive_cases2 ne_case:"\<turnstile> F1 <e: eff.NE"
inductive_cases2 ne_case_rev:"\<turnstile> eff.NE <e: F1"
inductive_cases2 tt_case:"\<turnstile> F1 <e: eff.TT"
inductive_cases2 tt_case_rev:"\<turnstile> eff.TT <e: F1"
inductive_cases2 ff_case:"\<turnstile> F1 <e: eff.FF"
inductive_cases2 ff_case_rev:"\<turnstile> eff.FF <e: F1"
thm ne_case



lemma no_sub_FF: 
   "\<lbrakk>\<turnstile> T <e: T' ; T' = FF \<rbrakk> \<Longrightarrow> T = FF"
  by (induct rule: subeff.induct) auto

lemma no_sub_TT: 
   "\<lbrakk>\<turnstile> T <e: T' ; T' = TT \<rbrakk> \<Longrightarrow> T = TT"
  by (induct rule: subeff.induct) auto


text{* subtyping *}

inductive2
  subtype :: "ty \<Rightarrow> ty \<Rightarrow> bool" ("\<turnstile> _ <: _" [60,60] 60)
where
  S_Refl[intro]: "\<turnstile> T <: T"
| S_Trans[intro]: "\<lbrakk>\<turnstile> T1 <: T2 ; \<turnstile> T2 <: T3\<rbrakk> \<Longrightarrow> \<turnstile> T1 <: T3"
| S_Fun[intro]: "\<lbrakk>\<turnstile> S1 <: T1 ; \<turnstile> T2 <: S2\<rbrakk> \<Longrightarrow> \<turnstile> (T1 \<rightarrow> T2 : eff) <: (S1 \<rightarrow> S2 : eff)"
| S_Top[intro]: "\<turnstile> T <: Top"

lemma no_sub_int: 
   "\<lbrakk>\<turnstile> T <: T' ; T' = ty.Int \<rbrakk> \<Longrightarrow> T = ty.Int"
  by (induct rule: subtype.induct) auto

lemma no_sub_bool: assumes a:"\<turnstile> T <: T'" and "T' = ty.Bool" shows "T = ty.Bool" 
  using prems
  by (induct rule: subtype.induct) auto

(* type environments *)

types varEnv = "(name*ty) list"

text {* valid contexts *}
inductive2
  valid :: "(name\<times>ty) list \<Rightarrow> bool"
where
    v1[intro]: "valid []"
  | v2[intro]: "\<lbrakk>valid \<Gamma>;a\<sharp>\<Gamma>\<rbrakk>\<Longrightarrow> valid ((a,\<sigma>)#\<Gamma>)"

lemma eqvt_valid[eqvt]:
  fixes   pi:: "name prm"
  assumes a: "valid \<Gamma>"
  shows   "valid (pi\<bullet>\<Gamma>)"
using a
by (induct)
   (auto simp add: fresh_bij)

lemma fresh_context[rule_format]: 
  fixes  \<Gamma> :: "(name\<times>ty)list"
  and    a :: "name"
  assumes a: "a\<sharp>\<Gamma>"
  shows "\<not>(\<exists>\<tau>::ty. (a,\<tau>)\<in>set \<Gamma>)"
using a
apply(induct \<Gamma>)
apply(auto simp add: fresh_prod fresh_list_cons fresh_atm)
done

lemma valid_elim: 
  fixes  \<Gamma> :: "(name\<times>ty)list"
  and    pi:: "name prm"
  and    a :: "name"
  and    \<tau> :: "ty"
  shows "valid ((a,\<tau>)#\<Gamma>) \<Longrightarrow> valid \<Gamma> \<and> a\<sharp>\<Gamma>"
apply(ind_cases2 "valid ((a,\<tau>)#\<Gamma>)", simp)
done

lemma valid_unicity[rule_format]: 
  assumes a: "valid \<Gamma>"
  and     b: "(c,\<sigma>)\<in>set \<Gamma>"
  and     c: "(c,\<tau>)\<in>set \<Gamma>"
  shows "\<sigma>=\<tau>" 
using a b c
apply(induct \<Gamma>)
apply(auto dest!: valid_elim fresh_context)
done

declare fresh_list_cons[simp]
declare fresh_list_nil[simp]

(* environment operations *)

consts 
  env_plus1 :: "eff \<Rightarrow> varEnv => varEnv"
  env_minus1 :: "eff \<Rightarrow> varEnv => varEnv"

(* original type is the SECOND argument *)
constdefs 
  restrict :: "ty \<Rightarrow> ty \<Rightarrow> ty"
  "restrict t1 t2 ==  t1" -- "old if subtype t1 t2 then t1 else t2"
  remove :: "ty \<Rightarrow> ty \<Rightarrow> ty"
  "remove t1 t2 == t2"

fun mapfun :: "(ty \<Rightarrow> ty \<Rightarrow> ty) \<Rightarrow> ty \<Rightarrow> name \<Rightarrow> (name*ty) \<Rightarrow> (name * ty)"
where
mapfun_def: "mapfun f T x (v,S) =  (if (x = v) then (v, f T S) else (v,S))" 


constdefs
 envop :: "(ty \<Rightarrow> ty \<Rightarrow> ty) \<Rightarrow> name \<Rightarrow> ty \<Rightarrow> (name*ty) list \<Rightarrow> (name*ty) list"
envop_def[simp]:"envop f n t G == map (% (v,ty). (if (n = v) then (v,f t ty) else (v,ty))) G"

lemma envop_mapfun:
  shows "map (mapfun f T x) \<Gamma> = envop f x T \<Gamma> " using mapfun_def by auto

lemma envop_fresh:
  fixes v::name
  assumes a:"v \<sharp> \<Gamma>"  and c:"valid \<Gamma>"
  shows "v \<sharp> (envop f n t \<Gamma>)"
  using c a
  proof (induct \<Gamma> rule: valid.induct)
    print_cases
    case v1 thus ?case by auto
  next
    case (v2 \<Gamma>' x ty)
    thus ?case by (cases "n = x") auto
  qed

lemma envop_valid:
  assumes "valid \<Gamma>"
  shows "valid (envop f n t \<Gamma>)"
  using assms
  proof (induct)
    case v1
    have "envop f n t [] = []" by auto
    thus ?case by auto
  next
    case (v2 \<Gamma>' a \<sigma>)
    thus ?case using envop_fresh by (cases "n = a") auto
qed

lemma envop_forget:
  assumes "valid \<Gamma>" and "x \<sharp> \<Gamma>"
  shows "envop f x T \<Gamma> = \<Gamma>"
  using prems
  proof (induct rule: valid.induct)
    case v1 thus ?case by auto
  next
    case (v2 \<Gamma>' a S)
    have "x ~= a" and "x \<sharp> \<Gamma>'" using v2 fresh_list_cons fresh_atm[of x a] by auto
    hence A:"envop f x T ((a,S)#\<Gamma>') = (a,S)# (envop f x T \<Gamma>')" by auto
    thus ?case using v2 `x \<sharp> \<Gamma>'` by auto
  qed
    

nominal_primrec
  "env_plus1 (NE) G = G"
  "env_plus1 (TE T x) G = envop restrict x T G"
  "env_plus1 (VE x) G = G"
  "env_plus1 (TT) G = G"
  "env_plus1 (FF) G = G"
  by auto

nominal_primrec
  "env_minus1 (NE) G = G"
  "env_minus1 (TE T x) G = envop remove x T G"
  "env_minus1 (VE x) G = G"
  "env_minus1 (TT) G = G"
  "env_minus1 (FF) G = G"
  by auto


fun   env_plus :: "varEnv \<Rightarrow> eff \<Rightarrow> varEnv" ("_ |+ _"  [70,70] 70)
where
  [simp]:"(G |+ eff) = env_plus1 eff G"

fun   env_minus :: "varEnv \<Rightarrow> eff \<Rightarrow> varEnv" ("_ |- _"  [70,70] 70)
where
  [simp]: "(G |- eff) = env_minus1 eff G"

lemma ty_eqvt:
  fixes pi::"name prm"
  and T :: ty
  shows "(pi \<bullet> T) = T"
  by auto

--"Induction principle for type envs"
lemma env_induct[case_names Nil Cons]:
  fixes \<Gamma> :: varEnv
  assumes a1:"P []"
  and     a2:"!!G v T. P G \<Longrightarrow> P ((v,T)#G)"
  shows "P \<Gamma>"
  using a1 a2
  by (induct \<Gamma>) auto

lemma envop_eqvt:
  fixes pi::"name prm"
  shows  "envop f (pi\<bullet>n) T (pi\<bullet>\<Gamma>) = (pi\<bullet> (envop f n T \<Gamma>))"
  proof (induct \<Gamma> rule: env_induct)
    case Nil thus ?case by auto
  next
    case (Cons  G v T0) thus ?case using pt_bij4[of pi n v] pt_name_inst at_name_inst by auto
  qed
 
lemma env_plus1_eqvt:
  fixes pi::"name prm"
  shows "env_plus1  (pi\<bullet>eff) (pi\<bullet>\<Gamma>)= pi\<bullet>(env_plus1 eff \<Gamma>)"
  by (nominal_induct eff avoiding: \<Gamma> rule: eff.induct)
   (auto simp add: eff.eqvts envop_eqvt simp del: envop_def)


lemma env_plus_eqvt:
  fixes pi::"name prm"
  shows "(pi\<bullet>\<Gamma>) |+ pi\<bullet>eff = pi\<bullet>(\<Gamma> |+ eff)"
  using env_plus1_eqvt by simp

lemma env_minus1_eqvt:
  fixes pi::"name prm"
  shows "env_minus1  (pi\<bullet>eff) (pi\<bullet>\<Gamma>)= pi\<bullet>(env_minus1 eff \<Gamma>)"
  by (nominal_induct eff avoiding: \<Gamma> rule: eff.induct)
     (auto simp add: eff.eqvts envop_eqvt simp del: envop_def)


lemma env_minus_eqvt:
  fixes pi::"name prm"
  shows "(pi\<bullet>\<Gamma>) |- pi\<bullet>eff = pi\<bullet>(\<Gamma> |- eff)"
  using env_minus1_eqvt by simp

constdefs
  simple_eff :: "eff \<Rightarrow> bool"
  simple_eff_def[simp]:"simple_eff e == e = eff.NE \<or> e = FF \<or> e = TT"

lemma simple_eff_cases[consumes 1, case_names NE FF TT]:
  fixes F::eff
  and P :: "eff \<Rightarrow> bool"
  assumes a:"simple_eff F"
  and a1:"P NE"
  and a2:"P FF"
  and a3:"P TT"
  shows "P F"
  using prems
by (nominal_induct F rule: eff.induct) auto

lemma simple_eff_below_ne:
  assumes "simple_eff F"
  shows "\<turnstile> F <e: NE"
  using prems
by (nominal_induct F rule: eff.induct) auto
  

lemma env_plus_simple_eff:
  assumes "simple_eff eff"
  shows "\<Gamma> |+ eff = \<Gamma>"
  using prems 
  by (induct eff rule: simple_eff_cases) auto
  
lemma env_minus_simple_eff:
  assumes "simple_eff eff"
  shows "\<Gamma> |- eff = \<Gamma>"
  using prems
  by (induct eff rule: simple_eff_cases) auto

text {* type overlap *}

inductive2
  overlap :: "ty \<Rightarrow> ty \<Rightarrow> bool"
where
 overlap_common[intro]: "\<turnstile> S <: T1 \<Longrightarrow> \<turnstile> S <: T2 \<Longrightarrow> overlap T1 T2"

lemma overlap_elim:
  assumes "overlap S T"
  shows "EX U. \<turnstile> U <: S \<and> \<turnstile> U <: T"
  using prems
  by (induct) auto

lemma overlap_of_subtype:
  assumes "overlap S T" and "\<turnstile> S <: S'"
  shows "overlap S' T"
  using prems
  by (induct rule:overlap.induct) auto

lemma overlap_commute:
  assumes "overlap S T" shows "overlap T S"
  using prems
  by induct auto

text {* type judgments *}

inductive2
  typing :: "varEnv \<Rightarrow> trm \<Rightarrow> ty \<Rightarrow> eff \<Rightarrow> bool" (" _ \<turnstile> _ : _ ; _ " [60,60,60,60] 60) 
where
  T_Var[intro]:   "\<lbrakk>valid \<Gamma>; (v,T)\<in>set \<Gamma>\<rbrakk>\<Longrightarrow> \<Gamma> \<turnstile> Var v : T ; VE v" 
| T_Const[intro]: "valid \<Gamma> \<Longrightarrow> \<Delta>\<^isub>\<tau> b = T \<Longrightarrow> \<Gamma> \<turnstile> (BI b) : T ; NE"
| T_Num[intro]: "valid \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> (Num n) : ty.Int ; NE"
| T_True[intro]: "valid \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> (Bool True) : ty.Bool ; TT"
| T_False[intro]: "valid \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> (Bool False) : ty.Bool ; FF"
| T_Abs[intro]:   "\<lbrakk>x \<sharp> \<Gamma>; ((x,T1)#\<Gamma>) \<turnstile> b : T2; eff\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Lam [x:T1].b : (T1\<rightarrow>T2 : latent_eff.NE) ; NE"
| T_App[intro]: "\<lbrakk>\<Gamma> \<turnstile> e1 : (T0 \<rightarrow> T1 : le); eff1; \<Gamma> \<turnstile> e2 : T; eff2 ;  \<turnstile> T <: T0\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> App e1 e2 : T1 ; NE"
| T_AppPred[intro]: "\<lbrakk>\<Gamma> \<turnstile> e1 : (T0 \<rightarrow> T1 : Latent S); eff1; \<Gamma> \<turnstile> e2 : T; VE x ;  \<turnstile> T <: T0\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> App e1 e2 : T1 ; TE S x"
| T_If[intro]: "\<lbrakk>\<Gamma> \<turnstile> e1 : T1; eff1; (\<Gamma> |+ eff1) \<turnstile> e2 : T2; eff2; (\<Gamma> |- eff1) \<turnstile> e3 : T3; eff3; \<turnstile> T2 <: T; \<turnstile> T3 <: T\<rbrakk> \<Longrightarrow>
  \<Gamma> \<turnstile> (Iff e1 e2 e3) : T ; NE"
| T_AppPredTrue[intro]:
  "\<lbrakk>\<Gamma> \<turnstile> e1 : (T0 \<rightarrow> T1 : Latent S); eff1; \<Gamma> \<turnstile> e2 : T; eff2 ;  \<turnstile> T <: T0; \<turnstile> T <: S\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> App e1 e2 : T1 ; TT"
| T_AppPredFalse[intro]:
  "\<lbrakk>\<Gamma> \<turnstile> e1 : (T0 \<rightarrow> T1 : Latent S); eff1; \<Gamma> \<turnstile> e2 : T; eff2 ;  \<turnstile> T <: T0; ~(\<turnstile> T <: S) ; e2 : values ; closed e2\<rbrakk>
  \<Longrightarrow> \<Gamma> \<turnstile> App e1 e2 : T1 ; FF"
| T_IfTrue[intro]: "\<lbrakk>\<Gamma> \<turnstile> e1 : T1 ; TT ; \<Gamma> \<turnstile> e2 : T2 ; eff;  \<turnstile> T2 <: T\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (Iff e1 e2 e3) : T ; NE" 
| T_IfFalse[intro]: "\<lbrakk>\<Gamma> \<turnstile> e1 : T1 ; FF ; \<Gamma> \<turnstile> e3 : T3 ; eff;  \<turnstile> T3 <: T\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (Iff e1 e2 e3) : T ; NE" 


(* general lemmas about typing *)

lemma eqvt_typing: 
  fixes  \<Gamma> :: "(name\<times>ty) list"
  and    t :: "trm"
  and    f :: eff
  and    \<tau> :: "ty"
  and    pi:: "name prm"
  assumes a: "\<Gamma> \<turnstile> t : \<tau> ; f"
  shows "(pi\<bullet>\<Gamma>) \<turnstile> (pi\<bullet>t) : \<tau> ; (pi\<bullet>f)"
using a
proof (induct)
  case (T_Var \<Gamma> a \<tau>)
  have "valid (pi\<bullet>\<Gamma>)" by (rule eqvt_valid)
  moreover
  have "(pi\<bullet>(a,\<tau>))\<in>((pi::name prm)\<bullet>set \<Gamma>)" by (rule pt_set_bij2[OF pt_name_inst, OF at_name_inst])
  ultimately show ?case
    using typing.T_Var by (force simp add: pt_list_set_pi[OF pt_name_inst, symmetric])
next 
  case (T_Abs a \<Gamma> T t \<sigma> eff)
  moreover have "(pi\<bullet>a)\<sharp>(pi\<bullet>\<Gamma>)" by (simp add: fresh_bij)
  ultimately show ?case by force
next
  case T_If thus ?case by (auto simp add: env_plus1_eqvt env_minus1_eqvt)
qed (auto simp add: eqvt_valid values_eqvt closed_eqvt )


text {* nominal induction for typing - only needed for weakening! *}

lemma typing_induct[consumes 1, case_names T_Var T_Const T_Num T_True T_False T_App T_Lam T_AppPred T_If 
  T_AppPredTrue T_AppPredFalse T_IfTrue T_IfFalse]:
  fixes  P :: "'a::fs_name\<Rightarrow>(name\<times>ty) list \<Rightarrow> trm \<Rightarrow> ty \<Rightarrow> eff \<Rightarrow> bool"
  and    \<Gamma> :: "(name\<times>ty) list"
  and    t :: "trm"
  and    T :: "ty"
  and    F :: "eff"
  and    x :: "'a::fs_name"
  assumes a: "\<Gamma> \<turnstile> t : T ; F"
  and a1:    "\<And>\<Gamma> (a::name) \<tau> x. valid \<Gamma> \<Longrightarrow> (a,\<tau>) \<in> set \<Gamma> \<Longrightarrow> P x \<Gamma> (Var a) \<tau> (VE a)"
  and a2:    "!! \<Gamma> b T x. valid \<Gamma> \<Longrightarrow> \<Delta>\<^isub>\<tau> b = T \<Longrightarrow> P x \<Gamma> (BI b) T NE"
  and a3:    "!! \<Gamma> n x. valid \<Gamma> \<Longrightarrow> P x \<Gamma> (Num n) ty.Int NE"
  and a4:    "!! \<Gamma> x. valid \<Gamma> \<Longrightarrow> P x \<Gamma> (Bool True) ty.Bool TT"
  and a5:    "!! \<Gamma> x. valid \<Gamma> \<Longrightarrow> P x \<Gamma> (Bool False) ty.Bool FF"
  and a6:    "\<And>\<Gamma> \<tau> \<sigma> t1 t2 x F1 F2 le \<tau>0. 
              \<Gamma> \<turnstile> t1 : \<tau>\<rightarrow>\<sigma>:le ; F1 \<Longrightarrow> (\<And>z. P z \<Gamma> t1 (\<tau>\<rightarrow>\<sigma>:le) F1) \<Longrightarrow> \<Gamma> \<turnstile> t2 : \<tau>0 ; F2 \<Longrightarrow> (\<And>z. P z \<Gamma> t2 \<tau>0 F2) \<Longrightarrow> \<turnstile> \<tau>0 <: \<tau>
              \<Longrightarrow> P x \<Gamma> (App t1 t2) \<sigma> NE"
  and a7:    "\<And>a \<Gamma> \<tau> \<sigma> t x F0. a\<sharp>x \<Longrightarrow> a\<sharp>\<Gamma> \<Longrightarrow> ((a,\<tau>) # \<Gamma>) \<turnstile> t : \<sigma> ; F0 \<Longrightarrow> (\<And>z. P z ((a,\<tau>)#\<Gamma>) t \<sigma> F0)
              \<Longrightarrow> P x \<Gamma> (Lam [a:\<tau>].t) (\<tau>\<rightarrow>\<sigma>:latent_eff.NE) NE"
  and a8:    "\<And>\<Gamma> \<tau> \<sigma> t1 t2 x F1 \<tau>0 S v. 
              \<Gamma> \<turnstile> t1 : \<tau>\<rightarrow>\<sigma>:Latent S ; F1 \<Longrightarrow> (\<And>z. P z \<Gamma> t1 (\<tau>\<rightarrow>\<sigma>:Latent S) F1) \<Longrightarrow> \<Gamma> \<turnstile> t2 : \<tau>0 ; VE v \<Longrightarrow> (\<And>z. P z \<Gamma> t2 \<tau>0 (VE v)) 
              \<Longrightarrow> \<turnstile> \<tau>0 <: \<tau>  \<Longrightarrow> P x \<Gamma> (App t1 t2) \<sigma> (TE S v)"
  and a9:    "!! \<Gamma> e1 e2 e3 T1 T2 T3 T eff1 eff2 eff3 x. 
                 \<lbrakk>\<Gamma> \<turnstile> e1 : T1; eff1; !!z. P z \<Gamma> e1 T1 eff1; (\<Gamma> |+ eff1) \<turnstile> e2 : T2; eff2; !!z. P z (\<Gamma>|+ eff1) e2 T2 eff2; 
                 (\<Gamma> |- eff1) \<turnstile> e3 : T3; eff3; !!z. P z (\<Gamma>|- eff1) e3 T3 eff3; \<turnstile> T2 <: T; \<turnstile> T3 <: T\<rbrakk>
                 \<Longrightarrow> P x \<Gamma> (Iff e1 e2 e3) T NE"
  and a10:   "!! \<Gamma> e1 e2 T0 T1 T S eff1 eff2 x. \<lbrakk>\<Gamma> \<turnstile> e1 : (T0 \<rightarrow> T1 : Latent S); eff1; !!z. P z \<Gamma> e1 (T0 \<rightarrow> T1 : Latent S) eff1;
              \<Gamma> \<turnstile> e2 : T; eff2 ;  !! z. P z \<Gamma> e2 T eff2; \<turnstile> T <: T0; \<turnstile> T <: S\<rbrakk> \<Longrightarrow> P x \<Gamma> (App e1 e2) T1 TT"
  and a11:   "!! \<Gamma> e1 e2 T0 T1 T S eff1 eff2 x. \<lbrakk>\<Gamma> \<turnstile> e1 : (T0 \<rightarrow> T1 : Latent S); eff1; !!z. P z \<Gamma> e1 (T0 \<rightarrow> T1 : Latent S) eff1;
              \<Gamma> \<turnstile> e2 : T; eff2 ;  !! z. P z \<Gamma> e2 T eff2; \<turnstile> T <: T0; ~(\<turnstile> T <: S) ; e2 : values; closed e2\<rbrakk>
  \<Longrightarrow> P x \<Gamma> (App e1 e2) T1 FF"
  and a12:   "!! \<Gamma> e1 e2 e3 T T1 T2 eff x. \<lbrakk>\<Gamma> \<turnstile> e1 : T1 ; TT ; !! z. P z \<Gamma> e1 T1 TT; 
               \<Gamma> \<turnstile> e2 : T2 ; eff;  !!z .P z \<Gamma> e2 T2 eff; \<turnstile> T2 <: T\<rbrakk> \<Longrightarrow> P x \<Gamma> (Iff e1 e2 e3) T NE"
  and a13:   "!! \<Gamma> e1 e2 e3 T T1 T3 eff x. \<lbrakk>\<Gamma> \<turnstile> e1 : T1 ; FF ; !! z. P z \<Gamma> e1 T1 FF; 
               \<Gamma> \<turnstile> e3 : T3 ; eff;  !!z .P z \<Gamma> e3 T3 eff; \<turnstile> T3 <: T\<rbrakk> \<Longrightarrow> P x \<Gamma> (Iff e1 e2 e3) T NE"
  shows "P x \<Gamma> t T F"
  proof -
    from a have "\<And>(pi::name prm) x. P x (pi\<bullet>\<Gamma>) (pi\<bullet>t) T (pi\<bullet>F)"
    proof (induct)
      case (T_Const b T) thus ?case using a2 perm_builtin eqvt_valid by auto
    next
      case T_Num thus ?case using a3 eqvt_valid by auto
    next
      case T_True thus ?case using a4 eqvt_valid by auto
    next
      case T_False thus ?case using a5 eqvt_valid by auto
    next
      case (T_App \<Gamma> e1 T0 T1 le F1 e2 T F2) thus  ?case using a6
        by simp (blast intro: eqvt_typing)
    next
      case T_AppPredTrue thus  ?case using a10
        by simp (blast intro: eqvt_typing)
    next
      case T_AppPredFalse thus  ?case using a11
        by simp (blast intro: eqvt_typing values_eqvt closed_eqvt)
    next
      case (T_If \<Gamma> e1 T1 eff1 e2 T2 eff2 e3 T3 eff3 T)
	have A:" pi \<bullet> \<Gamma> \<turnstile> pi \<bullet> e1 : T1 ; pi \<bullet> eff1" using T_If eqvt_typing by auto
	have B:" pi \<bullet> (\<Gamma> |+ eff1) \<turnstile> pi \<bullet> e2 : T2 ; pi \<bullet> eff2" using T_If eqvt_typing by auto
	have C:" pi \<bullet> (\<Gamma> |- eff1) \<turnstile> pi \<bullet> e3 : T3 ; pi \<bullet> eff3" using T_If eqvt_typing by auto
	from B have B': " (pi \<bullet> \<Gamma>) |+ (pi \<bullet> eff1) \<turnstile> pi \<bullet> e2 : T2 ; pi \<bullet> eff2" using T_If env_plus_eqvt by auto
	from C have C': " (pi \<bullet> \<Gamma>) |- (pi \<bullet> eff1) \<turnstile> pi \<bullet> e3 : T3 ; pi \<bullet> eff3" using T_If env_minus_eqvt by auto
	have D:"!! x. P x (pi \<bullet> \<Gamma>) (pi \<bullet> e1) T1 (pi \<bullet> eff1)" .
	have E:"!! x. P x ((pi \<bullet> \<Gamma>) |+ (pi \<bullet> eff1)) (pi \<bullet> e2) T2 (pi \<bullet> eff2)" using env_plus_eqvt T_If by auto
	have F:"!! x. P x ((pi \<bullet> \<Gamma>) |- (pi \<bullet> eff1)) (pi \<bullet> e3) T3 (pi \<bullet> eff3)" using env_minus_eqvt T_If by auto	
	show  ?case using a9 A B' C' D E F T_If by auto
    next
      case (T_IfTrue \<Gamma> e1 T1 e2 T2 eff2 T e3) 
      have A:" pi \<bullet> \<Gamma> \<turnstile> pi \<bullet> e1 : T1 ; pi \<bullet> TT" using T_IfTrue eqvt_typing[of \<Gamma> e1 T1 TT] by auto
      have B:" pi \<bullet> \<Gamma> \<turnstile> pi \<bullet> e2 : T2 ; pi \<bullet> eff2" using T_IfTrue eqvt_typing[of \<Gamma> e2 T2] by auto
      show ?case using A B  T_IfTrue(2)[of _ pi] T_IfTrue(4)[of _ pi] `\<turnstile> T2 <: T` a12 by auto
    next
      case (T_IfFalse \<Gamma> e1 T1 e3 T3 eff3 T e2)
      have A:" pi \<bullet> \<Gamma> \<turnstile> pi \<bullet> e1 : T1 ; pi \<bullet> FF" using T_IfFalse eqvt_typing[of \<Gamma> e1 T1 FF] by auto
      have B:" pi \<bullet> \<Gamma> \<turnstile> pi \<bullet> e3 : T3 ; pi \<bullet> eff3" using T_IfFalse eqvt_typing[of \<Gamma> e3 T3] by auto
      show ?case using A B  T_IfFalse(2)[of _ pi] T_IfFalse(4)[of _ pi] `\<turnstile> T3 <: T` a13 by auto
    next
      case (T_AppPred \<Gamma> e1 T0 T1 S eff1 e2 T v) 
      have A:" pi \<bullet> \<Gamma> \<turnstile> pi \<bullet> e1 : T0 \<rightarrow> T1 : Latent S ; pi \<bullet> eff1" using T_AppPred eqvt_typing[of \<Gamma> e1 _ eff1] by auto
      have B:" pi \<bullet> \<Gamma> \<turnstile> pi \<bullet> e2 : T ; pi \<bullet> (VE v)" using T_AppPred eqvt_typing[of \<Gamma> e2 T "VE v"] by auto
      show ?case using A B T_AppPred a8 by auto
    next
      case (T_Var \<Gamma> a T)	
      have j1: "valid \<Gamma>" by fact
      have j2: "(a,T)\<in>set \<Gamma>" by fact
      from j1 have j3: "valid (pi\<bullet>\<Gamma>)" by (rule eqvt_valid)
      from j2 have "pi\<bullet>(a,T)\<in>pi\<bullet>(set \<Gamma>)" by (simp only: pt_set_bij[OF pt_name_inst, OF at_name_inst])  
      hence j4: "(pi\<bullet>a,T)\<in>set (pi\<bullet>\<Gamma>)" by (simp add: pt_list_set_pi[OF pt_name_inst])
      show "P x (pi\<bullet>\<Gamma>) (pi\<bullet>(Var a)) T (pi\<bullet> VE a) " using a1 j3 j4 by simp
    next
      case (T_Abs a \<Gamma> \<tau> t \<sigma> F)
      have k1: "a\<sharp>\<Gamma>" by fact
      have k2: "((a,\<tau>)#\<Gamma>)\<turnstile>t:\<sigma>;F" by fact
      have k3: "\<And>(pi::name prm) (x::'a::fs_name). P x (pi \<bullet>((a,\<tau>)#\<Gamma>)) (pi\<bullet>t) \<sigma> (pi\<bullet>F)" by fact
      have f: "\<exists>c::name. c\<sharp>(pi\<bullet>a,pi\<bullet>t,pi\<bullet>\<Gamma>,x,pi\<bullet>F)"
	by (rule exists_fresh', simp add: fs_name1)
      then obtain c::"name" 
	where f1: "c\<noteq>(pi\<bullet>a)" and f2: "c\<sharp>x" and f3: "c\<sharp>(pi\<bullet>t)" and f4: "c\<sharp>(pi\<bullet>\<Gamma>)" and f5: "c\<sharp>(pi\<bullet>F)"
	by (force simp add: fresh_prod at_fresh[OF at_name_inst])
      from k1 have k1a: "(pi\<bullet>a)\<sharp>(pi\<bullet>\<Gamma>)" 
	by (simp add: pt_fresh_left[OF pt_name_inst, OF at_name_inst] 
          pt_rev_pi[OF pt_name_inst, OF at_name_inst])
      have l1: "(([(c,pi\<bullet>a)]@pi)\<bullet>\<Gamma>) = (pi\<bullet>\<Gamma>)" using f4 k1a 
	by (simp only: pt2[OF pt_name_inst], rule pt_fresh_fresh[OF pt_name_inst, OF at_name_inst])
      have "\<And>x. P x (([(c,pi\<bullet>a)]@pi)\<bullet>((a,\<tau>)#\<Gamma>)) (([(c,pi\<bullet>a)]@pi)\<bullet>t) \<sigma> (([(c,pi\<bullet>a)]@pi)\<bullet>F)" using k3 by force
      hence l2: "\<And>x. P x ((c, \<tau>)#(pi\<bullet>\<Gamma>)) (([(c,pi\<bullet>a)]@pi)\<bullet>t) \<sigma> (([(c,pi\<bullet>a)]@pi)\<bullet>F)" using f1 l1
	by (force simp add: pt2[OF pt_name_inst]  at_calc[OF at_name_inst])
      have "(([(c,pi\<bullet>a)]@pi)\<bullet>((a,\<tau>)#\<Gamma>)) \<turnstile> (([(c,pi\<bullet>a)]@pi)\<bullet>t) : \<sigma> ; (([(c,pi\<bullet>a)]@pi)\<bullet>F)" using k2 by (rule eqvt_typing)
      hence l3: "((c, \<tau>)#(pi\<bullet>\<Gamma>)) \<turnstile> (([(c,pi\<bullet>a)]@pi)\<bullet>t) : \<sigma> ; (([(c,pi\<bullet>a)]@pi)\<bullet>F)" using l1 f1 
	by (force simp add: pt2[OF pt_name_inst]  at_calc[OF at_name_inst])
      have l4: "P x (pi\<bullet>\<Gamma>) (Lam [c:\<tau>].(([(c,pi\<bullet>a)]@pi)\<bullet>t)) (\<tau> \<rightarrow> \<sigma> : latent_eff.NE) eff.NE" using f2 f4 f5 l2 l3 l1
	a7[of c x "pi \<bullet> \<Gamma>" \<tau> "(([(c, pi \<bullet> a)] @ pi) \<bullet> t) " \<sigma>] by auto
      have alpha: "(Lam [c:\<tau>].([(c,pi\<bullet>a)]\<bullet>(pi\<bullet>t))) = (Lam [(pi\<bullet>a):\<tau>].(pi\<bullet>t))" using f1 f3
	by (simp add: trm.inject alpha)
      show "P x (pi\<bullet>\<Gamma>) (pi\<bullet>(Lam [a:\<tau>].t)) (\<tau> \<rightarrow> \<sigma> : latent_eff.NE) (pi\<bullet>eff.NE)" using l4 alpha 
	by (simp only: pt2[OF pt_name_inst], simp)
    qed
  hence "P x (([]::name prm)\<bullet>\<Gamma>) (([]::name prm)\<bullet>t) T (([]::name prm)\<bullet>F)" by blast
  thus "P x \<Gamma> t T F" by simp
qed


(* typing example *)

text {* then we begin on preservation *}

abbreviation
  "sub" :: "(name\<times>ty) list \<Rightarrow> (name\<times>ty) list \<Rightarrow> bool" (" _ \<lless> _ " [80,80] 80) where
  "\<Gamma>1 \<lless> \<Gamma>2 \<equiv> \<forall>a \<sigma>. (a,\<sigma>)\<in>set \<Gamma>1 \<longrightarrow>  (a,\<sigma>)\<in>set \<Gamma>2"

lemma envplus_empty:
  shows "env_plus1 eff [] = []"
  by (nominal_induct rule: eff.induct) auto
lemma envminus_empty:
  shows "env_minus1 eff [] = []"
  by (nominal_induct rule: eff.induct) auto

lemma weaking_envplus: 
  assumes "\<Gamma> \<lless> \<Gamma>'" and a:"valid \<Gamma>'"
  shows "env_plus1 eff \<Gamma> \<lless> env_plus1 eff \<Gamma>'"
  using a prems
  proof (nominal_induct eff avoiding: \<Gamma> \<Gamma>' rule: eff.induct)
    case (TE S x \<Gamma>1 \<Gamma>2)
    let ?op = "restrict"
    let ?mapfun = "(% (v,ty). (if (x = v) then (v,?op S ty) else (v,ty)))"
    have "env_plus1 (TE S x) \<Gamma>1 = envop ?op x S \<Gamma>1" by auto
    hence A:"env_plus1 (TE S x) \<Gamma>1 = map ?mapfun \<Gamma>1" by auto
    have "env_plus1 (TE S x) \<Gamma>2 = envop ?op x S \<Gamma>2" by auto
    hence B:"env_plus1 (TE S x) \<Gamma>2 = map ?mapfun \<Gamma>2" by auto
    have "set \<Gamma>1 <= set \<Gamma>2" using TE by auto
    hence "?mapfun ` (set \<Gamma>1) <= ?mapfun ` (set \<Gamma>2)" by blast
    hence "set (map ?mapfun \<Gamma>1) <= set (map ?mapfun \<Gamma>2)" by auto
    hence "(map ?mapfun \<Gamma>1) \<lless> (map ?mapfun \<Gamma>2)" by blast
    thus ?case using A B by auto
  qed (auto)


lemma "(a:: 'a set) <= b \<Longrightarrow> f`a <= f`b "
  by blast

lemma weaking_envminus: 
  assumes "\<Gamma> \<lless> \<Gamma>'" and a:"valid \<Gamma>'" and b:"valid \<Gamma>"
  shows "env_minus1 eff \<Gamma> \<lless> env_minus1 eff \<Gamma>'"
  using a prems
  proof (nominal_induct eff avoiding: \<Gamma> \<Gamma>' rule: eff.induct)
    case (TE S x \<Gamma>1 \<Gamma>2)
    let ?op = "remove"
    let ?mapfun = "(% (v,ty). (if (x = v) then (v,?op S ty) else (v,ty)))"
    have "env_minus1 (TE S x) \<Gamma>1 = envop ?op x S \<Gamma>1" by auto
    hence A:"env_minus1 (TE S x) \<Gamma>1 = map ?mapfun \<Gamma>1" by auto
    have "env_minus1 (TE S x) \<Gamma>2 = envop ?op x S \<Gamma>2" by auto
    hence B:"env_minus1 (TE S x) \<Gamma>2 = map ?mapfun \<Gamma>2" by auto
    have "set \<Gamma>1 <= set \<Gamma>2" using TE by auto
    hence "?mapfun ` (set \<Gamma>1) <= ?mapfun ` (set \<Gamma>2)" by blast
    hence "set (map ?mapfun \<Gamma>1) <= set (map ?mapfun \<Gamma>2)" by auto
    hence "(map ?mapfun \<Gamma>1) \<lless> (map ?mapfun \<Gamma>2)" by blast
    thus ?case using A B by auto
  qed (auto)

lemma envplus_valid:
  assumes "valid \<Gamma>"
  shows "valid (\<Gamma> |+ F)"
  using prems
proof (induct rule: valid.induct)
  case v1 thus ?case using envplus_empty by auto
next
  case (v2 \<Gamma>' a T) thus ?case
    proof (nominal_induct rule: eff.induct)
      case (TE S x)
        let ?op = "restrict"
        let ?G = "((a, T) # \<Gamma>')"
        let ?mapfun = "(% (v,ty). (if (x = v) then (v,?op S ty) else (v,ty)))"
        have "?G |+ TE S x = envop ?op x S ?G" by auto
        hence A:"?G |+ TE S x = map ?mapfun ?G" by auto
        thus ?case using TE v2
          proof (cases "a = x")
            case False
            hence B:"?G |+ TE S x = ((a,T)# (map ?mapfun \<Gamma>'))" by auto
            have C:"valid (map ?mapfun \<Gamma>')" using v2 TE A by auto
            have "map ?mapfun \<Gamma>' = \<Gamma>' |+ TE S x" by auto
            hence "map ?mapfun \<Gamma>' = envop ?op x S \<Gamma>'" by auto
            hence D:"a \<sharp> (map ?mapfun \<Gamma>')" using C TE v2 envop_fresh by auto
            hence E:"valid ((a,T)# (map ?mapfun \<Gamma>'))" using C by auto
            thus ?thesis using B by auto
          next
            case True
            hence B:"?G |+ TE S x = ((a,?op S T)# (map ?mapfun \<Gamma>'))" by auto
            have C:"valid (map ?mapfun \<Gamma>')" using v2 TE A by auto
            have "map ?mapfun \<Gamma>' = \<Gamma>' |+ TE S x" by auto
            hence "map ?mapfun \<Gamma>' = envop ?op x S \<Gamma>'" by auto
            hence D:"a \<sharp> (map ?mapfun \<Gamma>')" using C TE v2 envop_fresh by auto
            hence E:"valid ((a,?op S T)# (map ?mapfun \<Gamma>'))" using C by auto
            thus ?thesis using B by auto
          qed
        qed (auto)
      qed

lemma envminus_valid:
  assumes "valid \<Gamma>"
  shows "valid (\<Gamma> |- F)"
  using prems 
proof (induct rule: valid.induct)
  case v1 thus ?case using envminus_empty by auto
next
  case (v2 \<Gamma>' a T) thus ?case
    proof (nominal_induct rule: eff.induct)
      case (TE S x)
        let ?op = "remove"
        let ?G = "((a, T) # \<Gamma>')"
        let ?mapfun = "(% (v,ty). (if (x = v) then (v,?op S ty) else (v,ty)))"
        have "?G |- TE S x = envop ?op x S ?G" by auto
        hence A:"?G |- TE S x = map ?mapfun ?G" by auto
        thus ?case using TE v2
          proof (cases "a = x")
            case False
            hence B:"?G |- TE S x = ((a,T)# (map ?mapfun \<Gamma>'))" by auto
            have C:"valid (map ?mapfun \<Gamma>')" using v2 TE A by auto
            have "map ?mapfun \<Gamma>' = \<Gamma>' |- TE S x" by auto
            hence "map ?mapfun \<Gamma>' = envop ?op x S \<Gamma>'" by auto
            hence D:"a \<sharp> (map ?mapfun \<Gamma>')" using C TE v2 envop_fresh by auto
            hence E:"valid ((a,T)# (map ?mapfun \<Gamma>'))" using C by auto
            thus ?thesis using B by auto
          next
            case True
            hence B:"?G |- TE S x = ((a,?op S T)# (map ?mapfun \<Gamma>'))" by auto
            have C:"valid (map ?mapfun \<Gamma>')" using v2 TE A by auto
            have "map ?mapfun \<Gamma>' = \<Gamma>' |- TE S x" by auto
            hence "map ?mapfun \<Gamma>' = envop ?op x S \<Gamma>'" by auto
            hence D:"a \<sharp> (map ?mapfun \<Gamma>')" using C TE v2 envop_fresh by auto
            hence E:"valid ((a,?op S T)# (map ?mapfun \<Gamma>'))" using C by auto
            thus ?thesis using B by auto
          qed
        qed (auto)
      qed

lemma weakening: 
  assumes a: "\<Gamma>1 \<turnstile> t : \<sigma> ; F" 
  and     b: "valid \<Gamma>2" 
  and     c: "\<Gamma>1 \<lless> \<Gamma>2"
  and d:"valid \<Gamma>1"
  shows "\<Gamma>2 \<turnstile> t:\<sigma> ; F"
using a b c d
proof (nominal_induct \<Gamma>1 t \<sigma> F avoiding: \<Gamma>2 rule: typing_induct)
  case (T_If \<Gamma> t1 t2 t3 T1 T2 T3 T F1 F2 F3 \<Gamma>2)
    have A:"valid (\<Gamma> |+ F1)" using T_If envplus_valid by auto
    have B:"valid (\<Gamma> |- F1)" using T_If envminus_valid by auto
    have A':"valid (\<Gamma>2 |+ F1)" using T_If envplus_valid by auto
    have B':"valid (\<Gamma>2 |- F1)" using T_If envminus_valid by auto
    have C:"(\<Gamma> |+ F1) \<lless> (\<Gamma>2 |+ F1)" using T_If weaking_envplus by auto
    have D:"(\<Gamma> |- F1) \<lless> (\<Gamma>2 |- F1)" using T_If weaking_envminus by auto
    show ?case using T_If A B C D A' B' by blast
qed (auto | atomize)+ 
(* FIXME: before using meta-connectives and the new induction *)
(* method, this was completely automatic *)
(* need weaking lemmas about env+/- *)


lemma eff_parts_typing:
  assumes "\<Gamma> \<turnstile> e : T ; F" and "!! a S. (a,S) : set \<Gamma> \<Longrightarrow> eff_parts S <= {ty.Int, ty.Bool}"
  shows "eff_parts T <= {ty.Int, ty.Bool}"
  using prems
  proof (induct rule: typing.induct)
    case (T_Var \<Gamma> v T') thus ?case by auto
  next
    case (T_Abs x b T) oops


lemma "[] \<turnstile> (Lam[x:Top]. (Iff (App (BI NumberP) (Var x)) (App (BI Add1) (Var x)) (Num 12))) : (Top \<rightarrow> ty.Int : latent_eff.NE) ; NE"
  apply (rule T_Abs)
  apply (auto simp add: fresh_def   supp_def perm_fun_def)

  apply (rule T_If)
  apply auto
  apply (rule T_AppPred)
  apply (auto simp add: valid.intros)
  apply (rule T_App)
  apply (auto simp add: restrict_def valid.intros)
  done


(* inductive cases about typing *)

inductive_cases2 iff_t_cases : "G \<turnstile> Iff tst thn els : t ; e"
inductive_cases2 app_bi_cases : "G \<turnstile> App (Const (BI b)) rand : t ; e"
inductive_cases2 type_arr_case_num: "\<Gamma> \<turnstile> ((Num n)) : (T1 \<rightarrow> T2 : eff) ; eff'"
inductive_cases2 type_arr_case_bool: "\<Gamma> \<turnstile> ((Bool b)) : (T1 \<rightarrow> T2 : eff) ; eff'"
inductive_cases2 type_bi_case: "\<Gamma> \<turnstile> ((BI b)) : t ; eff"
inductive_cases2 type_add1_case: "\<Gamma> \<turnstile> ((BI Add1)) : t ; eff"
inductive_cases2 bi_typing_cases: "\<Gamma> \<turnstile> (BI b) : t ; eff"
inductive_cases2 abs_ty_int: "\<Gamma> \<turnstile> (Abs x body t) : ty.Int ; eff'"
inductive_cases2 abs_ty_bool: "\<Gamma> \<turnstile> (Abs x body t) : ty.Bool ; eff'"
inductive_cases2 const_ty_int: "\<Gamma> \<turnstile> e : ty.Int ; eff'"
inductive_cases2 const_ty_bool: "\<Gamma> \<turnstile> e : ty.Bool ; eff'"
inductive_cases2 iff_false_ty: "\<Gamma> \<turnstile> Iff (Bool False) thn els : t ; eff"
inductive_cases2 app_bi_ty: "\<Gamma> \<turnstile> App (BI b) arg : t ; eff"

(* Typing Values*)

lemma value_int_ty:
  assumes a:"\<Gamma> \<turnstile> e : ty.Int ; eff"
  and b: "e : values"
  shows "EX n. e = (Num n)"
  using b a
proof (induct rule: values.induct)
  case (abs_value body ty x)
  thus ?case using abs_ty_int[of \<Gamma> x body ty eff] by auto 
next
  case (num_value c) thus ?case by auto
next
  case (bool_value bb)
  thus ?case
    using const_ty_int[of \<Gamma> "(Bool bb)" eff] by (auto simp add: trm.inject)
next
  case (bi_value bb)
  thus ?case
    using const_ty_int[of \<Gamma> "BI bb" eff]
    by (nominal_induct bb rule: builtin.induct)
       (auto simp add: trm.inject)
qed


lemma value_bool_ty:
  assumes a:"\<Gamma> \<turnstile> e : ty.Bool ; eff"
  and b: "e : values"
  shows "EX b. e = (Bool b)"
  using b a
proof (induct rule: values.induct)
  case (abs_value body ty x)
  thus ?case using abs_ty_bool[of \<Gamma> x body ty eff] by auto 
next
  case (bool_value bb) thus ?case by auto
next
  case (num_value nn)
  thus ?case
    using const_ty_bool[of \<Gamma> "(Num nn)" eff] by (auto simp add: trm.inject)
next
  case (bi_value bb)
  thus ?case
    using const_ty_bool[of \<Gamma> "BI bb" eff]
    by (nominal_induct bb rule: builtin.induct)
       (auto simp add: trm.inject)
qed


lemma typing_bi:
  assumes a:"\<Gamma> \<turnstile> (BI b) : t ; eff"
  shows "t = \<Delta>\<^isub>\<tau> b"
  using a bi_typing_cases[of \<Gamma> b t eff "t = \<Delta>\<^isub>\<tau> b"]
  by (simp add: trm.inject)  

lemma typed_prim_reduce:
  assumes a:"\<Gamma> \<turnstile> (BI b) : T0 \<rightarrow> T1 : le ; eff" and b:"\<Gamma> \<turnstile> v : T ; eff'" and c:"v : values"
  and sub:"\<turnstile> T <: T0"
  shows "EX v'. \<Delta> b v = Some v'"
  using a b c sub
  proof (nominal_induct b rule: builtin.induct)
    case Add1
    have "(T0 \<rightarrow> T1 : le) = \<Delta>\<^isub>\<tau> Add1" using Add1 typing_bi[of \<Gamma> Add1 "(T0 \<rightarrow> T1 : le)" eff] by simp
    hence "T0 = ty.Int" and "T1 = ty.Int" and "le = latent_eff.NE" by (auto simp add: ty.inject)
    hence "T = ty.Int" using sub no_sub_int by simp
    have "EX n. v = (Num n)" using c b `T = ty.Int` value_int_ty by auto
    then obtain n where "v = (Num n)" by auto
    thus ?case by (auto simp add: \<Delta>.simps)
  next
    case Nott
    have "(T0 \<rightarrow> T1 : le) = \<Delta>\<^isub>\<tau> Nott" using Nott typing_bi[of \<Gamma> Nott "(T0 \<rightarrow> T1 : le)" eff] by simp
    hence "T0 = ty.Bool" and "T1 = ty.Bool" and "le = latent_eff.NE" by (auto simp add: ty.inject)
    hence "T = ty.Bool" using sub no_sub_bool by simp
    have "EX b. v = (Bool b)" using c b `T = ty.Bool` value_bool_ty by auto
    then obtain b where "v = (Bool b)" by auto
    thus ?case by (auto simp add: \<Delta>.simps)
  next
    case NumberP thus ?case by auto
  next
    case BooleanP thus ?case by auto
  qed


text {* Progress together with necessary lemmas *}

(* first some lemmas about decomposing various kinds of syntax *)

lemma if_decomp:
  assumes b:"closed tst \<Longrightarrow> (\<exists>E L R. tst = E L \<and> E \<in> ctxt \<and> L \<hookrightarrow> R) \<or> tst \<in> values"
  and c:"closed (Iff tst thn els)"
  shows "(EX E L R. (Iff tst thn els) = E L \<and> E : ctxt \<and> L \<hookrightarrow> R) \<or> (Iff tst thn els) : values"
  proof -
    {
      assume "tst : values"
      hence "EX E L R. Iff tst thn els = E L \<and> E : ctxt \<and> (L \<hookrightarrow> R)"
        using if_val_reduces[of tst thn els] ex_help[of "Iff tst thn els" "(%t. t)"] by auto
    }
    moreover
    {
      assume asm:"tst \<notin> values"
      have cl:"closed tst" using `closed (Iff tst thn els)` by (auto simp add: closed_def trm.supp)
      hence ih:"\<exists>E t t'. tst = E t \<and> E \<in> ctxt \<and> t \<hookrightarrow> t'" using b asm by auto
      hence "\<exists>E t t' . Iff tst thn els = E t \<and> E \<in> ctxt \<and> t \<hookrightarrow> t'"
        using reduce_in_ctxt[of "(%t . (Iff t thn els))"] ih by auto
    }
    ultimately show ?thesis by auto
  qed
  



lemma app_decomp:
  assumes a:" G \<turnstile> rator : T0 \<rightarrow> T1 : le ; eff1"
  and aa:" G \<turnstile> rand : T ; eff"
  and b:"closed rator \<Longrightarrow> (\<exists>E L R. rator = E L \<and> E \<in> ctxt \<and> L \<hookrightarrow> R) \<or> rator \<in> values"
  and bb:"closed rand \<Longrightarrow> (\<exists>E L R. rand = E L \<and> E \<in> ctxt \<and> L \<hookrightarrow> R) \<or> rand \<in> values"
  and c:"closed (App rator rand)"
  and sub:"\<turnstile> T <: T0"
  shows "(EX E L R. (App rator rand) = E L \<and> E : ctxt \<and> L \<hookrightarrow> R) \<or> (App rator rand) : values"
  proof -
    have well_typed:"G \<turnstile> (App rator rand) : T1 ; eff.NE" using T_App[of G rator T0 T1 le eff1 rand T eff] a aa sub by auto
    have "closed rator" using c by (auto simp add: closed_def trm.supp)
    hence ih1:"(\<exists>E L R. rator = E L \<and> E \<in> ctxt \<and> L \<hookrightarrow> R) \<or> rator \<in> values" using b by simp
    have "closed rand" using c by (auto simp add: closed_def trm.supp)
    hence ih2:"(\<exists>E L R. rand = E L \<and> E \<in> ctxt \<and> L \<hookrightarrow> R) \<or> rand \<in> values" using bb by simp
    {
      assume asm1:"rator \<in> values" and asm2:"rand \<in> values"
      hence "(EX E L R. (App rator rand) = E L \<and> E : ctxt \<and> L \<hookrightarrow> R)" using asm1 a aa sub well_typed
        proof (induct rule: values.induct)
          case (abs_value b t x)
          let ?E = "(%t. t)"
          let ?L = "App (Abs x b t) rand"
          have "?L \<hookrightarrow> (b[x::=rand])" by (rule e_beta)
          thus ?case using ex_help[of ?L ?E ?L] by auto
        next
          case (bool_value b) thus ?case using type_arr_case_bool[of G b T0 T1 le eff1] 
            by (auto simp add: trm.inject)
        next
          case (num_value n) thus ?case using type_arr_case_num[of G n T0 T1 le eff1] 
            by (auto simp add: trm.inject)
        next
          case (bi_value b) 
          let ?E = "(%t. t)"
          let ?L = "App ((BI b)) rand"
          have h:"\<And>v. (\<Delta> b rand) = (Some v)  \<Longrightarrow> App ((BI b)) rand \<hookrightarrow> v" using bi_value by auto
          have "EX v . (\<Delta> b rand) = (Some v)" using bi_value typed_prim_reduce[of G b T0 T1 le]  by auto
          then obtain v' where "(\<Delta> b rand) = (Some v')" by auto
          then show ?case using h[of v'] ex_help[of ?L ?E] by auto
        qed
    }
    moreover
    {
      assume asm1:"rator \<in> values" and asm2:"rand \<notin> values"
      have "\<exists>E t t' . App rator rand = E t \<and> E \<in> ctxt \<and> t \<hookrightarrow> t'"
	using asm1 asm2 reduce_in_ctxt[of "(%t . (App rator t))"] ih2 by auto
    }
    moreover
    {
      assume asm:"rator \<notin> values"
      have "\<exists>E t t' . App rator rand = E t \<and> E \<in> ctxt \<and> t \<hookrightarrow> t'"
	using asm reduce_in_ctxt[of "(%t . (App t rand))"] ih1 by auto
    }  
    ultimately show ?thesis by auto
  qed


(* then the main lemma, that every well typed term can be decomposed
   into a context and a redex *)

lemma decomposition:
  assumes a:"closed e" and b:"\<Gamma> \<turnstile> e : t ; eff"
  shows "(EX E L R. e = E L \<and> E : ctxt \<and> L \<hookrightarrow> R) \<or> e : values"
  using b a
proof (induct rule: typing.induct)
  case T_Var
  thus ?case using closed_def by (auto simp add: at_supp at_name_inst trm.supp) 
next
  case T_If
  thus ?case using if_decomp by auto
next
  case T_IfTrue
  thus ?case using if_decomp by auto
next
  case T_IfFalse
  thus ?case using if_decomp by auto
next
  case T_App
  thus ?case using app_decomp by auto
next
  case T_AppPred
  thus ?case using app_decomp by auto
next
  case T_AppPredTrue
  thus ?case using app_decomp by auto
next
  case T_AppPredFalse
  thus ?case using app_decomp by auto
qed (simp_all) (* The value cases are automatic *)

(* Now we conclude progress *)

theorem progress:
  assumes typed:"\<Gamma> \<turnstile> e : t ; eff" and cl:"closed e"
  shows "e : values \<or> (EX e'. e \<longrightarrow> e')"
proof (cases "e : values")
  case False
  hence "(\<exists>E L R. e = E L \<and> E \<in> ctxt \<and> L \<hookrightarrow> R)" using typed cl decomposition[of e] by auto
  thus ?thesis by auto
qed (simp)

(* Some useful lemmas for deriving facts from typing derivations *)

inductive_cases2 app_ty_elim2[consumes 1, case_names 1 2 3 4]: "\<Gamma> \<turnstile> App t1 t2 : \<sigma> ; eff"
thm app_ty_elim2
inductive_cases2 iff_ty_elim2[consumes 1, case_names 1 2 3]: "\<Gamma> \<turnstile> Iff t1 t2 t3 : T ; eff"
inductive_cases2 abs_ty_elim2[consumes 1, case_names 1]: "\<Gamma> \<turnstile> Lam[x:S].b : T ; eff"
thm abs_ty_elim2

lemma app_ty_elim[rule_format]: 
  "\<Gamma> \<turnstile> App t1 t2 : \<sigma> ; eff \<Longrightarrow> 
  \<exists> T0 T0' T1 le eff' eff''. (\<Gamma> \<turnstile> t1 : (T0 \<rightarrow> T1 : le) ; eff' \<and> \<Gamma> \<turnstile> t2 : T0' ; eff'' \<and> \<turnstile> T0' <: T0 \<and> T1 = \<sigma>)"
  by (ind_cases2 "\<Gamma> \<turnstile> App t1 t2 : \<sigma> ; eff")
     (auto simp add: trm.inject)


lemma abs_ty_elim_eff[rule_format]: 
  "\<lbrakk>\<Gamma> \<turnstile> Lam[a:T0].b : \<sigma> ; eff\<rbrakk> \<Longrightarrow> eff = eff.NE"
  by (ind_cases2 "\<Gamma> \<turnstile> Lam[a:T0].b : \<sigma> ; eff")
     (auto simp add: trm.inject)


lemma abs_ty_elim[rule_format]: 
  "\<lbrakk>\<Gamma> \<turnstile> Lam[a:T0].b : \<sigma> ; eff ; a \<sharp> \<Gamma>\<rbrakk> \<Longrightarrow> 
  \<exists> T1 eff'. ((a,T0)#\<Gamma> \<turnstile> b : T1 ; eff' \<and> \<sigma> = (T0 \<rightarrow> T1 : latent_eff.NE) \<and> eff = eff.NE)"
apply (ind_cases2 "\<Gamma> \<turnstile> Lam[a:T0].b: \<sigma> ; eff")
apply(auto simp add: trm.distinct trm.inject alpha) 
apply(drule_tac pi="[(a,x)]::name prm" in eqvt_typing)
apply(auto)
apply(subgoal_tac "([(a,x)]::name prm)\<bullet>\<Gamma> = \<Gamma>")(*A*)
apply(force simp add: calc_atm)
(*A*)
apply(force intro!: pt_fresh_fresh[OF pt_name_inst, OF at_name_inst])
done

lemma app_abs_ty_elim_eff[rule_format]: 
  "\<lbrakk>\<Gamma> \<turnstile> App (Abs x b T) t2 : \<sigma> ; eff ; x \<sharp> \<Gamma>\<rbrakk> \<Longrightarrow> eff = eff.NE"
  proof (ind_cases2 "\<Gamma> \<turnstile> App (Abs x b T) t2 : \<sigma> ; eff", auto simp add: trm.inject abs_ty_elim)
    fix T0 S eff1
    assume  "\<Gamma> \<turnstile> Abs x b T : T0 \<rightarrow> \<sigma> : Latent S ; eff1" and "x \<sharp> \<Gamma>"
    thus False using abs_ty_elim[of \<Gamma> x b T "T0 \<rightarrow> \<sigma> : Latent S"]  by (auto simp add: ty.inject)
  next
    fix T0 S eff1
    assume  "\<Gamma> \<turnstile> Abs x b T : T0 \<rightarrow> \<sigma> : Latent S ; eff1" and "x \<sharp> \<Gamma>"
    thus False using abs_ty_elim[of \<Gamma> x b T "T0 \<rightarrow> \<sigma> : Latent S"]  by (auto simp add: ty.inject)
  next
    fix T0 S eff1
    assume " \<Gamma> \<turnstile> Abs x b T : T0 \<rightarrow> \<sigma> : Latent S ; eff1 " and "x \<sharp> \<Gamma>"
    thus False using abs_ty_elim[of \<Gamma> x b T "T0 \<rightarrow> \<sigma> : Latent S"]  by (auto simp add: ty.inject)
  qed


lemma if_ty_elim_weak[rule_format]: 
  "\<Gamma> \<turnstile> Iff t1 t2 t3: \<sigma> ; eff \<Longrightarrow> \<exists> T0 eff'. (\<Gamma> \<turnstile> t1 : T0 ; eff') \<and> eff = NE"
by (ind_cases2 "\<Gamma> \<turnstile> Iff t1 t2 t3: \<sigma> ; eff")
   (auto simp add: trm.inject)

lemma if_ty_elim[rule_format]: 
  "\<Gamma> \<turnstile> Iff t1 t2 t3: \<sigma> ; eff \<Longrightarrow> 
  (\<exists> T1 T2 T3 F1 F2 F3. (\<Gamma> \<turnstile> t1 : T1 ; F1) \<and> \<Gamma> |+ F1 \<turnstile> t2 : T2 ; F2 \<and> \<Gamma> |- F1 \<turnstile> t3 : T3 ; F3 \<and> \<turnstile> T2 <: \<sigma>  \<and> \<turnstile> T3 <: \<sigma> \<and> eff = NE)
  \<or>
  (\<exists> T1 T3 F3. (\<Gamma> \<turnstile> t1 : T1 ; FF) \<and> \<Gamma> \<turnstile> t3 : T3 ; F3 \<and> \<turnstile> T3 <: \<sigma> \<and> eff = NE)
  \<or>
  (\<exists> T1 T2 F2. (\<Gamma> \<turnstile> t1 : T1 ; TT) \<and> \<Gamma> \<turnstile> t2 : T2 ; F2 \<and> \<turnstile> T2 <: \<sigma>  \<and> eff = NE)"
proof (ind_cases2 "\<Gamma> \<turnstile> Iff t1 t2 t3: \<sigma> ; eff")
  fix e1 T1 eff1 e2 T2 eff2 e3 T3 eff3
  assume "Iff t1 t2 t3 = Iff e1 e2 e3"" eff = eff.NE""  \<Gamma> \<turnstile> e1 : T1 ; eff1""  env_plus1 eff1 \<Gamma> \<turnstile> e2 : T2 ; eff2 "
    "env_minus1 eff1 \<Gamma> \<turnstile> e3 : T3 ; eff3"" \<turnstile> T2 <: \<sigma>"" \<turnstile> T3 <: \<sigma>"
  from prems have A:"\<Gamma> \<turnstile> t1 : T1 ; eff1" using trm.inject by auto
  from prems have B:"\<Gamma> |+ eff1 \<turnstile> t2 : T2 ; eff2" using trm.inject by auto
  from prems have C:"\<Gamma> |- eff1 \<turnstile> t3 : T3 ; eff3" using trm.inject by auto
  from prems have D:"\<turnstile> T2 <: \<sigma>" by auto
  from prems have E:"\<turnstile> T3 <: \<sigma>" by auto
  from prems have F:"eff = NE" by auto
  from A B C D E F show ?thesis by blast 
next
  fix e1 T1 e2 T2 effa e3
  assume "Iff t1 t2 t3 = Iff e1 e2 e3"" eff = eff.NE""  \<Gamma> \<turnstile> e1 : T1 ; TT ""  \<Gamma> \<turnstile> e2 : T2 ; effa "" \<turnstile> T2 <: \<sigma>"
  from prems have A:  "\<Gamma> \<turnstile> t1 : T1 ; TT" using trm.inject by auto
  from prems have B:  "\<Gamma> \<turnstile> t2 : T2 ; effa" using trm.inject by auto
  from prems have C:  "\<turnstile> T2 <: \<sigma>" by auto
  from prems have D: "eff = NE" by auto
  from A B C D show ?thesis by blast
next
  fix e1 T1 e2 T3 effa e3
  assume "Iff t1 t2 t3 = Iff e1 e2 e3"" eff = eff.NE""  \<Gamma> \<turnstile> e1 : T1 ; FF ""  \<Gamma> \<turnstile> e3 : T3 ; effa "" \<turnstile> T3 <: \<sigma>"
  from prems have A:  "\<Gamma> \<turnstile> t1 : T1 ; FF" using trm.inject by auto
  from prems have B:  "\<Gamma> \<turnstile> t3 : T3 ; effa" using trm.inject by auto
  from prems have C:  "\<turnstile> T3 <: \<sigma>" by auto
  from prems have D: "eff = NE" by auto
  from A B C D show ?thesis by blast
qed


lemma false_ty_elim[rule_format]: 
  "\<Gamma> \<turnstile> (trm.Bool False) : \<sigma> ; eff \<Longrightarrow> \<sigma> = ty.Bool \<and> eff = FF \<and> valid \<Gamma>"
apply (ind_cases2 "\<Gamma> \<turnstile> (trm.Bool False) : \<sigma> ; eff")
apply (auto simp add: trm.inject)
done

lemma num_ty_elim[rule_format]: 
  "\<Gamma> \<turnstile> (Num n) : \<sigma> ; eff \<Longrightarrow> \<sigma> = ty.Int \<and> eff = NE \<and> valid \<Gamma>"
apply (ind_cases2 "\<Gamma> \<turnstile> (Num n) : \<sigma> ; eff")
apply (auto simp add: trm.inject)
done

lemma true_ty_elim[rule_format]: 
  "\<Gamma> \<turnstile> (trm.Bool True) : \<sigma> ; eff \<Longrightarrow> \<sigma> = ty.Bool \<and> eff = TT \<and> valid \<Gamma> "
apply (ind_cases2 "\<Gamma> \<turnstile> (trm.Bool True) : \<sigma> ; eff")
apply (auto simp add: trm.inject)
done

lemma bi_ty_elim[rule_format]: 
  "\<Gamma> \<turnstile> (BI b) : \<sigma> ; eff \<Longrightarrow> eff = NE \<and> \<sigma> = \<Delta>\<^isub>\<tau> b \<and> valid \<Gamma>"
apply (ind_cases2 "\<Gamma> \<turnstile> (BI b) : \<sigma> ; eff")
apply (auto simp add: trm.inject)
done

inductive_cases2 iff_false_ty_cases:  "\<Gamma> \<turnstile> Iff (trm.Bool False) t2 t3: \<sigma> ; eff"

inductive_cases2 ff_eff_cases: "\<Gamma> \<turnstile> e : T; FF"
thm ff_eff_cases
inductive_cases2 tt_eff_cases: "\<Gamma> \<turnstile> e : T; TT"
thm tt_eff_cases
inductive_cases2 ne_eff_cases: "\<Gamma> \<turnstile> e : T; NE"
thm ne_eff_cases


(* lemma if_ne_ty_elim[rule_format]: *)
(*   "\<lbrakk>\<Gamma> \<turnstile> Iff tst t1 t2: \<sigma> ; eff ; \<Gamma> \<turnstile> tst : T; NE\<rbrakk> \<Longrightarrow> EX T1 T2 F1 F2. \<Gamma> \<turnstile> t1 : T1 ; F1 \<and> \<Gamma> \<turnstile> t2 : T2 ; F2 \<and> eff = NE \<and> \<turnstile> T1 <: \<sigma> \<and> \<turnstile> T2 <: \<sigma>" *)
(*   apply (ind_cases2 "\<Gamma> \<turnstile> Iff (tst) t1 t2: \<sigma> ; eff") *)
(*   apply (auto simp add: trm.inject ty.inject) *)
(*   apply  *)

lemma if_true_ty_elim[rule_format]: 
   "\<lbrakk>\<Gamma> \<turnstile> Iff v t2 t3: \<sigma> ; eff ; v : values; v ~= Bool False\<rbrakk> \<Longrightarrow>
  \<exists> T0 eff'. ((\<Gamma> \<turnstile> t2 : T0 ; eff') \<and> \<turnstile> T0 <: \<sigma> \<and> eff = NE)"  
proof (ind_cases2 "\<Gamma> \<turnstile> Iff (v) t2 t3: \<sigma> ; eff")
  fix eff1 eff2 T1 T2 e1 e2 e3 
  assume "v : values" "env_plus1 eff1 \<Gamma> \<turnstile> e2 : T2 ; eff2" "Iff v t2 t3 = Iff e1 e2 e3" "\<turnstile> T2 <: \<sigma>" 
    "\<Gamma> \<turnstile> e1 : T1 ; eff1" "eff = NE"
  have "\<Gamma> \<turnstile> v : T1 ; eff1" using prems by (simp add: trm.inject)
  have "eff1 = eff.NE \<or> eff1 = FF \<or> eff1 = TT" using `v : values` `\<Gamma> \<turnstile> v : T1 ; eff1`
  proof (induct rule: values.induct)
    case (abs_value b T x) thus ?case using abs_value abs_ty_elim_eff by auto
  next
    case (num_value n) thus ?case using num_ty_elim by auto
  next
    case (bool_value n) thus ?case using false_ty_elim true_ty_elim by (cases n) auto
  next
    case bi_value thus ?case using bi_ty_elim by auto
  qed
  hence "env_plus1 eff1 \<Gamma> = \<Gamma>" by auto
  hence "\<Gamma> \<turnstile> e2 : T2 ; eff2 \<and> \<turnstile> T2 <: \<sigma>" using prems by auto
  thus ?thesis using prems by (auto simp add: trm.inject)
next
  fix e1 T2 e2 e3 effa
  assume "Iff v t2 t3 = Iff e1 e2 e3"  "\<Gamma> \<turnstile> e2 : T2 ; effa"  "\<turnstile> T2 <: \<sigma>" "eff = NE"
  thus ?thesis by (auto simp add: trm.inject)
next
  fix e1 T1 e3 T3 effa e2
  assume "v : values" "v \<noteq> trm.Bool False" "Iff v t2 t3 = Iff e1 e2 e3" "\<Gamma> \<turnstile> e1 : T1 ; FF" "eff = NE"
  have "v = e1" using prems trm.inject by auto
  hence tv:"\<Gamma> \<turnstile> v : T1 ; FF" by simp
  have "v = Bool False" using `v : values` tv
  proof (induct v rule: values.induct)
    case (abs_value b T x) thus ?case using abs_ty_elim_eff[of \<Gamma> x b T T1 FF] by auto
  next
    case (num_value n) thus ?case using num_ty_elim[of _ _ _ FF] by auto
  next
    case (bool_value n) thus ?case using true_ty_elim[of _ _ FF] by (cases n) auto
  next
    case bi_value thus ?case using bi_ty_elim[of _ _ _ FF] by auto
  qed
  show ?thesis using `v = Bool False` `v ~= Bool False` by auto
qed 


lemma if_false_ty_elim[rule_format]: 
   "\<Gamma> \<turnstile> Iff (trm.Bool False) t2 t3: \<sigma> ; eff \<Longrightarrow>
  \<exists> T0 eff'. ((\<Gamma> \<turnstile> t3 : T0 ; eff') \<and> \<turnstile> T0 <: \<sigma> \<and> eff = eff.NE)"  
proof (ind_cases2 "\<Gamma> \<turnstile> Iff (trm.Bool False) t2 t3: \<sigma> ; eff")
  fix e1 e2 e3 T1
  assume "Iff (trm.Bool False) t2 t3 = Iff e1 e2 e3" and "\<Gamma> \<turnstile> e1 : T1 ; TT"
  hence "\<Gamma> \<turnstile> (trm.Bool False) : T1 ; TT" by (simp add: trm.inject)
  hence "TT = FF" using false_ty_elim[of \<Gamma> T1 TT] by simp
  thus ?thesis by (simp)
next
  fix e1 e2 e3 T1 T3 effa
  assume "Iff (trm.Bool False) t2 t3 = Iff e1 e2 e3" and " eff = eff.NE"and" \<Gamma> \<turnstile> e1 : T1 ; FF" and "  \<Gamma> \<turnstile> e3 : T3 ; effa"and " \<turnstile> T3 <: \<sigma>"
  thus ?thesis by (auto simp add: trm.inject)
next
  fix e1 e2 e3 T1 T3 eff1 eff3
  assume "Iff (trm.Bool False) t2 t3 = Iff e1 e2 e3" and "eff = eff.NE" 
    and f:"\<Gamma> \<turnstile> e1 : T1 ; eff1" and g:"env_minus1 eff1 \<Gamma> \<turnstile> e3 : T3 ; eff3" and "\<turnstile> T3 <: \<sigma>"
  hence "e1 = Bool False" and "t3 = e3" by (auto simp add: trm.inject)
  hence "eff1 = FF" using f false_ty_elim by auto
  hence "env_minus1 eff1 \<Gamma> = \<Gamma>" by simp
  hence "\<Gamma> \<turnstile> e3 : T3 ; eff3" using g by simp
  thus ?thesis using `t3 = e3` `\<turnstile> T3 <: \<sigma>` `eff = eff.NE` by auto
qed 

lemma var_ty_elim:
  "\<Gamma> \<turnstile> Var v : \<sigma> ; eff \<Longrightarrow> (v,\<sigma>) : set \<Gamma> \<and> eff = VE v \<and> valid \<Gamma>"
  by (ind_cases2 "\<Gamma> \<turnstile> Var v : \<sigma> ; eff")
     (auto simp add: trm.inject)

lemma subtype_arr_elim:
  "\<lbrakk>\<turnstile> T <: S ; S = S0 \<rightarrow> S1 : le\<rbrakk> \<Longrightarrow> EX T0 T1. T = T0 \<rightarrow> T1 : le \<and> \<turnstile> S0 <: T0 \<and> \<turnstile> T1 <: S1 "
proof (induct arbitrary: S0 S1  rule: subtype.induct)
  case S_Refl thus ?case by auto
next
  case S_Top thus ?case by (auto simp add: ty.inject)
next
  case (S_Fun T0' S0' T1' S1' le')
  thus ?case using ty.inject by auto
next
  case (S_Trans A B C S0' S1')
  have  "\<exists>T0' T1'. B = T0' \<rightarrow> T1' : le \<and> \<turnstile> S0' <: T0' \<and> \<turnstile> T1' <: S1'" using S_Trans by auto
  then obtain T0' T1' where "B = T0' \<rightarrow> T1' : le "" \<turnstile> S0' <: T0' "" \<turnstile> T1' <: S1'" by auto
  hence "\<exists>T0'' T1''. A = T0'' \<rightarrow> T1'' : le \<and> \<turnstile> T0' <: T0'' \<and> \<turnstile> T1'' <: T1'" using S_Trans by auto
  then obtain T0'' T1'' where a:" A = T0'' \<rightarrow> T1'' : le "" \<turnstile> T0' <: T0'' "" \<turnstile> T1'' <: T1'" by auto
  hence b:"\<turnstile> S0' <: T0''" using ` \<turnstile> S0' <: T0'` by auto
  from a have c:"\<turnstile> T1'' <: S1'" using  ` \<turnstile> T1' <: S1'` by auto
  thus ?case using a b by auto
qed

inductive_cases2 app_ty_ff:"\<Gamma> \<turnstile> App e arg : T' ; FF"
thm app_ty_ff
  
lemma app_ty_ff_elim:
  "\<Gamma> \<turnstile> App rator rand : T ; FF \<Longrightarrow>
  EX S T0 le F1 T0' F2.  \<Gamma> \<turnstile> rator : T0 \<rightarrow> T : le ; F1 \<and> \<Gamma> \<turnstile> rand : T0' ; F2 \<and> \<turnstile> T0' <: T0 \<and> le = Latent S \<and> (~ (\<turnstile> T0' <: S)) \<and> rand : values \<and> closed rand"
  proof (ind_cases2 "\<Gamma> \<turnstile> App rator rand : T ; FF")
    fix e1 T0 S eff1 e2 Ta eff2
    assume "App rator rand = App e1 e2 "" \<Gamma> \<turnstile> e1 : T0 \<rightarrow> T : Latent S ; eff1 "
      "\<Gamma> \<turnstile> e2 : Ta ; eff2 ""\<turnstile> Ta <: T0""~ (\<turnstile> Ta <: S)" "e2 : values" "closed e2"
    have a:" \<Gamma> \<turnstile> rator : T0 \<rightarrow> T : Latent S ; eff1 " using prems trm.inject by auto
    have b:"\<Gamma> \<turnstile> rand : Ta ; eff2"  using prems trm.inject by auto
    have c:"rand : values" "closed rand" using prems trm.inject by auto
    from a b c prems show ?thesis by blast
  qed
  
lemma app_ty_tt_elim:
  "\<Gamma> \<turnstile> App rator rand : T ; TT \<Longrightarrow>
  EX S T0 le F1 T0' F2.  \<Gamma> \<turnstile> rator : T0 \<rightarrow> T : le ; F1 \<and> \<Gamma> \<turnstile> rand : T0' ; F2 \<and> \<turnstile> T0' <: T0 \<and> le = Latent S \<and> \<turnstile> T0' <: S "
  proof (ind_cases2 "\<Gamma> \<turnstile> App rator rand : T ; TT")
    fix e1 T0 S eff1 e2 Ta eff2
    assume "App rator rand = App e1 e2 "" \<Gamma> \<turnstile> e1 : T0 \<rightarrow> T : Latent S ; eff1 "
      "\<Gamma> \<turnstile> e2 : Ta ; eff2 ""\<turnstile> Ta <: T0"" \<turnstile> Ta <: S"
    have a:" \<Gamma> \<turnstile> rator : T0 \<rightarrow> T : Latent S ; eff1 " using prems trm.inject by auto
    have b:"\<Gamma> \<turnstile> rand : Ta ; eff2"  using prems trm.inject by auto
    from a b prems show ?thesis by blast
  qed

text {* complete induction on typing derivations *}

lemma typing_induct_complete[consumes 1, case_names T_Var T_Const T_Num T_True T_False T_App T_Lam T_AppPred T_If 
  T_AppPredTrue T_AppPredFalse T_IfTrue T_IfFalse]:
  fixes  P :: "'a::fs_name\<Rightarrow>(name\<times>ty) list \<Rightarrow> trm \<Rightarrow> ty \<Rightarrow> eff \<Rightarrow> bool"
  and    \<Gamma> :: "(name\<times>ty) list"
  and    t :: "trm"
  and    T :: "ty"
  and    F :: "eff"
  and    x :: "'a::fs_name"
  assumes a: "\<Gamma> \<turnstile> t : T ; F"
  and a1:    "\<And>\<Gamma> (a::name) \<tau> x. valid \<Gamma> \<Longrightarrow> (a,\<tau>) \<in> set \<Gamma> \<Longrightarrow> 
  (!! x t T \<Gamma> F. (t,Var a) : smaller_than \<Longrightarrow> \<Gamma> \<turnstile> t : T ; F \<Longrightarrow> P x \<Gamma> t T F) \<Longrightarrow> valid \<Gamma> \<Longrightarrow> P x \<Gamma> (Var a) \<tau> (VE a)"
  and a2:    "!! \<Gamma> b T x. \<Delta>\<^isub>\<tau> b = T \<Longrightarrow> 
  (!! x t T \<Gamma> F. (t,BI b) : smaller_than \<Longrightarrow> \<Gamma> \<turnstile> t : T ; F \<Longrightarrow> P x \<Gamma> t T F) \<Longrightarrow> valid \<Gamma> \<Longrightarrow> P x \<Gamma> (BI b) T NE"
  and a3:    "!! \<Gamma> n x.   (!! x t T \<Gamma> F. (t,Num n) : smaller_than \<Longrightarrow> \<Gamma> \<turnstile> t : T ; F \<Longrightarrow> P x \<Gamma> t T F) \<Longrightarrow> valid \<Gamma> \<Longrightarrow> 
  P x \<Gamma> (Num n) ty.Int NE"
  and a4:    "!! \<Gamma> x.   (!! x t T \<Gamma> F. (t,Bool True) : smaller_than \<Longrightarrow> \<Gamma> \<turnstile> t : T ; F \<Longrightarrow> P x \<Gamma> t T F) \<Longrightarrow> valid \<Gamma> \<Longrightarrow> 
  P x \<Gamma> (Bool True) ty.Bool TT"
  and a5:    "!! \<Gamma> x. (!! x t T \<Gamma> F. (t,Bool False) : smaller_than \<Longrightarrow> \<Gamma> \<turnstile> t : T ; F \<Longrightarrow> P x \<Gamma> t T F) \<Longrightarrow> valid \<Gamma> \<Longrightarrow> 
  P x \<Gamma> (Bool False) ty.Bool FF"
  and a6:    "\<And>\<Gamma> \<tau> \<sigma> t1 t2 x F1 F2 le \<tau>0. (!! x t T \<Gamma> F. (t,App t1 t2) : smaller_than \<Longrightarrow> \<Gamma> \<turnstile> t : T ; F \<Longrightarrow> P x \<Gamma> t T F) \<Longrightarrow> 
              \<Gamma> \<turnstile> t1 : \<tau>\<rightarrow>\<sigma>:le ; F1 \<Longrightarrow> (\<And>z. P z \<Gamma> t1 (\<tau>\<rightarrow>\<sigma>:le) F1) \<Longrightarrow> \<Gamma> \<turnstile> t2 : \<tau>0 ; F2 \<Longrightarrow> (\<And>z. P z \<Gamma> t2 \<tau>0 F2) \<Longrightarrow> \<turnstile> \<tau>0 <: \<tau>
              \<Longrightarrow> P x \<Gamma> (App t1 t2) \<sigma> NE"
  and a7:    "\<And>a \<Gamma> \<tau> \<sigma> t x F0. a\<sharp>x \<Longrightarrow> a\<sharp>\<Gamma> \<Longrightarrow> ((a,\<tau>) # \<Gamma>) \<turnstile> t : \<sigma> ; F0 \<Longrightarrow> (\<And>z. P z ((a,\<tau>)#\<Gamma>) t \<sigma> F0) \<Longrightarrow>
              (!! x t' T \<Gamma> F. (t',Lam[a:\<tau>].t) : smaller_than \<Longrightarrow> \<Gamma> \<turnstile> t' : T ; F \<Longrightarrow> P x \<Gamma> t' T F) 
              \<Longrightarrow> P x \<Gamma> (Lam [a:\<tau>].t) (\<tau>\<rightarrow>\<sigma>:latent_eff.NE) NE"
  and a8:    "\<And>\<Gamma> \<tau> \<sigma> t1 t2 x F1 \<tau>0 S v. 
              (!! x t T \<Gamma> F. t \<guillemotleft> App t1 t2 \<Longrightarrow> \<Gamma> \<turnstile> t : T ; F \<Longrightarrow> P x \<Gamma> t T F) \<Longrightarrow> 
              \<Gamma> \<turnstile> t1 : \<tau>\<rightarrow>\<sigma>:Latent S ; F1 \<Longrightarrow> (\<And>z. P z \<Gamma> t1 (\<tau>\<rightarrow>\<sigma>:Latent S) F1) \<Longrightarrow> \<Gamma> \<turnstile> t2 : \<tau>0 ; VE v \<Longrightarrow> (\<And>z. P z \<Gamma> t2 \<tau>0 (VE v)) 
              \<Longrightarrow> \<turnstile> \<tau>0 <: \<tau>  \<Longrightarrow> P x \<Gamma> (App t1 t2) \<sigma> (TE S v)"
  and a9:    "!! \<Gamma> e1 e2 e3 T1 T2 T3 T eff1 eff2 eff3 x. 
                 \<lbrakk>\<Gamma> \<turnstile> e1 : T1; eff1; !!z. P z \<Gamma> e1 T1 eff1; (\<Gamma> |+ eff1) \<turnstile> e2 : T2; eff2; !!z. P z (\<Gamma>|+ eff1) e2 T2 eff2; 
                (!! x t T \<Gamma> F. t \<guillemotleft> Iff e1 e2 e3 \<Longrightarrow> \<Gamma> \<turnstile> t : T ; F \<Longrightarrow> P x \<Gamma> t T F);
                 (\<Gamma> |- eff1) \<turnstile> e3 : T3; eff3; !!z. P z (\<Gamma>|- eff1) e3 T3 eff3; \<turnstile> T2 <: T; \<turnstile> T3 <: T\<rbrakk>
                 \<Longrightarrow> P x \<Gamma> (Iff e1 e2 e3) T NE"
  and a10:   "!! \<Gamma> e1 e2 T0 T1 T S eff1 eff2 x. \<lbrakk>\<Gamma> \<turnstile> e1 : (T0 \<rightarrow> T1 : Latent S); eff1; !!z. P z \<Gamma> e1 (T0 \<rightarrow> T1 : Latent S) eff1;
              (!! x t T \<Gamma> F. t \<guillemotleft> App e1 e2 \<Longrightarrow> \<Gamma> \<turnstile> t : T ; F \<Longrightarrow> P x \<Gamma> t T F);
              \<Gamma> \<turnstile> e2 : T; eff2 ;  !! z. P z \<Gamma> e2 T eff2; \<turnstile> T <: T0; \<turnstile> T <: S\<rbrakk> \<Longrightarrow> P x \<Gamma> (App e1 e2) T1 TT"
  and a11:   "!! \<Gamma> e1 e2 T0 T1 T S eff1 eff2 x. \<lbrakk>\<Gamma> \<turnstile> e1 : (T0 \<rightarrow> T1 : Latent S); eff1; !!z. P z \<Gamma> e1 (T0 \<rightarrow> T1 : Latent S) eff1;
              (!! x t T \<Gamma> F. t \<guillemotleft> App e1 e2 \<Longrightarrow> \<Gamma> \<turnstile> t : T ; F \<Longrightarrow> P x \<Gamma> t T F);
              \<Gamma> \<turnstile> e2 : T; eff2 ;  !! z. P z \<Gamma> e2 T eff2; \<turnstile> T <: T0; ~(\<turnstile> T <: S) ; e2 : values ; closed e2\<rbrakk>
  \<Longrightarrow> P x \<Gamma> (App e1 e2) T1 FF"
  and a12:   "!! \<Gamma> e1 e2 e3 T T1 T2 eff x. \<lbrakk>\<Gamma> \<turnstile> e1 : T1 ; TT ; !! z. P z \<Gamma> e1 T1 TT; 
                (!! x t T \<Gamma> F. t \<guillemotleft> Iff e1 e2 e3 \<Longrightarrow> \<Gamma> \<turnstile> t : T ; F \<Longrightarrow> P x \<Gamma> t T F);
               \<Gamma> \<turnstile> e2 : T2 ; eff;  !!z .P z \<Gamma> e2 T2 eff; \<turnstile> T2 <: T\<rbrakk> \<Longrightarrow> P x \<Gamma> (Iff e1 e2 e3) T NE"
  and a13:   "!! \<Gamma> e1 e2 e3 T T1 T3 eff x. \<lbrakk>\<Gamma> \<turnstile> e1 : T1 ; FF ; !! z. P z \<Gamma> e1 T1 FF; 
                (!! x t T \<Gamma> F. t \<guillemotleft> Iff e1 e2 e3 \<Longrightarrow> \<Gamma> \<turnstile> t : T ; F \<Longrightarrow> P x \<Gamma> t T F);
               \<Gamma> \<turnstile> e3 : T3 ; eff;  !!z .P z \<Gamma> e3 T3 eff; \<turnstile> T3 <: T\<rbrakk> \<Longrightarrow> P x \<Gamma> (Iff e1 e2 e3) T NE"
  shows "P x \<Gamma> t T F"
  using a
  proof (nominal_induct t avoiding: x \<Gamma> T F rule: trm_comp_induct)
    case (Var v) 
    thus ?case using a1 var_ty_elim[of \<Gamma> v T F] by auto
  next
    case (App t1 t2 x \<Gamma> T)
    show ?case using App(4)
    proof (induct rule: app_ty_elim2)
      case 1 thus ?thesis using a6 App trm.inject ty.inject by auto
    next
      case 2 thus ?thesis using a8 App trm.inject ty.inject by auto
    next
      case 3 thus ?thesis using a10 App trm.inject ty.inject by auto
    next
      case 4 thus ?thesis using a11 App trm.inject ty.inject by auto
    qed
  next
    case Iff
    show ?case using Iff(5)
    proof (induct rule: iff_ty_elim2)
      case 1 thus ?thesis using a9 Iff trm.inject ty.inject by auto
    next
      case 2 thus ?thesis using a12 Iff trm.inject ty.inject by auto
    next
      case 3 thus ?thesis using a13 Iff trm.inject ty.inject by auto
    qed
  next
    case (Lam v b x \<Gamma> S1 F S2)
    show ?case using Lam abs_ty_elim[of \<Gamma> v b S2 S1 F] a7 by (auto simp add: trm.inject ty.inject)
  next
    case (BI b) thus ?case using bi_ty_elim[of \<Gamma> b T F] trm.inject a2 by auto
  next
    case (Num n) thus ?case using num_ty_elim[of \<Gamma> n T F] trm.inject a3 by auto
  next
    case (Bool b) thus ?case using true_ty_elim[of \<Gamma> T F] false_ty_elim[of \<Gamma> T F] trm.inject a4 a5 by (cases b) auto
qed



text {* lemmas about the effects of closed terms *}

lemma ve_not_closed:
  "\<Gamma> \<turnstile> e : T ; eff.VE x \<Longrightarrow>
  x : supp e"
  by (ind_cases2 "\<Gamma> \<turnstile> e : T ; eff.VE x")
     (auto simp add: eff.inject trm.supp at_supp supp_atm)

lemma te_not_closed:
  "\<Gamma> \<turnstile> e : T ; eff.TE T' x \<Longrightarrow>
  x : supp e"
  proof (ind_cases2 "\<Gamma> \<turnstile> e : T ; eff.TE T' x")
    fix e1 T0 S eff1 e2 Ta xa
    assume "e = App e1 e2" "TE T' x = TE S xa" "\<Gamma> \<turnstile> e2 : Ta ; VE xa"
    have "x = xa" using prems eff.inject by auto
    hence "\<Gamma> \<turnstile> e2 : Ta ; VE x" using prems eff.inject by auto
    hence "x : supp e2" using ve_not_closed by auto
    thus "x : supp e" using prems trm.supp by auto
  qed

lemma closed_eff:
  assumes "closed e" and "\<Gamma> \<turnstile> e : T ; eff"
  shows "simple_eff eff"
using prems
proof (nominal_induct eff rule: eff.induct)
  case (VE name) thus ?case using ve_not_closed[of _ e _ name] closed_def by auto
next
  case (TE _ name) thus ?case using te_not_closed[of _ e _ _ name] closed_def by auto
qed (auto)

lemma closed_eff_below_NE:
  assumes "closed e" and "\<Gamma> \<turnstile> e : T ; eff"
  shows "\<turnstile> eff <e: eff.NE"
  using closed_eff simple_eff_below_ne prems by auto

inductive_cases2 const_ty_int_case: "\<Gamma> \<turnstile> (Num n) : ty.Int ; eff"
inductive_cases2 trm_ty_int_case: "\<Gamma> \<turnstile> e : ty.Int ; eff"
inductive_cases2 const_ty_bool_case: "\<Gamma> \<turnstile> (Bool b) : ty.Bool ; eff"
thm const_ty_bool_case
thm trm_ty_int_case


lemma add1_eff_ne:
  "\<Gamma> \<turnstile> (App (BI Add1) v) :  T1 ; eff1 \<Longrightarrow> eff1 = eff.NE"
proof (ind_cases2 " \<Gamma> \<turnstile> (App (BI Add1) v) :  T1 ; eff1")
  assume "eff1 = eff.NE" thus ?thesis by simp
next
  fix T0 T1 S eff1a e1 e2
  assume "\<Gamma> \<turnstile> e1 : T0 \<rightarrow> T1 : Latent S ; eff1a" "App (BI Add1) v = App e1 e2"
  hence "\<Gamma> \<turnstile> (BI Add1) : T0 \<rightarrow> T1 : Latent S ; eff1a" by (simp add: trm.inject)
  hence "\<Delta>\<^isub>\<tau> Add1 = T0 \<rightarrow> T1 : Latent S" using type_add1_case[of \<Gamma> "T0 \<rightarrow> T1 : Latent S"] by (auto simp add: trm.inject)
  thus ?thesis by (auto simp add: ty.inject)
next
  fix T0 T1 S eff1a e1 e2
  assume "\<Gamma> \<turnstile> e1 : T0 \<rightarrow> T1 : Latent S ; eff1a" "App (BI Add1) v = App e1 e2"
  hence "\<Gamma> \<turnstile> (BI Add1) : T0 \<rightarrow> T1 : Latent S ; eff1a" by (simp add: trm.inject)
  hence "\<Delta>\<^isub>\<tau> Add1 = T0 \<rightarrow> T1 : Latent S" using type_add1_case[of \<Gamma> "T0 \<rightarrow> T1 : Latent S"] by (auto simp add: trm.inject)
  thus ?thesis by (auto simp add: ty.inject)
next
  fix T0 T1 S eff1a e1 e2
  assume "\<Gamma> \<turnstile> e1 : T0 \<rightarrow> T1 : Latent S ; eff1a" "App (BI Add1) v = App e1 e2"
  hence "\<Gamma> \<turnstile> (BI Add1) : T0 \<rightarrow> T1 : Latent S ; eff1a" by (simp add: trm.inject)
  hence "\<Delta>\<^isub>\<tau> Add1 = T0 \<rightarrow> T1 : Latent S" using type_add1_case[of \<Gamma> "T0 \<rightarrow> T1 : Latent S"] by (auto simp add: trm.inject)
  thus ?thesis by (auto simp add: ty.inject)
qed



inductive_cases2 type_nott_case: "\<Gamma> \<turnstile> (BI Nott) : t ; e"

lemma nott_eff_ne:
  "\<Gamma> \<turnstile> (App (BI Nott) v) :  T1 ; eff1 \<Longrightarrow> eff1 = eff.NE"
proof (ind_cases2 " \<Gamma> \<turnstile> (App (BI Nott) v) :  T1 ; eff1")
  assume "eff1 = eff.NE" thus ?thesis by simp
next
  fix T0 T1 S eff1a e1 e2
  assume "\<Gamma> \<turnstile> e1 : T0 \<rightarrow> T1 : Latent S ; eff1a" "App (BI Nott) v = App e1 e2"
  hence "\<Gamma> \<turnstile> (BI Nott) : T0 \<rightarrow> T1 : Latent S ; eff1a" by (simp add: trm.inject)
  hence "\<Delta>\<^isub>\<tau> Nott = T0 \<rightarrow> T1 : Latent S" using type_nott_case[of \<Gamma> "T0 \<rightarrow> T1 : Latent S"] by (auto simp add: trm.inject)
  thus ?thesis by (auto simp add: ty.inject)
next
  fix T0 T1 S eff1a e1 e2
  assume "\<Gamma> \<turnstile> e1 : T0 \<rightarrow> T1 : Latent S ; eff1a" "App (BI Nott) v = App e1 e2"
  hence "\<Gamma> \<turnstile> (BI Nott) : T0 \<rightarrow> T1 : Latent S ; eff1a" by (simp add: trm.inject)
  hence "\<Delta>\<^isub>\<tau> Nott = T0 \<rightarrow> T1 : Latent S" using type_nott_case[of \<Gamma> "T0 \<rightarrow> T1 : Latent S"] by (auto simp add: trm.inject)
  thus ?thesis by (auto simp add: ty.inject)
next
  fix T0 T1 S eff1a e1 e2
  assume "\<Gamma> \<turnstile> e1 : T0 \<rightarrow> T1 : Latent S ; eff1a" "App (BI Nott) v = App e1 e2"
  hence "\<Gamma> \<turnstile> (BI Nott) : T0 \<rightarrow> T1 : Latent S ; eff1a" by (simp add: trm.inject)
  hence "\<Delta>\<^isub>\<tau> Nott = T0 \<rightarrow> T1 : Latent S" using type_nott_case[of \<Gamma> "T0 \<rightarrow> T1 : Latent S"] by (auto simp add: trm.inject)
  thus ?thesis by (auto simp add: ty.inject)
qed

inductive_cases2 type_booleanp_case: "\<Gamma> \<turnstile> (BI BooleanP) : t ; e"

lemma value_eff:
  assumes "v : values" and "\<Gamma> \<turnstile> v :  T ; eff"
  shows "simple_eff eff"
  using prems
  proof (induct v rule :values.induct)
    case abs_value thus ?case using abs_ty_elim_eff by auto
  next
    case num_value thus ?case using num_ty_elim by auto
  next
    case (bool_value b) thus ?case using true_ty_elim false_ty_elim by (cases b) auto
  next
    case bi_value thus ?case using bi_ty_elim by auto
  qed

lemma booleanp_eff_simple:
  "\<lbrakk>\<Gamma> \<turnstile> (App (BI BooleanP) v) :  T1 ; eff1 ; v : values\<rbrakk> \<Longrightarrow> simple_eff eff1"
proof (ind_cases2 " \<Gamma> \<turnstile> (App (BI BooleanP) v) :  T1 ; eff1")
  fix T0 T1 S eff1a e1 e2 xa T
  assume "\<Gamma> \<turnstile> e2 : T ; VE xa" "App (BI BooleanP) v = App e1 e2" "v : values"
  hence "VE xa = eff.NE \<or> VE xa = eff.TT  \<or> VE xa = eff.FF " using value_eff[of v \<Gamma> T "VE xa"] by (auto simp add: trm.inject)
  thus ?thesis using ty.distinct by auto
qed (auto)

lemma numberp_eff_simple:
  "\<lbrakk>\<Gamma> \<turnstile> (App (BI NumberP) v) :  T1 ; eff1 ; v : values\<rbrakk> \<Longrightarrow> simple_eff eff1"
proof (ind_cases2 " \<Gamma> \<turnstile> (App (BI NumberP) v) :  T1 ; eff1")
  fix T0 T1 S eff1a e1 e2 xa T
  assume "\<Gamma> \<turnstile> e2 : T ; VE xa" "App (BI NumberP) v = App e1 e2" "v : values"
  hence "VE xa = eff.NE \<or> VE xa = eff.TT  \<or> VE xa = eff.FF " using value_eff[of v \<Gamma> T "VE xa"] by (auto simp add: trm.inject)
  thus ?thesis using ty.distinct by auto
qed (auto)

inductive_cases2 app_boolp_ff: "\<Gamma> \<turnstile> (App (BI BooleanP) v) :  T1 ; FF"
thm app_boolp_ff

lemma booleanp_FF_preserved:
  assumes "\<Gamma> \<turnstile> (App (BI BooleanP) v) :  T1 ; FF" and "v : values" and "\<Delta> BooleanP v = Some u"
  shows "u = Bool False"
  using `v : values` prems
  proof (induct v rule: values.induct)
    case (bool_value b)
    let ?P = "\<Gamma> \<turnstile> App (BI BooleanP) (trm.Bool b) : T1 ; FF" 
    have "?P ==> ?case"
      proof (ind_cases2 ?P)
        fix S T e1 e2 T0 eff1 eff2
        assume "App (BI BooleanP) (trm.Bool b) = App e1 e2"  "\<Gamma> \<turnstile> e1 : T0 \<rightarrow> T1 : Latent S ; eff1 "  "\<Gamma> \<turnstile> e2 : T ; eff2"
          "~ (\<turnstile> T <: S)" "e2 : values"
        hence a:"\<Gamma> \<turnstile> (BI BooleanP) : T0 \<rightarrow> T1 : Latent S ; eff1 " using trm.inject by auto
        from prems have b:"\<Gamma> \<turnstile> Bool b : T ; eff2" using trm.inject by auto
        from a have c:"S = ty.Bool" using bi_ty_elim[of \<Gamma> BooleanP "T0 \<rightarrow> T1 : Latent S"] ty.inject latent_eff.inject by auto
        from b have d:"T = ty.Bool" using true_ty_elim false_ty_elim by (cases b) auto
        from c d have "\<turnstile> T <: S" by auto
        thus ?thesis using prems by auto
      qed
    thus ?case using bool_value by auto
  qed (auto)

lemma booleanp_TT_preserved:
  assumes "\<Gamma> \<turnstile> (App (BI BooleanP) v) :  T1 ; TT" and "v : values" and "\<Delta> BooleanP v = Some u"
  shows "u = Bool True"
  using `v : values` prems
  proof (nominal_induct v avoiding: \<Gamma> rule: values_induct)
    case (bool_value b) thus ?case by auto
  next
    case (num_value n)
    let ?P = "\<Gamma> \<turnstile> App (BI BooleanP) (Num n) : T1 ; TT" 
    have "?P ==> ?case"
    proof (ind_cases2 ?P)
      fix S T e1 e2 T0 eff1 eff2
      assume "App (BI BooleanP) (Num n) = App e1 e2"  "\<Gamma> \<turnstile> e1 : T0 \<rightarrow> T1 : Latent S ; eff1 "  "\<Gamma> \<turnstile> e2 : T ; eff2"
        "\<turnstile> T <: S"
      hence a:"\<Gamma> \<turnstile> (BI BooleanP) : T0 \<rightarrow> T1 : Latent S ; eff1 " using trm.inject by auto
      from prems have b:"\<Gamma> \<turnstile> Num n : T ; eff2" using trm.inject by auto
      from a have c:"S = ty.Bool" using bi_ty_elim[of \<Gamma> BooleanP "T0 \<rightarrow> T1 : Latent S"] ty.inject latent_eff.inject by auto
      from b have d:"T ~= ty.Bool" using num_ty_elim[of \<Gamma> n T eff2] by auto
      thus ?thesis using c no_sub_bool[of T S] prems by auto
    qed
    thus ?case using num_value by auto
  next
    case (bi_value n)
    let ?P = "\<Gamma> \<turnstile> App (BI BooleanP) (BI n) : T1 ; TT" 
    have "?P ==> ?case"
    proof (ind_cases2 ?P)
      fix S T e1 e2 T0 eff1 eff2
      assume "App (BI BooleanP) (BI n) = App e1 e2"  "\<Gamma> \<turnstile> e1 : T0 \<rightarrow> T1 : Latent S ; eff1 "  "\<Gamma> \<turnstile> e2 : T ; eff2"
        "\<turnstile> T <: S"
      hence a:"\<Gamma> \<turnstile> (BI BooleanP) : T0 \<rightarrow> T1 : Latent S ; eff1 " using trm.inject by auto
      from prems have b:"\<Gamma> \<turnstile> BI n : T ; eff2" using trm.inject by auto
      from a have c:"S = ty.Bool" using bi_ty_elim[of \<Gamma> BooleanP "T0 \<rightarrow> T1 : Latent S"] ty.inject latent_eff.inject by auto
      from b have d:"T ~= ty.Bool" using bi_ty_elim[of \<Gamma> n T eff2] by (nominal_induct n rule: builtin.induct) auto
      thus ?thesis using c no_sub_bool[of T S] prems by auto
    qed
    thus ?case using bi_value by auto
  next
    case (abs_value x U b)
    let ?P = "\<Gamma> \<turnstile> App (BI BooleanP) (Abs x b U) : T1 ; TT" 
    have "?P ==> ?case"
    proof (ind_cases2 ?P)
      fix S T e1 e2 T0 eff1 eff2
      assume "App (BI BooleanP) (Abs x b U) = App e1 e2"  "\<Gamma> \<turnstile> e1 : T0 \<rightarrow> T1 : Latent S ; eff1 "  "\<Gamma> \<turnstile> e2 : T ; eff2"
        "\<turnstile> T <: S"
      hence a:"\<Gamma> \<turnstile> (BI BooleanP) : T0 \<rightarrow> T1 : Latent S ; eff1 " using trm.inject by auto
      from prems have b:"\<Gamma> \<turnstile> Abs x b U : T ; eff2" using trm.inject by auto
      from a have c:"S = ty.Bool" using bi_ty_elim[of \<Gamma> BooleanP "T0 \<rightarrow> T1 : Latent S"] ty.inject latent_eff.inject by auto
      from b have d:"T ~= ty.Bool" using `x \<sharp> \<Gamma>` abs_ty_elim[of \<Gamma> x b U T eff2] by auto
      thus ?thesis using c no_sub_bool[of T S] prems by auto
    qed
    thus ?case using abs_value by auto
  qed

lemma booleanp_soundness_eff:
  assumes "\<Gamma> \<turnstile> App (BI BooleanP) v : T ; F" and "v : values" and "\<Delta> BooleanP v = Some u" and "\<Gamma> \<turnstile> u : T' ; F'"
  shows "\<turnstile> F' <e: F"
  proof -
    have cl:"closed u" using prems delta_closed[of BooleanP v u] by auto
    hence se:"simple_eff F'" using prems closed_eff by auto
    have or:"simple_eff F" using booleanp_eff_simple prems by auto
    thus ?thesis using prems
      proof (induct rule: simple_eff_cases)
        case NE thus ?case using se simple_eff_below_ne by auto
      next
        case FF thus ?case using false_ty_elim[of \<Gamma> T' F'] booleanp_FF_preserved by auto 
      next
        case TT thus ?case using true_ty_elim[of \<Gamma> T' F'] booleanp_TT_preserved by auto 
      qed
    qed

inductive_cases2 app_nump_ff: "\<Gamma> \<turnstile> (App (BI NumberP) v) :  T1 ; FF"
thm app_nump_ff

lemma numberp_FF_preserved:
  assumes "\<Gamma> \<turnstile> (App (BI NumberP) v) :  T1 ; FF" and "v : values" and "\<Delta> NumberP v = Some u"
  shows "u = Bool False"
  using `v : values` prems
  proof (induct v rule: values.induct)
    case (bool_value b) thus ?case by (cases b) auto
  next
    case (num_value b) 
    let ?P = "\<Gamma> \<turnstile> App (BI NumberP) (trm.Num b) : T1 ; FF" 
    have "?P ==> ?case"
      proof (ind_cases2 ?P)
        fix S T e1 e2 T0 eff1 eff2
        assume "App (BI NumberP) (trm.Num b) = App e1 e2"  "\<Gamma> \<turnstile> e1 : T0 \<rightarrow> T1 : Latent S ; eff1 "  "\<Gamma> \<turnstile> e2 : T ; eff2"
          "~ (\<turnstile> T <: S)"
        hence a:"\<Gamma> \<turnstile> (BI NumberP) : T0 \<rightarrow> T1 : Latent S ; eff1 " using trm.inject by auto
        from prems have b:"\<Gamma> \<turnstile> Num b : T ; eff2" using trm.inject by auto
        from a have c:"S = ty.Int" using bi_ty_elim[of \<Gamma> NumberP "T0 \<rightarrow> T1 : Latent S"] ty.inject latent_eff.inject by auto
        from b have d:"T = ty.Int" using num_ty_elim by  auto
        from c d have "\<turnstile> T <: S" by auto
        thus ?thesis using prems by auto
      qed
    thus ?case using num_value by auto
  qed (auto)

lemma numberp_TT_preserved:
  assumes "\<Gamma> \<turnstile> (App (BI NumberP) v) :  T1 ; TT" and "v : values" and "\<Delta> NumberP v = Some u"
  shows "u = Bool True"
  using `v : values` prems
  proof (nominal_induct v avoiding: \<Gamma> rule: values_induct)
    case (num_value b) thus ?case by auto
  next
    case (bi_value n)
    let ?P = "\<Gamma> \<turnstile> App (BI NumberP) (BI n) : T1 ; TT" 
    have "?P ==> ?case"
    proof (ind_cases2 ?P)
      fix S T e1 e2 T0 eff1 eff2
      assume "App (BI NumberP) (BI n) = App e1 e2"  "\<Gamma> \<turnstile> e1 : T0 \<rightarrow> T1 : Latent S ; eff1 "  "\<Gamma> \<turnstile> e2 : T ; eff2"
        "\<turnstile> T <: S"
      hence a:"\<Gamma> \<turnstile> (BI NumberP) : T0 \<rightarrow> T1 : Latent S ; eff1 " using trm.inject by auto
      from prems have b:"\<Gamma> \<turnstile> BI n : T ; eff2" using trm.inject by auto
      from a have c:"S = ty.Int" using bi_ty_elim[of \<Gamma> NumberP "T0 \<rightarrow> T1 : Latent S"] ty.inject latent_eff.inject by auto
      from b have d:"T ~= ty.Int" using bi_ty_elim[of \<Gamma> n T eff2] by (nominal_induct n rule: builtin.induct) auto
      thus ?thesis using c no_sub_int[of T S] prems by auto
    qed
    thus ?case using bi_value by auto
  next
    case (abs_value x U b)
    let ?P = "\<Gamma> \<turnstile> App (BI NumberP) (Abs x b U) : T1 ; TT" 
    have "?P ==> ?case"
    proof (ind_cases2 ?P)
      fix S T e1 e2 T0 eff1 eff2
      assume "App (BI NumberP) (Abs x b U) = App e1 e2"  "\<Gamma> \<turnstile> e1 : T0 \<rightarrow> T1 : Latent S ; eff1 "  "\<Gamma> \<turnstile> e2 : T ; eff2"
        "\<turnstile> T <: S"
      hence a:"\<Gamma> \<turnstile> (BI NumberP) : T0 \<rightarrow> T1 : Latent S ; eff1 " using trm.inject by auto
      from prems have b:"\<Gamma> \<turnstile> Abs x b U : T ; eff2" using trm.inject by auto
      from a have c:"S = ty.Int" using bi_ty_elim[of \<Gamma> NumberP "T0 \<rightarrow> T1 : Latent S"] ty.inject latent_eff.inject by auto
      from b have d:"T ~= ty.Int" using `x \<sharp> \<Gamma>` abs_ty_elim[of \<Gamma> x b U T eff2] by auto
      thus ?thesis using c no_sub_int[of T S] prems by auto
    qed
    thus ?case using abs_value by auto
  next
    case (bool_value b)
    let ?P = "\<Gamma> \<turnstile> App (BI NumberP) (Bool b) : T1 ; TT" 
    have "?P ==> ?case"
    proof (ind_cases2 ?P)
      fix S T e1 e2 T0 eff1 eff2
      assume "App (BI NumberP) (Bool b) = App e1 e2"  "\<Gamma> \<turnstile> e1 : T0 \<rightarrow> T1 : Latent S ; eff1 "  "\<Gamma> \<turnstile> e2 : T ; eff2"
        "\<turnstile> T <: S"
      hence a:"\<Gamma> \<turnstile> (BI NumberP) : T0 \<rightarrow> T1 : Latent S ; eff1 " using trm.inject by auto
      from prems have b:"\<Gamma> \<turnstile> Bool b : T ; eff2" using trm.inject by auto
      from a have c:"S = ty.Int" using bi_ty_elim[of \<Gamma> NumberP "T0 \<rightarrow> T1 : Latent S"] ty.inject latent_eff.inject by auto
      from b have d:"T ~= ty.Int" using true_ty_elim[of \<Gamma> T eff2] false_ty_elim[of \<Gamma> T eff2] by (cases b) auto
      thus ?thesis using c no_sub_int[of T S] prems by auto
    qed
    thus ?case using bool_value by auto
  qed

lemma numberp_soundness_eff:
  assumes "\<Gamma> \<turnstile> App (BI NumberP) v : T ; F" and "v : values" and "\<Delta> NumberP v = Some u" and "\<Gamma> \<turnstile> u : T' ; F'"
  shows "\<turnstile> F' <e: F"
  proof -
    have cl:"closed u" using prems delta_closed[of NumberP v u] by auto
    hence se:"simple_eff F'" using prems closed_eff by auto
    have or:"simple_eff F" using numberp_eff_simple prems by auto
    thus ?thesis using prems
      proof (induct rule: simple_eff_cases)
        case NE thus ?case using se simple_eff_below_ne by auto
      next
        case FF thus ?case using false_ty_elim[of \<Gamma> T' F'] numberp_FF_preserved by auto 
      next
        case TT thus ?case using true_ty_elim[of \<Gamma> T' F'] numberp_TT_preserved by auto 
      qed
    qed

lemma typing_valid:
  assumes "\<Gamma> \<turnstile> e : T ; F"
  shows "valid \<Gamma>"
using prems 
proof (induct)
  case (T_Abs a \<Gamma> T b T' F') thus ?case using valid_elim[of a T \<Gamma>] by auto
qed (auto)

text {* soundness of the \<Delta> rule *}

lemma delta_soundness:
  assumes "\<Delta>\<^isub>\<tau> b = (T0 \<rightarrow> T1 : le)" and "v : values" and "\<Gamma> \<turnstile> v : T ; eff1" and "\<turnstile> T <: T0" and "\<Gamma> \<turnstile> (App (BI b) v) : T1 ; eff"
  and "\<Delta> b v = Some u" and "valid \<Gamma>"
  shows "EX eff'. \<Gamma> \<turnstile> u : T1 ; eff' \<and> \<turnstile> eff' <e: eff"
  using prems
proof (nominal_induct b rule: builtin.induct)
  case Add1
  hence a:"eff = NE" using add1_eff_ne[of \<Gamma> v T1 eff] by auto
  have "EX  eff'. \<Gamma> \<turnstile> u : T1 ; eff'" using `v : values` `valid \<Gamma>` Add1
    by (induct v rule: values.induct) (auto simp add: ty.inject)
  then obtain eff' where b:"\<Gamma> \<turnstile> u : T1 ; eff'" by auto
  have "simple_eff eff'" using delta_closed[of Add1 v u] closed_eff b Add1 by auto
  hence c:"\<turnstile> eff' <e: eff" using a simple_eff_below_ne by auto 
  from b c show ?case by auto
next
  case Nott
  hence a:"eff = NE" using nott_eff_ne[of \<Gamma> v T1 eff] by auto
  have "EX  eff'. \<Gamma> \<turnstile> u : T1 ; eff'" using `v : values` `valid \<Gamma>` Nott
  proof (induct v rule: values.induct) 
    case (bool_value b)
    thus ?case by (cases b) (auto simp add: ty.inject)
  qed (auto)
  then obtain eff' where b:"\<Gamma> \<turnstile> u : T1 ; eff'" by auto
  have "simple_eff eff'" using delta_closed[of Nott v u] closed_eff b Nott by auto
  hence c:"\<turnstile> eff' <e: eff" using a simple_eff_below_ne by auto 
  from b c show ?case by auto
next
  case BooleanP
  have "T1 = ty.Bool" using BooleanP by (simp add: ty.inject)
  then obtain bb where "\<Delta> BooleanP v = Some (Bool bb)" by (nominal_induct v rule: trm.induct) (auto)
  then obtain eff' where a:"\<Gamma> \<turnstile> u : T1 ; eff'" using `T1 = ty.Bool` BooleanP by (cases bb) (auto simp add: trm.inject)
  have c:"simple_eff eff'" using delta_closed[of BooleanP v u] closed_eff prems by auto  
  have b:"simple_eff eff" using BooleanP booleanp_eff_simple by auto
  hence "\<turnstile> eff' <e: eff" using b prems
  proof (induct rule: simple_eff_cases)
    case NE thus ?case using simple_eff_below_ne c by auto
  next
    case FF
    hence "u = Bool False" 
      using booleanp_FF_preserved  `v : values`  `\<Gamma> \<turnstile> App (BI BooleanP) v : T1 ; eff` `\<Delta> BooleanP v = Some u` by auto
    hence "eff'= FF" using a false_ty_elim by auto
    thus ?case using FF by auto
  next
    case TT
    hence "u = Bool True" 
      using booleanp_TT_preserved  `v : values`  `\<Gamma> \<turnstile> App (BI BooleanP) v : T1 ; eff` `\<Delta> BooleanP v = Some u` by auto
    hence "eff'= TT" using a true_ty_elim by auto
    thus ?case using TT by auto
  qed
  thus ?case using a by auto
next
  case NumberP
  have "T1 = ty.Bool" using NumberP by (simp add: ty.inject)
  then obtain bb where "\<Delta> NumberP v = Some (Bool bb)" by (nominal_induct v rule: trm.induct) (auto)
  then obtain eff' where a:"\<Gamma> \<turnstile> u : T1 ; eff'" using `T1 = ty.Bool` NumberP by (cases bb) (auto simp add: trm.inject)
  have c:"simple_eff eff'" using delta_closed[of NumberP v u] closed_eff prems by auto  
  have b:"simple_eff eff" using NumberP numberp_eff_simple by auto
  hence "\<turnstile> eff' <e: eff" using b prems
  proof (induct rule: simple_eff_cases)
    case NE thus ?case using c simple_eff_below_ne by auto
  next
    case FF
    hence "u = Bool False" 
      using numberp_FF_preserved  `v : values`  `\<Gamma> \<turnstile> App (BI NumberP) v : T1 ; eff` `\<Delta> NumberP v = Some u` by auto
    hence "eff'= FF" using a false_ty_elim by auto
    thus ?case using FF by auto
  next
    case TT
    hence "u = Bool True" 
      using numberp_TT_preserved  `v : values`  `\<Gamma> \<turnstile> App (BI NumberP) v : T1 ; eff` `\<Delta> NumberP v = Some u` by auto
    hence "eff'= TT" using a true_ty_elim by auto
    thus ?case using TT by auto
  qed
  thus ?case using a by auto
qed

lemma simple_eff_below_ve:
  assumes "simple_eff F"
  shows "\<turnstile> F <e: VE x"
  using prems
  by (induct F rule: simple_eff_cases) auto

lemma below_ne_simple:
  assumes "\<turnstile> F <e: G" and "G = NE"
  shows "simple_eff F"
  using prems no_sub_TT no_sub_FF
  by induct auto

lemma below_ve_simple:
  assumes "\<turnstile> F <e: G" and "G = VE x"
  shows "simple_eff F \<or> F = VE x"
  using prems
  by induct auto

consts
  remove_env  :: "'a list => 'a => 'a list" ("_ - _" [100,100] 100)

primrec
  "[] - x = []"
  "(y#xs) - x = (if x=y then (xs - x) else y#(xs - x))"

lemma fresh_remove:
  fixes a::"name"
  and   \<Gamma>::"(name\<times>ty) list"
  assumes a: "a\<sharp>\<Gamma>"
  shows "a\<sharp>(\<Gamma> - (x,T))"
using a
by (induct \<Gamma>) (auto simp add: fresh_list_cons)

lemma valid_remove:
  fixes pair::"name\<times>ty"
  assumes a: "valid \<Gamma>"
  shows "valid (\<Gamma> - (x,T))"
using a
by (induct \<Gamma>) (auto simp add: fresh_remove)

lemma set_remove:
  assumes a: "(a,T)\<in>set \<Gamma>"
  and     b: "a\<noteq>x"
  shows "(a,T)\<in>set (\<Gamma> - (x,T'))"
using a b
by (induct \<Gamma>) (auto)

lemma closed_elim:"closed e \<Longrightarrow> (supp e = ({}::name set))" using closed_def by auto

lemma set_remove_comm:
  shows "set (l - a) = (set l) - {a}"
  by (induct l) auto


lemma envplus_set:
  shows "set (\<Gamma> |+ TE T x) = (mapfun restrict T x) ` set \<Gamma>"
proof -
  have A:"!! a b. a = b \<Longrightarrow> set a = set b" by auto
  have "\<Gamma> |+ TE T x = map (mapfun restrict T x) \<Gamma>" by auto
  hence "set (\<Gamma> |+ TE T x) = set (map (mapfun restrict T x) \<Gamma>)" 
    using A[of "(\<Gamma> |+ TE T x)" "map (mapfun restrict T x) \<Gamma>"] by auto
  also have "\<dots> = (mapfun restrict T x) ` set \<Gamma>" by auto
  ultimately show ?thesis by auto
qed

lemma envminus_set:
  shows "set (\<Gamma> |- TE T x) = (mapfun remove T x) ` set \<Gamma>"
proof -
  have A:"!! a b. a = b \<Longrightarrow> set a = set b" by auto
  have "\<Gamma> |- TE T x = map (mapfun remove T x) \<Gamma>" by auto
  hence "set (\<Gamma> |- TE T x) = set (map (mapfun remove T x) \<Gamma>)" 
    using A[of "(\<Gamma> |- TE T x)" "map (mapfun remove T x) \<Gamma>"] by auto
  also have "\<dots> = (mapfun remove T x) ` set \<Gamma>" by auto
  ultimately show ?thesis by auto
qed

lemma fresh_weakening:
  assumes a:"x\<sharp>e" and b:"\<Gamma> \<turnstile> e : T ; F" and c: "valid \<Gamma>" 
  shows "(\<Gamma> - (x,T')) \<turnstile> e : T ; F"
  using b a c 
proof (nominal_induct \<Gamma> e T F avoiding: x T'  rule: typing_induct)
  case T_Var thus ?case
    by(force simp add: fresh_atm abs_fresh set_remove valid_remove fresh_remove)+
next
  case (T_App \<Gamma>' _ _ t1 t2) thus ?case
    by(force simp add: fresh_atm abs_fresh set_remove valid_remove fresh_remove)
next
  case T_Lam thus ?case
    by(force simp add: fresh_atm abs_fresh set_remove valid_remove fresh_remove)+
next
  case T_AppPred thus ?case
    by(force simp add: fresh_atm abs_fresh set_remove valid_remove fresh_remove)+
next
  case T_IfTrue thus ?case
    by(force simp add: fresh_atm abs_fresh set_remove valid_remove fresh_remove)+
next
  case T_IfFalse thus ?case
    by(force simp add: fresh_atm abs_fresh set_remove valid_remove fresh_remove)+
next
  case T_True thus ?case
    by(force simp add: fresh_atm abs_fresh set_remove valid_remove fresh_remove)+
next
  case T_False thus ?case
    by(force simp add: fresh_atm abs_fresh set_remove valid_remove fresh_remove)+
next
  case T_Num thus ?case
    by(force simp add: fresh_atm abs_fresh set_remove valid_remove fresh_remove)+
next
  case T_Const thus ?case
    by(force simp add: fresh_atm abs_fresh set_remove valid_remove fresh_remove)+
next
  case (T_AppPredTrue \<Gamma>' e1 e2 T1 T2 T0 S F1 F2 x T')
  have A:"x \<sharp> e1" "x \<sharp> e2" using T_AppPredTrue by auto
  hence "\<Gamma>' - (x,T') \<turnstile> e1 : T1 \<rightarrow> T2 : Latent S ; F1" using T_AppPredTrue by auto
  also have "\<Gamma>' - (x,T') \<turnstile> e2 : T0 ; F2" using T_AppPredTrue A by auto
  ultimately show ?case using `\<turnstile> T0 <: S` `\<turnstile> T0 <: T1` by auto
next
  case (T_AppPredFalse \<Gamma>' e1 e2 T1 T2 T0 S F1 F2 x T')
  have A:"x \<sharp> e1" "x \<sharp> e2" using T_AppPredFalse by auto
  hence "\<Gamma>' - (x,T') \<turnstile> e1 : T1 \<rightarrow> T2 : Latent S ; F1" using T_AppPredFalse by auto
  also have "\<Gamma>' - (x,T') \<turnstile> e2 : T0 ; F2" using T_AppPredFalse A by auto
  ultimately show ?case using `~ (\<turnstile> T0 <: S)` `\<turnstile> T0 <: T1` `e2 : values` `closed e2` by auto
next
  case (T_If \<Gamma>' e1 e2 e3 T1 T2 T3 T F1 F2 F3 x)
  have A:"x \<sharp> e1" "x \<sharp> e2" "x \<sharp> e3" using T_If by auto
  have "\<Gamma>' - (x,T') \<turnstile> e1 : T1 ; F1" using T_If A by auto
  thus ?case using T_If
    proof (nominal_induct F1 rule: eff.induct)
      case NE
      from NE have 1:"\<Gamma>' - (x, T') \<turnstile> e1 : T1 ; eff.NE" by auto
      from NE have 2:"(\<Gamma>' - (x, T') |+ eff.NE) \<turnstile> e2 : T2 ; F2" by auto
      from NE have 3:"(\<Gamma>' - (x, T') |- eff.NE) \<turnstile> e3 : T3 ; F3" by auto
      from 1 2 3 show ?case using `\<turnstile> T2 <: T` `\<turnstile> T3 <: T` by auto
    next
      case TT
      from TT have 1:"\<Gamma>' - (x, T') \<turnstile> e1 : T1 ; eff.TT" by auto
      from TT have 2:"(\<Gamma>' - (x, T') |+ eff.TT) \<turnstile> e2 : T2 ; F2" by auto
      from 1 2 show ?case using `\<turnstile> T2 <: T` by auto
    next
      case FF
      from FF have 1:"\<Gamma>' - (x, T') \<turnstile> e1 : T1 ; eff.FF" by auto
      from FF have 3:"(\<Gamma>' - (x, T') |+ eff.FF) \<turnstile> e3 : T3 ; F3" by auto
      from 1 3 show ?case using `\<turnstile> T3 <: T` by auto
    next
      case (VE z)
      from VE have 1:"\<Gamma>' - (x, T') \<turnstile> e1 : T1 ; VE z" by auto
      from VE have 2:"(\<Gamma>' - (x, T') |+ eff.VE z) \<turnstile> e2 : T2 ; F2" by auto
      from VE have 3:"(\<Gamma>' - (x, T') |- eff.VE z) \<turnstile> e3 : T3 ; F3" by auto
      from 1 2 3 show ?case using `\<turnstile> T2 <: T` `\<turnstile> T3 <: T` by auto
    next
      case (TE U z)
      from TE have 1:"\<Gamma>' - (x, T') \<turnstile> e1 : T1 ; TE U z" by auto
      have val1:"valid (\<Gamma>' |+ TE U z)" using TE envplus_valid[of \<Gamma>' "TE U z"] by auto
      have val2:"valid (\<Gamma>' |- TE U z)" using TE envminus_valid[of \<Gamma>' "TE U z"] by auto
      have "valid (\<Gamma>' |- TE U z)" using TE envminus_valid[of \<Gamma>' "TE U z"] by auto
      have A0:"!!T0 . (\<Gamma>' |- TE U z) - (x, T0) \<turnstile> e3 : T3 ; F3" using TE(7) A `valid (\<Gamma>' |- TE U z)` by auto

      have A:"!!T0 . (\<Gamma>' |+ TE U z) - (x, T0) \<turnstile> e2 : T2 ; F2" using TE(5) A `valid (\<Gamma>' |+ TE U z)` by auto
      let ?op = "remove"
      let ?mapfun = "(% (v,ty). (if (x = v) then (v,?op S ty) else (v,ty)))"
      have B:"!! p. set ((\<Gamma>' |+ TE U z) - p) = ((mapfun restrict U z) ` (set \<Gamma>')) - {p}" 
	using envplus_set[of \<Gamma>' U z] set_remove_comm[of "(\<Gamma>' |+ TE U z)"] by auto
      have image_lem:"!! f S v. (f ` S) - {(f v)} <= (f ` (S - {v}))" by auto
      note image_lem[of "mapfun restrict U z" "set \<Gamma>'" "(x,T0)"]
      
      have eq1:"!! p. mapfun restrict U z ` set \<Gamma>' - {mapfun restrict U z p} = set ((\<Gamma>' |+ TE U z) - (mapfun restrict U z p))" using envplus_set[of \<Gamma>' U z] set_remove_comm[of "(\<Gamma>' |+ TE U z)"] by auto

      have eq2:"!! p. mapfun restrict U z ` (set \<Gamma>' - {p}) = set (\<Gamma>' - p |+ TE U z)"
      proof -
	fix p
	show "mapfun restrict U z ` (set \<Gamma>' - {p}) = set (\<Gamma>' - p |+ TE U z)"
	  using envplus_set[of "\<Gamma>' - p" U z] set_remove_comm[of \<Gamma>'] by auto
      qed
      have eq3:"!! x T0. mapfun restrict U z (x,T0) = (x, (if (x = z) then (restrict U T0) else (T0)))" by auto
      let ?restrictT' = "(if (x = z) then (restrict U T') else (T'))"
      have goal:"((\<Gamma>' |+ TE U z) - (x,?restrictT')) \<lless> ((\<Gamma>' - (x,T')) |+ TE U z)"
      proof -
	have " mapfun restrict U z ` set \<Gamma>' - {mapfun restrict U z (x,T')} <= 
	  mapfun restrict U z ` (set \<Gamma>' - {(x,T')})" using  image_lem[of "mapfun restrict U z" "set \<Gamma>'" "(x,T')"] by auto
	hence " mapfun restrict U z ` set \<Gamma>' - {mapfun restrict U z (x,T')} <= 
	  set ((\<Gamma>' - ((x,T'))) |+ TE U z)" using eq2[of " (x, T')"] by auto
	hence "set ((\<Gamma>' |+ TE U z) - (mapfun restrict U z (x,T'))) <= 
	  set ((\<Gamma>' - ((x,T'))) |+ TE U z)" 
	  using eq1[of "(x,T')"] by auto
	hence "set ((\<Gamma>' |+ TE U z) - (x,?restrictT')) <= set ((\<Gamma>' - (x,T')) |+ TE U z)" using eq3 by auto
	thus ?thesis by auto
      qed
      have val3:"valid ((\<Gamma>' |+ TE U z) - (x,?restrictT'))" using val1 valid_remove by auto
      have "valid ((\<Gamma>' - (x, T')))" using `valid \<Gamma>'` valid_remove envplus_valid by auto
      hence val4:"valid ((\<Gamma>' - (x, T')) |+ TE U z)" using  envplus_valid[of "\<Gamma>' - (x, T')" "TE U z"] by auto
      from  A have "(\<Gamma>' |+ TE U z) - (x,?restrictT') \<turnstile>  e2 : T2 ; F2" by auto
      hence 2:"(\<Gamma>' - (x, T')) |+ TE U z \<turnstile> e2 : T2 ; F2" using goal val3 val4
	weakening[of  "(\<Gamma>' |+ TE U z) - (x,?restrictT')" e2 T2 F2 "\<Gamma>' - (x,T') |+ TE U z"] by auto

      have eq4:"!! p. mapfun remove U z ` set \<Gamma>' - {mapfun remove U z p} = set ((\<Gamma>' |- TE U z) - (mapfun remove U z p))" using envminus_set[of \<Gamma>' U z] set_remove_comm[of "(\<Gamma>' |- TE U z)"] by auto

      have eq5:"!! p. mapfun remove U z ` (set \<Gamma>' - {p}) = set (\<Gamma>' - p |- TE U z)"
      proof -
	fix p
	show "mapfun remove U z ` (set \<Gamma>' - {p}) = set (\<Gamma>' - p |- TE U z)"
	  using envminus_set[of "\<Gamma>' - p" U z] set_remove_comm[of \<Gamma>'] by auto
      qed
      have eq6:"!! x T0. mapfun remove U z (x,T0) = (x, (if (x = z) then (remove U T0) else (T0)))" by auto
      let ?removeT' = "(if (x = z) then (remove U T') else (T'))"
      have goal':"((\<Gamma>' |- TE U z) - (x,?removeT')) \<lless> ((\<Gamma>' - (x,T')) |- TE U z)"
      proof -
	have " mapfun remove U z ` set \<Gamma>' - {mapfun remove U z (x,T')} <= 
	  mapfun remove U z ` (set \<Gamma>' - {(x,T')})" using  image_lem[of "mapfun remove U z" "set \<Gamma>'" "(x,T')"] by auto
	hence " mapfun remove U z ` set \<Gamma>' - {mapfun remove U z (x,T')} <= 
	  set ((\<Gamma>' - ((x,T'))) |- TE U z)" using eq5[of " (x, T')"] by auto
	hence "set ((\<Gamma>' |- TE U z) - (mapfun remove U z (x,T'))) <= 
	  set ((\<Gamma>' - ((x,T'))) |- TE U z)" 
	  using eq4[of "(x,T')"] by auto
	hence "set ((\<Gamma>' |- TE U z) - (x,?removeT')) <= set ((\<Gamma>' - (x,T')) |- TE U z)" using eq6 by auto
	thus ?thesis by auto
      qed
      have val5:"valid ((\<Gamma>' |- TE U z) - (x,?removeT'))" using val2 valid_remove by auto
      have "valid ((\<Gamma>' - (x, T')))" using `valid \<Gamma>'` valid_remove envminus_valid by auto
      hence val6:"valid ((\<Gamma>' - (x, T')) |- TE U z)" using  envminus_valid[of "\<Gamma>' - (x, T')" "TE U z"] by auto
      from  A0 have "(\<Gamma>' |- TE U z) - (x,?removeT') \<turnstile>  e3 : T3 ; F3" by auto
      hence 3:"(\<Gamma>' - (x, T')) |- TE U z \<turnstile> e3 : T3 ; F3" using goal' val5 val6
	weakening[of  "(\<Gamma>' |- TE U z) - (x,?removeT')" e3 T3 F3 "\<Gamma>' - (x,T') |- TE U z"] by auto
      from 1 2 3 show ?thesis using `\<turnstile> T2 <: T` `\<turnstile> T3 <: T` by auto
    qed
  qed

thm wf_induct

lemma fresh_weakening_cons:
  assumes "valid ((a,S)#\<Gamma>)" (is "valid ?\<Gamma>") and "(a,S)# \<Gamma> \<turnstile> e : T ; F" and "a \<sharp> e"
  shows "\<Gamma> \<turnstile> e : T ; F"
  proof -
    have v1:"valid \<Gamma>" using prems valid_elim by blast
    hence v2:"valid (\<Gamma> - (a,S))" using valid_remove by auto
    have A:"?\<Gamma> - (a,S) \<turnstile> e : T ; F" using prems fresh_weakening[of a e ?\<Gamma> T F S] by auto
    have "?\<Gamma> - (a,S) = \<Gamma> - (a,S)" by auto
    hence B:"\<Gamma> - (a,S)  \<lless> \<Gamma>" by (induct \<Gamma>) auto
    thus ?thesis using A weakening[of _ e T F \<Gamma>] v1 v2 by auto
  qed
    

lemma closed_empty_env:
  assumes "closed e" and "\<Gamma> \<turnstile> e : T ; F" and "valid \<Gamma>"
  shows "[] \<turnstile> e : T ; F"
  using `valid \<Gamma>` prems
  proof (induct \<Gamma> rule: valid.induct)
    case v1 thus ?case by simp
  next
    case (v2 \<Gamma>' a S)
    have "a \<sharp> e" using `closed e` closed_def fresh_def[of a e] by auto
    thus ?case using v2 fresh_weakening_cons by auto
  qed



lemma closed_any_env:
  assumes "closed e" and "\<Gamma> \<turnstile> e : T ; F" and val1:"valid \<Gamma>" and val2:"valid \<Gamma>'"
  shows "\<Gamma>' \<turnstile> e : T ; F"
  using prems closed_empty_env weakening 
  proof -
    have A:"[] \<turnstile> e : T ; F" using prems closed_empty_env by auto
    note weakening
    have B:"[] \<lless> \<Gamma>'" by auto
    from A B val1 val2 have "\<Gamma>' \<turnstile> e : T ; F" using weakening by blast
    thus ?thesis by simp
  qed    

inductive_cases2 ve_ty_elim: "\<Gamma> \<turnstile> e : T ; VE x"  
thm ve_ty_elim

lemma te_ty_elim: 
 "\<Gamma> \<turnstile> t1 : T ; TE U z \<Longrightarrow>
  EX f A A1 Fn. t1 = (App f (Var z)) \<and> \<Gamma> \<turnstile> f : A1 \<rightarrow> T : Latent U ; Fn \<and> 
  \<Gamma> \<turnstile> (Var z) : A ; VE z \<and> \<turnstile> A <: A1 "
  proof (ind_cases2 "\<Gamma> \<turnstile> t1 : T ; TE U z")
    fix e1 T0 eff1 e2 Ta x S
    assume "t1 = App e1 e2" "TE U z = TE S x"
      "\<Gamma> \<turnstile> e1 : T0 \<rightarrow> T : Latent S ; eff1 "" \<Gamma> \<turnstile> e2 : Ta ; VE x "
      "\<turnstile> Ta <: T0"
    from prems have A:"e2 = Var x" using ve_ty_elim[of \<Gamma> e2 Ta x]  eff.inject by auto
    hence B:"t1 = App e1 (Var z)" using prems trm.inject eff.inject by auto
    have C:" \<Gamma> \<turnstile> (Var z) : Ta ; VE z" using prems A trm.inject eff.inject by auto
    have D:" \<Gamma> \<turnstile> e1 : T0 \<rightarrow> T : Latent U ; eff1" using ty.inject latent_eff.inject prems eff.inject by auto
    from `\<turnstile> Ta <: T0` B C D show ?thesis by auto
  qed
    
  

lemma unique_var_typing:
  assumes  "(x,T)#\<Gamma> \<turnstile> Var x : T; VE x" and "(x,T)#\<Gamma> \<turnstile> Var x : T' ; VE x"
  shows "T = T'"
  proof (rule ccontr)
    assume "T ~= T'"
    have "(x,T) : set ((x,T)#\<Gamma>)" using var_ty_elim[of _ x T "VE x"] prems by auto
    have "(x,T') : set ((x,T)#\<Gamma>)" "valid ((x,T)#\<Gamma>)" using var_ty_elim[of "((x,T)#\<Gamma>)" x T' "VE x"] prems by auto
    hence A:"(x,T') : set \<Gamma>" "valid \<Gamma>" "x \<sharp> \<Gamma>" using prems valid_elim[of x T \<Gamma>] by auto
    have "x : supp \<Gamma>" using `valid \<Gamma>` A
    proof (induct \<Gamma> rule: valid.induct)
      case v1 thus ?case by auto
    next
      case (v2 \<Gamma>' a S) 
      hence "x \<sharp> (a,S)" "x \<sharp> \<Gamma>'" using fresh_list_cons by auto
      hence "x \<sharp> a" by auto
      hence "x ~= a" using fresh_atm by auto
      hence "(x,T') : set \<Gamma>'" using v2 by auto
      have "valid \<Gamma>'" using v2 valid_elim[of a S \<Gamma>'] by auto
      hence "x : supp \<Gamma>'" using v2 `(x,T') : set \<Gamma>'` `x \<sharp> \<Gamma>'` by auto
      hence "x : supp (a,S)  \<union> supp \<Gamma>'" by auto
      hence "x : (supp ((a,S)#\<Gamma>') :: name set)" using supp_list_cons[of "(a,S)" \<Gamma>'] by force
      thus ?case by simp 
    qed
    hence "~ (x \<sharp> \<Gamma>)" using fresh_def[of x \<Gamma>] by blast
    thus False using `x \<sharp> \<Gamma>` by auto
  qed

(* this is the key lemma in the whole soundness proof *)        
lemma reduce_remove_soundness:
  assumes "\<Gamma> \<turnstile> v : T0 ; F" and "v : values" and "\<turnstile> T0 <: T" 
  shows
  "(\<turnstile> T0 <: S \<and> \<turnstile> T0 <: restrict S T) \<or>
  (~ (\<turnstile> T0 <: S) \<and> \<turnstile> T0 <: remove S T)"
proof -
  {
    assume "\<turnstile> T0 <: S"
    hence "\<turnstile> T0 <: restrict S T" using `\<turnstile> T0 <: T` by (cases "\<turnstile> S <: T") (auto simp add: restrict_def)
    hence "\<turnstile> T0 <: S \<and> \<turnstile> T0 <: restrict S T" using prems by simp
    hence ?thesis by simp
  }
  moreover
  {
    assume A:"~ (\<turnstile> T0 <: S)" 
    have " \<turnstile> T0 <: remove S T" using `\<turnstile> T0 <: T` remove_def by auto
    hence ?thesis using A by simp
  }
  ultimately show ?thesis by auto
qed



text {*
old
  have B:"T0 = ty.Int \<or> T0 = ty.Bool \<or> (EX A1 A2 L. T0 = A1 \<rightarrow> A2 : L)"
    using `v:values` prems
    proof (nominal_induct v avoiding: \<Gamma> rule: values_induct)
      case (abs_value x T b)
      note abs_ty_elim[of \<Gamma> x b T T0 F] abs_value
      hence "EX T1. T0 = T \<rightarrow> T1 : latent_eff.NE" by auto
      thus ?case by auto
    next
      case (bi_value b)
      note bi_ty_elim[of \<Gamma> b T0 F]
      hence "T0 =  \<Delta>\<^isub>\<tau> b" using bi_value by auto
      thus ?case
        by (nominal_induct b rule: builtin.induct) auto
    next      
      case (num_value n)
      thus ?case using num_ty_elim by auto
    next      
      case (bool_value b)
      thus ?case using true_ty_elim false_ty_elim by (cases b) auto
    qed
    fix le :: latent_eff
    have "True \<and> ?thesis"
    proof (nominal_induct S rule: latent_eff_ty.induct)
      case NE thus ?case by simp
    next
      case Latent thus ?case by simp
    next
      case Top
      have "\<turnstile> T0 <: Top" by auto
      also have " \<turnstile> T0 <: restrict Top T" using restrict_def by auto
      ultimately show ?case by auto
    next
      case Int
      thus ?case
	proof (cases "T0 = ty.Int")
	  case True
	  hence "\<turnstile> T0 <: restrict ty.Int T" using `\<turnstile> T0 <: T` restrict_def by auto
	  also have "\<turnstile> T0 <: remove ty.Int T" using `\<turnstile> T0 <: T` remove_def by auto
	  ultimately show ?thesis by auto
	next
	  have "\<turnstile> T0 <: remove ty.Int T" using `\<turnstile> T0 <: T` remove_def by auto
	  also have "~ (overlap ty.Int T0)"
	    proof (rule ccontr)
	      assume " \<not> \<not> (overlap ty.Int T0)"
	      hence "overlap ty.Int T0" by simp
	      then obtain U where "\<turnstile> U <: ty.Int" "\<turnstile> U <: T0" by cases auto
	      hence "U = ty.Int" using no_sub_int by auto
	      
	  ultimately show ?thesis by auto

	  

 thus ?thesis using `\<turnstile> T0 <: T`by auto

using `\<turnstile> T0 <: T` by auto
      
  proof -
    {
      assume "\<turnstile> T0 <: S"
      hence "\<turnstile> T0 <: restrict S T" using restrict_def by auto
      hence ?thesis using prems by auto
    }
    moreover
    {
      assume "~ (\<turnstile> T0 <: S)" "S = ty.Int"
        (*
        proof idea:
        S has no subtypes, so if there's an overlap between S and T0, T0
        must be a supertype of S.  But consider cases on T0.  It must be either
        an arrow type (if v = Abs or v = BI), and then S is not a subtype.
        Or it is Bool, and then S is not a subtype.  Or it is Int, and then
        \<turnstile> T0 <: S since S = T0, which contradicts the assumption.
        *)
      have "~ overlap S T0"
      proof (rule ccontr)          
        assume "~ ~ (overlap S T0)"
        hence "(overlap S T0)" by auto
        hence "EX U. \<turnstile> U <: S \<and> \<turnstile> U <: T0" using overlap.cases[of S T0] by auto
        then obtain U where "\<turnstile> U <: S "" \<turnstile> U <: T0" by auto
        hence "U = ty.Int" using no_sub_int `S = ty.Int` by blast
        thus False
          proof -
            {
              assume "T0 = ty.Int"
              hence "\<turnstile> T0 <: S" using `S = ty.Int` by auto
              hence False using prems by auto
            }
            moreover
            {
              assume "T0 = ty.Bool"
              hence "U = ty.Bool" using ` \<turnstile> U <: T0` no_sub_bool by blast
              hence False using `U = ty.Int` ty.distinct by auto
            }
            moreover
            {
              assume "EX A1 A2 L. T0 = A1 \<rightarrow> A2 : L"
              then obtain A1 A2 L where "T0 = A1 \<rightarrow> A2 : L" by auto
              hence "EX A1' A2'. U = A1' \<rightarrow> A2' : L" using ` \<turnstile> U <: T0` subtype_arr_elim[of U T0 A1 A2 L] by auto
              hence False using `U = ty.Int` ty.distinct by auto
            }
            ultimately show False using B by auto
          qed
      qed
      hence ?thesis using prems A by auto
    }
    moreover
    {
      assume "~ (\<turnstile> T0 <: S)" "S = ty.Bool"
        (*
        proof idea:
        S has no subtypes, so if there's an overlap between S and T0, T0
        must be a supertype of S.  But consider cases on T0.  It must be either
        an arrow type (if v = Abs or v = BI), and then S is not a subtype.
        Or it is Bool, and then S is not a subtype.  Or it is Int, and then
        \<turnstile> T0 <: S since S = T0, which contradicts the assumption.
        *)
      have "~ overlap S T0"
      proof (rule ccontr)          
        assume "~ ~ (overlap S T0)"
        hence "(overlap S T0)" by auto
        hence "EX U. \<turnstile> U <: S \<and> \<turnstile> U <: T0" using overlap.cases[of S T0] by auto
        then obtain U where "\<turnstile> U <: S "" \<turnstile> U <: T0" by auto
        hence "U = ty.Bool" using no_sub_bool `S = ty.Bool` by blast
        thus False
          proof -
            {
              assume "T0 = ty.Bool"
              hence "\<turnstile> T0 <: S" using `S = ty.Bool` by auto
              hence False using prems by auto
            }
            moreover
            {
              assume "T0 = ty.Int"
              hence "U = ty.Int" using ` \<turnstile> U <: T0` no_sub_int by blast
              hence False using `U = ty.Bool` ty.distinct by auto
            }
            moreover
            {
              assume "EX A1 A2 L. T0 = A1 \<rightarrow> A2 : L"
              then obtain A1 A2 L where "T0 = A1 \<rightarrow> A2 : L" by auto
              hence "EX A1' A2'. U = A1' \<rightarrow> A2' : L" using ` \<turnstile> U <: T0` subtype_arr_elim[of U T0 A1 A2 L] by auto
              hence False using `U = ty.Bool` ty.distinct by auto
            }
            ultimately show False using B by auto
          qed
      qed
      hence ?thesis using prems A by auto
    }
    ultimately show ?thesis using prems by auto
  qed
qed
            
  
*}
        
    
    

lemma preserve_subst:
  assumes "(x,T0)#\<Gamma> \<turnstile> e : T ; F" and "\<Gamma> \<turnstile> e' : T1 ; G" and "\<turnstile> T1 <: T0" and "valid ((x,T0)#\<Gamma>)" and "closed e'" and "e' : values"
  shows "EX T' F'. \<Gamma> \<turnstile> e[x::=e'] : T' ; F' \<and> \<turnstile> T' <: T \<and> \<turnstile> F' <e: F"
  using prems
proof (nominal_induct e avoiding: \<Gamma> x e' T T1 T0 F G rule: trm_comp_induct)
  case (Var v)
  have a1: "\<Gamma> \<turnstile>e':T1;G" by fact
  have a2: "((x,T0)#\<Gamma>) \<turnstile> Var v:T;F" by fact
  hence a21: "(v,T)\<in>set((x,T0)#\<Gamma>)" and a22: "valid((x,T0)#\<Gamma>)" and a22b:"F = VE v"
    using var_ty_elim[of "(x, T0) # \<Gamma>"] by auto
  from a22 have a23: "valid \<Gamma>" and a24: "x\<sharp>\<Gamma>" by (auto dest: valid_elim) 
  from a24 have a25: "\<not>(\<exists>\<tau>. (x,\<tau>)\<in>set \<Gamma>)" by (rule fresh_context)
  show "EX T' F'. \<Gamma>\<turnstile>(Var v)[x::=e'] : T'; F' \<and>  \<turnstile> T' <: T \<and> \<turnstile> F' <e: F"
  proof (cases "v=x")
    assume case1: "v=x"
    hence "(Var v)[x::=e'] = e'" by simp
    hence A:"\<Gamma> \<turnstile> (Var v)[x::=e'] : T1; G" using Var by auto
    have "simple_eff G" using closed_eff `closed e'` prems by auto
    hence C:"\<turnstile> G <e: F" using a22b simple_eff_below_ve by auto
    have B:"T = T0"
    proof (rule ccontr)
      assume a3:"T ~= T0"
      from a3 a21 have "(v,T)\<in>set \<Gamma>" by force
      with case1 a25 show False by force 
    qed
    hence "\<turnstile> T1 <: T" using  `\<turnstile> T1 <: T0` by auto
    thus "EX T' F'. \<Gamma> \<turnstile> (Var v)[x::=e'] : T'; F' \<and>  \<turnstile> T' <: T \<and> \<turnstile> F' <e: F" using A a22b C by blast
  next
    assume case2: "v\<noteq>x"
    with a21 have a26: "(v,T)\<in>set \<Gamma>" by force
    have a27:" Var v[x::=e'] = Var v" using case2 by simp
    from a23 a26 a27 have "\<Gamma> \<turnstile> Var v:T;VE v" by force
    thus ?thesis using a27 a22b by auto
  qed
next
  case (Num n)
  have A:"(Num n)[x::=e'] = Num n" by auto
  have B:"F = eff.NE" using Num num_ty_elim by auto
  have "T = ty.Int" using num_ty_elim Num by auto
  hence "\<Gamma> \<turnstile> (Num n)[x::=e'] : T ; eff.NE" using Num A valid_elim[of x T0 \<Gamma>] by auto
  thus ?case using Num B by auto
next
  case (Bool b)
  have A:"(Bool b)[x::=e'] = Bool b" by auto
  have "T = ty.Bool" using true_ty_elim false_ty_elim Bool by (cases b) auto
  hence "EX Fn. \<Gamma> \<turnstile> (Bool b)[x::=e'] : T ; Fn" using Bool A valid_elim[of x T0 \<Gamma>] by (cases b) auto
  then obtain Fn where B:"\<Gamma> \<turnstile> (Bool b)[x::=e'] : T ; Fn" by auto
  hence "Fn = F" using true_ty_elim false_ty_elim Bool A 
  proof (cases b)
    case True
    have "\<Gamma> \<turnstile> (Bool True)[x::=e'] : T ; Fn" using True B by auto
    hence "\<Gamma> \<turnstile> (Bool True) : T ; Fn" using A by auto
    hence "Fn = TT" using true_ty_elim by auto
    have  " (x, T0) # \<Gamma> \<turnstile> (Bool True) : T ; F" using A True Bool by auto
    hence "F = TT" using true_ty_elim by auto
    thus ?thesis using `Fn = TT` by simp
  next
    case False
    have "\<Gamma> \<turnstile> (Bool False)[x::=e'] : T ; Fn" using False B by auto
    hence "\<Gamma> \<turnstile> (Bool False) : T ; Fn" using A by auto
    hence "Fn = FF" using false_ty_elim by auto
    have  " (x, T0) # \<Gamma> \<turnstile> (Bool False) : T ; F" using A False Bool by auto
    hence "F = FF" using false_ty_elim by auto
    thus ?thesis using `Fn = FF` by simp
  qed
  thus ?case using Bool B by auto
next
  case (BI b)
  have A:"(BI b)[x::=e'] = (BI b)" by auto
  have B:"F = eff.NE" using BI bi_ty_elim by auto
  have "T = \<Delta>\<^isub>\<tau> b" using bi_ty_elim BI by auto
  hence "\<Gamma> \<turnstile> (BI b)[x::=e'] : T ; eff.NE" using BI A valid_elim[of x T0 \<Gamma>] by  auto
  thus ?case using BI B by auto
next
  case (App s1 s2 \<Gamma>' x' e'' T' T1' T0' F' G')
  have ih_s1: "\<And>c \<sigma> T F T' F' e' \<Gamma>. ((c,\<sigma>)#\<Gamma>) \<turnstile> s1:T; F \<Longrightarrow> closed e' \<Longrightarrow> e' : values \<Longrightarrow> valid ((c,\<sigma>)#\<Gamma>) \<Longrightarrow> \<Gamma>\<turnstile> e': T' ; F' \<Longrightarrow> \<turnstile> T' <: \<sigma> \<Longrightarrow> EX S G. \<Gamma> \<turnstile> s1[c::=e']:S ; G \<and> \<turnstile> S <: T \<and> \<turnstile> G <e: F" .
  have ih_s2: "\<And>c \<sigma> T F T' F' e' \<Gamma>. ((c,\<sigma>)#\<Gamma>) \<turnstile> s2:T; F \<Longrightarrow> closed e' \<Longrightarrow> e' : values \<Longrightarrow> valid ((c,\<sigma>)#\<Gamma>) \<Longrightarrow> \<Gamma>\<turnstile> e': T' ; F' \<Longrightarrow> \<turnstile> T' <: \<sigma> \<Longrightarrow> EX S G. \<Gamma> \<turnstile> s2[c::=e']:S ; G \<and> \<turnstile> S <: T \<and> \<turnstile> G <e: F" .
  have appty:"((x',T0')#\<Gamma>')\<turnstile>App s1 s2 : T'; F'" .
  from appty have
    elim1:"\<exists>T0 T0'a T1 le eff' eff''.(x',T0')#\<Gamma>' \<turnstile> s1 :T0\<rightarrow>T1:le;eff' \<and> (x',T0')# \<Gamma>'\<turnstile> s2 : T0'a;eff'' \<and> \<turnstile> T0'a <: T0 \<and> T1 = T'"
    using app_ty_elim by auto
  from appty 
  have elim2:"(x', T0') # \<Gamma>' \<turnstile> App s1 s2 : T' ; FF \<Longrightarrow> \<exists>T0 T0'a leS eff' eff''.(x',T0')#\<Gamma>' \<turnstile> s1 :T0\<rightarrow>T':Latent leS;eff' \<and> 
    (x',T0')# \<Gamma>'\<turnstile> s2 : T0'a;eff'' \<and> \<turnstile> T0'a <: T0  \<and> ~ (\<turnstile> T0'a <: leS) \<and> s2 : values \<and> closed s2"
    using app_ty_ff_elim[of "((x',T0')#\<Gamma>')" s1 s2 T'] by auto
  have elim3:"(x', T0') # \<Gamma>' \<turnstile> App s1 s2 : T' ; TT \<Longrightarrow> \<exists>T0 T0'a leS eff' eff''.(x',T0')#\<Gamma>' \<turnstile> s1 :T0\<rightarrow>T':Latent leS;eff' \<and> 
    (x',T0')# \<Gamma>'\<turnstile> s2 : T0'a;eff'' \<and> \<turnstile> T0'a <: T0  \<and> \<turnstile> T0'a <: leS " using app_ty_tt_elim[of "((x',T0')#\<Gamma>')" s1 s2 T'] by auto
  from elim1  obtain T0 T0'a T1 le eff' eff'' where
    P:"(x',T0')#\<Gamma>' \<turnstile> s1 :T0\<rightarrow>T1:le;eff'"" (x',T0')# \<Gamma>'\<turnstile> s2 : T0'a;eff''"" \<turnstile> T0'a <: T0 "" T1 = T'" by auto
  hence "EX S1 G1. \<Gamma>' \<turnstile> s1[x'::=e''] : S1 ; G1 \<and> \<turnstile> S1 <: (T0\<rightarrow>T1:le) \<and> \<turnstile> G1 <e: eff'" using ih_s1 App by auto
  then obtain S1 G1 where Q:" \<Gamma>' \<turnstile> s1[x'::=e''] : S1 ; G1 "" \<turnstile> S1 <: (T0\<rightarrow>T1:le)" "\<turnstile> G1 <e: eff'" by auto
  then obtain S10 S11 where R:"S1 = S10\<rightarrow>S11:le"" \<turnstile> T0 <: S10 "" \<turnstile> S11 <: T1"
    using subtype_arr_elim[of S1 "T0\<rightarrow>T1:le" T0 T1 le] by auto
  have "\<turnstile> T0'a <: S10" and "\<turnstile> S11 <: T'" using P R by auto
    (* then apply ih_s2, get something about the substition of s2, and put it all back together. *)
  from P have "EX S G. \<Gamma>' \<turnstile> s2[x'::=e'']:S ; G \<and> \<turnstile> S <: T0'a \<and> \<turnstile> G <e: eff''" using ih_s2[of x' T0' \<Gamma>' T0'a eff''] App by auto
  then obtain S2 G2 where S:"\<Gamma>' \<turnstile> s2[x'::=e'']:S2 ; G2 "" \<turnstile> S2 <: T0'a" "\<turnstile> G2 <e: eff''" by auto
  let ?ns1 = "s1[x'::=e'']" and ?ns2 = "s2[x'::=e'']"
  have sub:"\<turnstile> S2 <: S10" using ` \<turnstile> S2 <: T0'a` `\<turnstile> T0'a <: S10` by auto
  have L1:"\<Gamma>' \<turnstile> App ?ns1 ?ns2 : S11 ; NE" using Q R S sub by auto
  have L2:"\<turnstile> S11 <: T'" by fact
  show ?case using appty
  proof (nominal_induct F' rule: eff.induct)
    case NE thus ?case using L1 L2 by auto
  next
    case VE thus ?case using L1 L2 by auto
  next
    case TE thus ?case using L1 L2 by auto
  next
    case TT
    from elim3 TT  obtain T0 T0'a T1 le leS eff' eff'' where
      P:"(x',T0')#\<Gamma>' \<turnstile> s1 :T0\<rightarrow>T1:le;eff'"" (x',T0')# \<Gamma>'\<turnstile> s2 : T0'a;eff''"" \<turnstile> T0'a <: T0 "" T1 = T'"
      "le = Latent leS" "\<turnstile> T0'a <: leS" by auto
    hence "EX S1 G1. \<Gamma>' \<turnstile> s1[x'::=e''] : S1 ; G1 \<and> \<turnstile> S1 <: (T0\<rightarrow>T1:le) \<and> \<turnstile> G1 <e: eff'" using ih_s1 App by auto
    then obtain S1 G1 where Q:" \<Gamma>' \<turnstile> s1[x'::=e''] : S1 ; G1 "" \<turnstile> S1 <: (T0\<rightarrow>T1:le)" "\<turnstile> G1 <e: eff'" by auto
    then obtain S10 S11 where R:"S1 = S10\<rightarrow>S11:le"" \<turnstile> T0 <: S10 "" \<turnstile> S11 <: T1"
      using subtype_arr_elim[of S1 "T0\<rightarrow>T1:le" T0 T1 le] by auto
    have "\<turnstile> T0'a <: S10" and "\<turnstile> S11 <: T'" using P R by auto
      (* then apply ih_s2, get something about the substition of s2, and put it all back together. *)
    from P have "EX S G. \<Gamma>' \<turnstile> s2[x'::=e'']:S ; G \<and> \<turnstile> S <: T0'a \<and> \<turnstile> G <e: eff''" using ih_s2[of x' T0' \<Gamma>' T0'a eff''] App by auto
    then obtain S2 G2 where S:"\<Gamma>' \<turnstile> s2[x'::=e'']:S2 ; G2 "" \<turnstile> S2 <: T0'a" "\<turnstile> G2 <e: eff''" by auto
    let ?ns1 = "s1[x'::=e'']" and ?ns2 = "s2[x'::=e'']"
    have sub:"\<turnstile> S2 <: S10" using ` \<turnstile> S2 <: T0'a` `\<turnstile> T0'a <: S10` by auto
    have noover: "\<turnstile> S2 <: leS" using `\<turnstile> S2 <: T0'a` `\<turnstile> T0'a <: leS` by auto
    have L1:"\<Gamma>' \<turnstile> App ?ns1 ?ns2 : S11 ; TT" using P Q R S sub noover T_AppPredFalse[of \<Gamma>' " s1[x'::=e'']" T0 T1] by auto
    have L2:"\<turnstile> S11 <: T'" by fact
    from L1 L2 show ?case by auto
  next
    case FF
    from elim2 FF  obtain T0 T0'a T1 le leS eff' eff'' where
      P:"(x',T0')#\<Gamma>' \<turnstile> s1 :T0\<rightarrow>T1:le;eff'"" (x',T0')# \<Gamma>'\<turnstile> s2 : T0'a;eff''"" \<turnstile> T0'a <: T0 "" T1 = T'"
      "le = Latent leS" "~ (\<turnstile> T0'a <: leS)" "s2 :values" "closed s2" by auto
    hence "EX S1 G1. \<Gamma>' \<turnstile> s1[x'::=e''] : S1 ; G1 \<and> \<turnstile> S1 <: (T0\<rightarrow>T1:le) \<and> \<turnstile> G1 <e: eff'" using ih_s1 App by auto
    then obtain S1 G1 where Q:" \<Gamma>' \<turnstile> s1[x'::=e''] : S1 ; G1 "" \<turnstile> S1 <: (T0\<rightarrow>T1:le)" "\<turnstile> G1 <e: eff'" by auto
    then obtain S10 S11 where R:"S1 = S10\<rightarrow>S11:le"" \<turnstile> T0 <: S10 "" \<turnstile> S11 <: T1"
      using subtype_arr_elim[of S1 "T0\<rightarrow>T1:le" T0 T1 le] by auto
    have "\<turnstile> T0'a <: S10" and "\<turnstile> S11 <: T'" using P R by auto
      (* then apply ih_s2, get something about the substition of s2, and put it all back together. *)
    from P have "EX S G. \<Gamma>' \<turnstile> s2[x'::=e'']:S ; G \<and> \<turnstile> S <: T0'a \<and> \<turnstile> G <e: eff''" using ih_s2[of x' T0' \<Gamma>' T0'a eff''] App by auto
    then obtain S2 G2 where S:"\<Gamma>' \<turnstile> s2[x'::=e'']:S2 ; G2 "" \<turnstile> S2 <: T0'a" "\<turnstile> G2 <e: eff''" by auto
    let ?ns1 = "s1[x'::=e'']" and ?ns2 = "s2[x'::=e'']"
    have sub:"\<turnstile> S2 <: S10" using ` \<turnstile> S2 <: T0'a` `\<turnstile> T0'a <: S10` by auto
    have "x' \<sharp> s2" using closed_def fresh_def[of x' s2] `closed s2` by auto
    hence "s2 = ?ns2" using forget by auto
    hence S':"\<Gamma>' \<turnstile> ?ns2 : T0'a ; eff''" 
      using `(x',T0')#\<Gamma>' \<turnstile> s2 : T0'a ; eff''` fresh_weakening_cons `valid ((x',T0')#\<Gamma>')` `x' \<sharp> s2`
      by auto

    have noover: "~(\<turnstile> T0'a <: leS)" .
    have T:"closed ?ns2" "?ns2 : values" using `s2 = ?ns2` `closed s2` `s2 : values` by auto
    have L1:"\<Gamma>' \<turnstile> App ?ns1 ?ns2 : S11 ; FF" using P Q R S' T noover sub by auto
    have L2:"\<turnstile> S11 <: T'" by fact
    from L1 L2 show ?case by auto
  qed
next
  case (Lam a body \<Gamma>' x' e''  T' T1' T0' F' G' ty )
  hence f1: "a\<sharp>\<Gamma>'" and f2: "a\<noteq>x'" and f2': "x'\<sharp>a" and f3: "a\<sharp>e''" and f4: "a\<sharp>((x',T0')#\<Gamma>')"
    by (auto simp add: fresh_atm fresh_prod fresh_list_cons)
  have c1: "((x',T0')#\<Gamma>')\<turnstile>Lam [a:ty].body : T' ; F'" by fact
  hence "\<exists>\<tau>2 eff. ((a,ty)#(x',T0')#\<Gamma>') \<turnstile> body : \<tau>2 ; eff \<and> T'=ty\<rightarrow>\<tau>2:latent_eff.NE  \<and> F' = NE" using f4 abs_ty_elim by auto
  then obtain \<tau>2 eff where c11: "T'=ty\<rightarrow>\<tau>2:latent_eff.NE" and c12: "((a,ty)#(x',T0')#\<Gamma>') \<turnstile> body : \<tau>2 ; eff" "F' = NE" by auto
  from c12 have "valid ((a,ty)#(x',T0')#\<Gamma>')" using Lam by auto
  hence ca: "valid \<Gamma>'" and cb: "a\<sharp>\<Gamma>'" and cc: "x'\<sharp>\<Gamma>'" 
    by (auto dest: valid_elim simp add: fresh_list_cons)
  have c2: "((a,ty)#(x',T0')#\<Gamma>') \<lless> ((x',T0')#(a,ty)#\<Gamma>')" by force
  have c3: "valid ((x',T0')#(a,ty)#\<Gamma>')"
    by (rule v2, rule v2, auto simp add: fresh_list_cons fresh_prod ca cb cc f2' fresh_ty)
  from c12 c2 c3 have c14: "((x',T0')#(a,ty)#\<Gamma>') \<turnstile> body : \<tau>2 ; eff" using `valid ((a, ty) # (x', T0') # \<Gamma>')`
    by (force intro: weakening)
  let ?inner\<Gamma> = "(a,ty)#\<Gamma>'"
  have validig:"valid ?inner\<Gamma>" using `a \<sharp> \<Gamma>'` `valid \<Gamma>'` by auto
  have c15:"\<Gamma>' \<lless>  ?inner\<Gamma>" by auto
  hence c16:"?inner\<Gamma> \<turnstile> e'' : T1' ; G'"
    using weakening[of \<Gamma>' _ _ _ ?inner\<Gamma>] `\<Gamma>' \<turnstile> e'' : T1' ; G'` validig `valid \<Gamma>'` by simp
  have "EX TA0 FA0. ?inner\<Gamma> \<turnstile> body[x'::=e''] : TA0 ; FA0 \<and> \<turnstile> TA0 <: \<tau>2 \<and> \<turnstile> FA0 <e: eff"
    using c16 Lam(10)[of x' T0' ?inner\<Gamma> \<tau>2 eff e'' T1' G'] ` \<turnstile> T1' <: T0'` `valid ((x', T0') # (a, ty) # \<Gamma>')` c14 `closed e''`
    `e'' : values`
    by auto
  then obtain TA0 FA0 where "?inner\<Gamma> \<turnstile> body[x'::=e''] : TA0 ; FA0 "" \<turnstile> TA0 <: \<tau>2" by auto
  hence L1:"\<Gamma>' \<turnstile> (Lam[a:ty].(body[x'::=e''])) : ty \<rightarrow> TA0 : latent_eff.NE; eff.NE" using `a \<sharp> \<Gamma>'` by auto
  have L2:"\<turnstile> ty \<rightarrow> TA0 : latent_eff.NE <: T'" using c11 ` \<turnstile> TA0 <: \<tau>2` by auto
  have L3:"(Lam[a:ty].body)[x'::=e''] = (Lam[a:ty].(body[x'::=e'']))" using Lam by auto
  have L4:"\<turnstile> eff.NE <e: F'" using `F' = NE` by auto
  from L1 L2 L3 L4 show  "EX TA FA. \<Gamma>' \<turnstile> (Lam [a:ty].body)[x'::=e''] : TA ; FA \<and> \<turnstile> TA <: T' \<and> \<turnstile> FA <e: F'" by auto
next
  case (Iff t1 t2 t3 \<Gamma>' x' e'' T' T0' T1' F' G')
  let ?\<Gamma> = "(x', T1') # \<Gamma>'"
  have A:"(\<exists> T1 T2 T3 F1 F2 F3. 
    (?\<Gamma> \<turnstile> t1 : T1 ; F1) \<and> ?\<Gamma> |+ F1 \<turnstile> t2 : T2 ; F2 \<and> ?\<Gamma> |- F1 \<turnstile> t3 : T3 ; F3 \<and> \<turnstile> T2 <: T'  \<and> \<turnstile> T3 <: T' \<and> F' = NE)
    \<or>
    (\<exists> T1 T3 F3. (?\<Gamma> \<turnstile> t1 : T1 ; FF) \<and> ?\<Gamma> \<turnstile> t3 : T3 ; F3 \<and> \<turnstile> T3 <: T' \<and> F' = NE)
    \<or>
    (\<exists> T1 T2 F2. (?\<Gamma> \<turnstile> t1 : T1 ; TT) \<and> ?\<Gamma> \<turnstile> t2 : T2 ; F2 \<and> \<turnstile> T2 <: T'  \<and> F' = NE)" using Iff if_ty_elim by auto
  thus ?case
  proof -
    {
      assume "(\<exists> T1 T2 T3 F1 F2 F3. 
        (?\<Gamma> \<turnstile> t1 : T1 ; F1) \<and> ?\<Gamma> |+ F1 \<turnstile> t2 : T2 ; F2 \<and> ?\<Gamma> |- F1 \<turnstile> t3 : T3 ; F3 \<and> \<turnstile> T2 <: T'  \<and> \<turnstile> T3 <: T' \<and> F' = NE)"
      then obtain T1 T2 T3 F1 F2 F3 where
	"?\<Gamma> \<turnstile> t1 : T1 ; F1 "" ?\<Gamma> |+ F1 \<turnstile> t2 : T2 ; F2 "" ?\<Gamma> |- F1 \<turnstile> t3 : T3 ; F3 "" \<turnstile> T2 <: T'""\<turnstile> T3 <: T'""F' = NE"
	by auto
      hence ?thesis
      proof (nominal_induct F1 rule: eff.induct)
	case NE
	from NE have "\<exists>S1 G1.  \<Gamma>' \<turnstile> t1[x'::=e''] : S1 ; G1  \<and> \<turnstile> S1 <: T1 \<and> \<turnstile> G1 <e: NE" using Iff by auto
	then obtain S1 G1 where  A:"\<Gamma>' \<turnstile> t1[x'::=e''] : S1 ; G1  "" \<turnstile> S1 <: T1 "" \<turnstile> G1 <e: NE" by auto
	have simple:"simple_eff G1" using `\<turnstile> G1 <e: NE` below_ne_simple by auto
	have p1:"(?\<Gamma> \<turnstile> t2 : T2 ; F2)" using prems by auto
	have p2:"(?\<Gamma> \<turnstile> t3 : T3 ; F3)" using prems by auto
	from p1 have "\<exists>S2 G2.  \<Gamma>' \<turnstile> t2[x'::=e''] : S2 ; G2  \<and> \<turnstile> S2 <: T2 \<and> \<turnstile> G2 <e: F2" using Iff by auto
	then obtain S2 G2 where  B:"\<Gamma>' \<turnstile> t2[x'::=e''] : S2 ; G2  "" \<turnstile> S2 <: T2 "" \<turnstile> G2 <e: F2" by auto
	from p2 have "\<exists>S3 G3.  \<Gamma>' \<turnstile> t3[x'::=e''] : S3 ; G3  \<and> \<turnstile> S3 <: T3 \<and> \<turnstile> G3 <e: F3" using Iff by auto
	then obtain S3 G3 where  C:"\<Gamma>' \<turnstile> t3[x'::=e''] : S3 ; G3  "" \<turnstile> S3 <: T3 "" \<turnstile> G3 <e: F3" by auto
	have B':"\<Gamma>' |+ G1 \<turnstile> t2[x'::=e''] : S2 ; G2" using B simple by auto
	have C':"\<Gamma>' |- G1 \<turnstile> t3[x'::=e''] : S3 ; G3" using C simple by auto
	have D:"\<turnstile> S2 <: T'" using prems B by auto
	have E:"\<turnstile> S3 <: T'" using prems C by auto
	from A B' C' D E have " \<Gamma>' \<turnstile> Iff t1 t2 t3[x'::=e''] : T' ; eff.NE"  by auto
	thus ?case using `F' = NE` by auto
      next
	case TT
	from TT have "\<exists>S1 G1.  \<Gamma>' \<turnstile> t1[x'::=e''] : S1 ; G1  \<and> \<turnstile> S1 <: T1 \<and> \<turnstile> G1 <e: TT" using Iff by auto
	then obtain S1 G1 where  A:"\<Gamma>' \<turnstile> t1[x'::=e''] : S1 ; G1  "" \<turnstile> S1 <: T1 "" \<turnstile> G1 <e: TT" by auto
	have simple:"G1 = TT" using A no_sub_TT by blast
	have p1:"(?\<Gamma> \<turnstile> t2 : T2 ; F2)" using prems by auto
	have p2:"(?\<Gamma> \<turnstile> t3 : T3 ; F3)" using prems by auto
	from p1 have "\<exists>S2 G2.  \<Gamma>' \<turnstile> t2[x'::=e''] : S2 ; G2  \<and> \<turnstile> S2 <: T2 \<and> \<turnstile> G2 <e: F2" using Iff by auto
	then obtain S2 G2 where  B:"\<Gamma>' \<turnstile> t2[x'::=e''] : S2 ; G2  "" \<turnstile> S2 <: T2 "" \<turnstile> G2 <e: F2" by auto
	from p2 have "\<exists>S3 G3.  \<Gamma>' \<turnstile> t3[x'::=e''] : S3 ; G3  \<and> \<turnstile> S3 <: T3 \<and> \<turnstile> G3 <e: F3" using Iff by auto
	then obtain S3 G3 where  C:"\<Gamma>' \<turnstile> t3[x'::=e''] : S3 ; G3  "" \<turnstile> S3 <: T3 "" \<turnstile> G3 <e: F3" by auto
	have B':"\<Gamma>' |+ G1 \<turnstile> t2[x'::=e''] : S2 ; G2" using B simple by auto
	have C':"\<Gamma>' |- G1 \<turnstile> t3[x'::=e''] : S3 ; G3" using C simple by auto
	have D:"\<turnstile> S2 <: T'" using prems B by auto
	have E:"\<turnstile> S3 <: T'" using prems C by auto
	from A B' C' D E have " \<Gamma>' \<turnstile> Iff t1 t2 t3[x'::=e''] : T' ; eff.NE"  by auto
	thus ?case using `F' = NE` by auto
      next
	case FF
	from FF have "\<exists>S1 G1.  \<Gamma>' \<turnstile> t1[x'::=e''] : S1 ; G1  \<and> \<turnstile> S1 <: T1 \<and> \<turnstile> G1 <e: FF" using Iff by auto
	then obtain S1 G1 where  A:"\<Gamma>' \<turnstile> t1[x'::=e''] : S1 ; G1  "" \<turnstile> S1 <: T1 "" \<turnstile> G1 <e: FF" by auto
	have simple:"G1 = FF" using A no_sub_FF by blast
	have p1:"(?\<Gamma> \<turnstile> t2 : T2 ; F2)" using prems by auto
	have p2:"(?\<Gamma> \<turnstile> t3 : T3 ; F3)" using prems by auto
	from p1 have "\<exists>S2 G2.  \<Gamma>' \<turnstile> t2[x'::=e''] : S2 ; G2  \<and> \<turnstile> S2 <: T2 \<and> \<turnstile> G2 <e: F2" using Iff by auto
	then obtain S2 G2 where  B:"\<Gamma>' \<turnstile> t2[x'::=e''] : S2 ; G2  "" \<turnstile> S2 <: T2 "" \<turnstile> G2 <e: F2" by auto
	from p2 have "\<exists>S3 G3.  \<Gamma>' \<turnstile> t3[x'::=e''] : S3 ; G3  \<and> \<turnstile> S3 <: T3 \<and> \<turnstile> G3 <e: F3" using Iff by auto
	then obtain S3 G3 where  C:"\<Gamma>' \<turnstile> t3[x'::=e''] : S3 ; G3  "" \<turnstile> S3 <: T3 "" \<turnstile> G3 <e: F3" by auto
	have B':"\<Gamma>' |+ G1 \<turnstile> t2[x'::=e''] : S2 ; G2" using B simple by auto
	have C':"\<Gamma>' |- G1 \<turnstile> t3[x'::=e''] : S3 ; G3" using C simple by auto
	have D:"\<turnstile> S2 <: T'" using prems B by auto
	have E:"\<turnstile> S3 <: T'" using prems C by auto
	from A B' C' D E have " \<Gamma>' \<turnstile> Iff t1 t2 t3[x'::=e''] : T' ; eff.NE"  by auto
	thus ?case using `F' = NE` by auto
      next
	case (VE z)
	from VE have "\<exists>S1 G1.  \<Gamma>' \<turnstile> t1[x'::=e''] : S1 ; G1  \<and> \<turnstile> S1 <: T1 \<and> \<turnstile> G1 <e: VE z" using Iff by auto
	then obtain S1 G1 where  A:"\<Gamma>' \<turnstile> t1[x'::=e''] : S1 ; G1  "" \<turnstile> S1 <: T1 "" \<turnstile> G1 <e: VE z" by auto
	have simple:"G1 = VE z \<or> simple_eff G1" using A below_ve_simple by blast
	have p1:"(?\<Gamma> \<turnstile> t2 : T2 ; F2)" using prems by auto
	have p2:"(?\<Gamma> \<turnstile> t3 : T3 ; F3)" using prems by auto
	from p1 have "\<exists>S2 G2.  \<Gamma>' \<turnstile> t2[x'::=e''] : S2 ; G2  \<and> \<turnstile> S2 <: T2 \<and> \<turnstile> G2 <e: F2" using Iff by auto
	then obtain S2 G2 where  B:"\<Gamma>' \<turnstile> t2[x'::=e''] : S2 ; G2  "" \<turnstile> S2 <: T2 "" \<turnstile> G2 <e: F2" by auto
	from p2 have "\<exists>S3 G3.  \<Gamma>' \<turnstile> t3[x'::=e''] : S3 ; G3  \<and> \<turnstile> S3 <: T3 \<and> \<turnstile> G3 <e: F3" using Iff by auto
	then obtain S3 G3 where  C:"\<Gamma>' \<turnstile> t3[x'::=e''] : S3 ; G3  "" \<turnstile> S3 <: T3 "" \<turnstile> G3 <e: F3" by auto
	have B':"\<Gamma>' |+ G1 \<turnstile> t2[x'::=e''] : S2 ; G2" using B simple by auto
	have C':"\<Gamma>' |- G1 \<turnstile> t3[x'::=e''] : S3 ; G3" using C simple by auto
	have D:"\<turnstile> S2 <: T'" using prems B by auto
	have E:"\<turnstile> S3 <: T'" using prems C by auto
	from A B' C' D E have " \<Gamma>' \<turnstile> Iff t1 t2 t3[x'::=e''] : T' ; eff.NE"  by auto
	thus ?case using `F' = NE` by auto
      next
	case (TE U z)
	have "EX f A A1 Fn. t1 = (App f (Var z)) \<and> (x', T1') # \<Gamma>' \<turnstile> f : A1 \<rightarrow> T1 : Latent U ; Fn \<and> 
	  (x', T1') # \<Gamma>' \<turnstile> (Var z) : A ; VE z \<and> \<turnstile> A <: A1" 
          using TE te_ty_elim[of ?\<Gamma> t1 T1 U z] by auto
	then obtain f A1 A Fn where A:"t1 = (App f (Var z)) "" (x', T1') # \<Gamma>' \<turnstile> f : A1 \<rightarrow> T1 : Latent U ; Fn"
	  "(x', T1') # \<Gamma>' \<turnstile> (Var z) : A ; VE z "" \<turnstile> A <: A1" by auto
	have size1:"(f,Iff t1 t2 t3) : smaller_than" using A(1) by (simp add: smaller_than_def measure_def)
	note Iff(1)[of f]
        hence ih_f:"!! c \<sigma> \<Gamma> T F e' T0 F0 . 
          (c,\<sigma>)#\<Gamma> \<turnstile> f : T ; F \<Longrightarrow> \<Gamma> \<turnstile> e' : T0 ; F0 \<Longrightarrow> \<turnstile> T0 <: \<sigma> \<Longrightarrow> valid ((c,\<sigma>)#\<Gamma>) \<Longrightarrow> closed e' \<Longrightarrow> e' : values
          \<Longrightarrow> EX T' F' . \<Gamma> \<turnstile> f[c::=e'] : T' ; F' \<and> \<turnstile> T' <: T \<and> \<turnstile> F' <e: F" using size1 by auto
        have "EX A' Fn' . \<Gamma>' \<turnstile> f[x'::=e''] : A' ; Fn' \<and> \<turnstile> A' <: A1 \<rightarrow> T1 : Latent U \<and> \<turnstile> Fn' <e: Fn" 
          using ih_f A Iff by auto
	then obtain A' Fn' where  B:"\<Gamma>' \<turnstile> f[x'::=e''] : A' ; Fn' \<and> \<turnstile> A' <: A1 \<rightarrow> T1 : Latent U" by auto
	hence "EX A1' A2' . A' = A1' \<rightarrow> A2' : Latent U \<and> \<turnstile> A1 <: A1' \<and> \<turnstile> A2' <: T1" using subtype_arr_elim
	  by auto
	then obtain A1' A2' where C:"A' = A1' \<rightarrow> A2' : Latent U "" \<turnstile> A1 <: A1' \<and> \<turnstile> A2' <: T1" by auto

	let ?mapfun = "(%f. (% (v,ty). (if (z = v) then (v,f U ty) else (v,ty))))"
        let ?\<Gamma>1 = "(map (?mapfun restrict) \<Gamma>')"
        let ?\<Gamma>2 = "(map (?mapfun remove) \<Gamma>')"          
        have "valid \<Gamma>'" using `valid ?\<Gamma>` using valid_elim[of x' T1' \<Gamma>'] by auto

	show ?case 
	proof (cases "x' = z")
	  case True
          from A True have  "(Var z)[x'::=e''] = e''" by auto
          hence D:"\<Gamma>' \<turnstile> (Var z)[x'::=e''] : T0' ; G'" "closed ((Var z)[x'::=e''])" "((Var z)[x'::=e'']) : values"
	    using Iff by auto
          have "\<turnstile> T0' <: T1'" .
          note var_ty_elim[of ?\<Gamma> z A "VE z"]
          hence "(x', A) : set ?\<Gamma>" using A True by auto
          have "?\<Gamma> \<turnstile> (Var x') : T1' ; VE x'" using `valid ?\<Gamma>` by auto
          hence "T1' = A" using A unique_var_typing[of ] True by auto
          have "\<turnstile> T0' <: T1'" .
          hence "\<turnstile> T0' <: A" using `T1' = A` by simp
          have or:"
            (\<turnstile> T0' <: U \<and> \<turnstile> T0' <: restrict U T1') \<or>
            (~ (\<turnstile> T0' <: U)  \<and> \<turnstile> T0' <: remove U T1')" 
            using `\<Gamma>' \<turnstile> e'' : T0' ; G'` `e'' : values` `\<turnstile> T0' <: T1'` `closed e''`
            reduce_remove_soundness
            by auto
          have "?\<Gamma>1 = envop restrict z U \<Gamma>'" by auto
          have "?\<Gamma>2 = envop remove z U \<Gamma>'" by auto
          have "x' \<sharp> \<Gamma>'" using Iff valid_elim[of x' T1' \<Gamma>'] by auto
          hence "?\<Gamma>1 = \<Gamma>'" using True envop_forget `valid \<Gamma>'` by auto
          hence GA:"?\<Gamma> |+ TE U z = (x',restrict U T1') # \<Gamma>'" using True by auto
          hence G1:"\<dots> \<turnstile> t2 : T2; F2" using `(?\<Gamma> |+ TE U z)\<turnstile> t2 : T2 ; F2` by auto
          have "?\<Gamma>2 = \<Gamma>'" using `x' \<sharp> \<Gamma>'` True envop_forget `valid \<Gamma>'` by auto
          hence GB:"?\<Gamma> |- TE U z = (x',remove U T1') # \<Gamma>'" using True by auto
          hence G2:"\<dots> \<turnstile> t3 : T3; F3" using `(?\<Gamma> |- TE U z)\<turnstile> t3 : T3 ; F3` by auto
          have "valid (?\<Gamma> |+ TE U z)" using `valid ?\<Gamma>` envplus_valid[of ?\<Gamma> "TE U z"] by auto
          hence G3:"valid ((x',restrict U T1') # \<Gamma>')" using GA by auto
          have "valid (?\<Gamma> |- TE U z)" using `valid ?\<Gamma>` envminus_valid[of ?\<Gamma> "TE U z"] by auto
          hence G4:"valid ((x',remove U T1') # \<Gamma>')" using GB by auto
          show ?thesis
          proof -
            {
              assume "\<turnstile> T0' <: restrict U T1' " " \<turnstile> T0' <: remove U T1'"
              have 0:"\<Gamma>' |+ eff.NE = \<Gamma>'" "\<Gamma>' |- eff.NE = \<Gamma>'" by auto
              have 2:"(x', restrict U T1') # \<Gamma>' \<turnstile> t2 : T2 ; F2 " using `?\<Gamma> |+ TE U z \<turnstile> t2 : T2 ; F2` GA by auto
              note Iff(2)[of x' "restrict U T1'" \<Gamma>' T2 F2 e'' T0' G'] 
              hence "\<exists>S2 G2.  \<Gamma>' \<turnstile> t2[x'::=e''] : S2 ; G2  \<and> \<turnstile> S2 <: T2 \<and> \<turnstile> G2 <e: F2" using G3 prems `closed e''` 2 by auto
              then obtain S2 G2 where L1:"\<Gamma>'|+ eff.NE \<turnstile> t2[x'::=e''] : S2 ; G2  "" \<turnstile> S2 <: T2 "" \<turnstile> G2 <e: F2" using 0 by auto
              have 3:"(x', remove U T1') # \<Gamma>' \<turnstile> t3 : T3 ; F3 " using `?\<Gamma> |- TE U z \<turnstile> t3 : T3 ; F3` GB by auto
              note Iff(3)[of x' "remove U T1'" \<Gamma>' T3 F3 e'' T0' G'] 
              hence "\<exists>S3 G3.  \<Gamma>' \<turnstile> t3[x'::=e''] : S3 ; G3  \<and> \<turnstile> S3 <: T3 \<and> \<turnstile> G3 <e: F3" using G4 prems `closed e''` 3 by auto
              then obtain S3 G3 where L2:"\<Gamma>'|-eff.NE \<turnstile> t3[x'::=e''] : S3 ; G3  "" \<turnstile> S3 <: T3 "" \<turnstile> G3 <e: F3" using 0 by auto
              have "\<turnstile> T0' <: A1'" using A B C D `\<turnstile> T0' <: A` by auto
              hence "\<Gamma>' \<turnstile> (App f (Var z))[x'::=e''] : A2' ; eff.NE" using A B C D `\<turnstile> T0' <: A` by auto
              hence L3:"\<Gamma>' \<turnstile> t1[x'::=e''] : A2' ; eff.NE" using `t1 = App f (Var z)` by auto
              have "\<turnstile> S2 <: T'" "\<turnstile> S3 <: T'" using L1 L2 `\<turnstile> T3 <: T'` `\<turnstile> T2 <: T'` by auto
              hence "\<Gamma>'\<turnstile> (Iff t1 t2 t3)[x'::=e''] : T' ; eff.NE"
                using L3 ` \<Gamma>'|+eff.NE \<turnstile> t2[x'::=e''] : S2 ; G2` ` \<Gamma>'|-NE \<turnstile> t3[x'::=e''] : S3 ; G3` by auto
              hence ?thesis using `F' = NE` by auto
            }
            moreover
            {
              assume "\<turnstile> T0' <: U "" \<turnstile> T0' <: restrict U T1'"
              have 2:"(x', restrict U T1') # \<Gamma>' \<turnstile> t2 : T2 ; F2 " using `?\<Gamma> |+ TE U z \<turnstile> t2 : T2 ; F2` GA by auto
              note Iff(2)[of x' "restrict U T1'" \<Gamma>' T2 F2 e'' T0' G'] 
              hence "\<exists>S2 G2.  \<Gamma>' \<turnstile> t2[x'::=e''] : S2 ; G2  \<and> \<turnstile> S2 <: T2 \<and> \<turnstile> G2 <e: F2" using G3 prems `closed e''` 2 by auto
              then obtain S2 G2 where L1:"\<Gamma>'|+ eff.TT \<turnstile> t2[x'::=e''] : S2 ; G2  "" \<turnstile> S2 <: T2 "" \<turnstile> G2 <e: F2" by auto
              have "\<turnstile> T0' <: A1'" using A B C D `\<turnstile> T0' <: A` by auto
              hence "\<Gamma>' \<turnstile> (App f (Var z))[x'::=e''] : A2' ; eff.TT" using A B C D `\<turnstile> T0' <: A` `\<turnstile> T0' <: U` by auto
              hence L3:"\<Gamma>' \<turnstile> t1[x'::=e''] : A2' ; eff.TT" using `t1 = App f (Var z)` by auto
              have "\<turnstile> S2 <: T'"  using L1 `\<turnstile> T2 <: T'` by auto
              hence "\<Gamma>'\<turnstile> (Iff t1 t2 t3)[x'::=e''] : T' ; eff.NE"
                using L3 ` \<Gamma>'|+eff.TT \<turnstile> t2[x'::=e''] : S2 ; G2` by auto
              hence ?thesis using `F' = NE` by auto              
            }
            moreover
            {
              assume "~ (\<turnstile> T0' <: U) "" \<turnstile> T0' <: remove U T1'"
              have 3:"(x', remove U T1') # \<Gamma>' \<turnstile> t3 : T3 ; F3 " using `?\<Gamma> |- TE U z \<turnstile> t3 : T3 ; F3` GB by auto
              note Iff(3)[of x' "remove U T1'" \<Gamma>' T3 F3 e'' T0' G'] 
              hence "\<exists>S3 G3.  \<Gamma>' \<turnstile> t3[x'::=e''] : S3 ; G3  \<and> \<turnstile> S3 <: T3 \<and> \<turnstile> G3 <e: F3" using G4 prems `closed e''` 3 by auto
              then obtain S3 G3 where L1:"\<Gamma>'|+ eff.FF \<turnstile> t3[x'::=e''] : S3 ; G3  "" \<turnstile> S3 <: T3 "" \<turnstile> G3 <e: F3" by auto
              have "\<turnstile> T0' <: A1'" using A B C D `\<turnstile> T0' <: A` by auto
              hence "\<Gamma>' \<turnstile> (App f (Var z))[x'::=e''] : A2' ; eff.FF" using A B C D `\<turnstile> T0' <: A` `~ (\<turnstile> T0' <: U)` by auto
              hence L3:"\<Gamma>' \<turnstile> t1[x'::=e''] : A2' ; eff.FF" using `t1 = App f (Var z)` by auto
              have "\<turnstile> S3 <: T'"  using L1 `\<turnstile> T3 <: T'` by auto
              hence "\<Gamma>'\<turnstile> (Iff t1 t2 t3)[x'::=e''] : T' ; eff.NE"
                using L3 ` \<Gamma>'|+eff.FF \<turnstile> t3[x'::=e''] : S3 ; G3` by auto
              hence ?thesis using `F' = NE` by auto              
            }
            ultimately show ?thesis using or by auto
          qed
	next
	  case False
	  from A False have "(Var z)[x'::=e''] = (Var z)" by auto
	  hence D:"\<Gamma>' \<turnstile> (Var z)[x'::=e''] : A ; VE z" using False A
          proof -
            have q1:"?\<Gamma> \<turnstile> Var z : A ; VE z" .
            have "x' \<sharp> Var z" using trm.fresh False fresh_atm by auto
            hence "\<Gamma>' \<turnstile> Var z : A ; VE z" using q1 fresh_weakening_cons `valid ((x',T1')# \<Gamma>')` by auto
            thus ?thesis using `(Var z)[x'::=e''] = Var z` by auto
          qed
	  from A B C D have "\<Gamma>' \<turnstile> App (f[x'::=e'']) ((Var z)[x'::=e'']) : A2' ; TE U z" by auto
          hence typetst: "\<Gamma>' \<turnstile> t1[x'::=e''] : A2' ; TE U z" using A by auto
	  have F:"?\<Gamma> |+ TE U z = (x',T1') # ?\<Gamma>1" using False by auto
          hence H:"(x',T1') # ?\<Gamma>1 \<turnstile> t2 : T2 ; F2" using `?\<Gamma> |+ TE U z \<turnstile> t2 : T2 ; F2` by auto
          hence K:"valid ?\<Gamma>1" using envop_valid `valid \<Gamma>'` by auto
          have J:"?\<Gamma>1 \<turnstile> e'' : T0' ; G'" using K `valid \<Gamma>'` closed_any_env `closed e''` Iff by blast
          have "x' \<sharp> ?\<Gamma>1" using Iff valid_elim[of x' T1' \<Gamma>'] envop_fresh[of x' \<Gamma>' restrict z U] `valid \<Gamma>'` by auto
          hence "valid ((x',T1')#?\<Gamma>1)" using `valid ?\<Gamma>1` by auto
          hence ex1:"\<exists>S2 G2. ?\<Gamma>1  \<turnstile> t2[x'::=e''] : S2 ; G2  \<and> \<turnstile> S2 <: T2 \<and> \<turnstile> G2 <e: F2"
            using H J K Iff by auto 

	  have G:"?\<Gamma> |- TE U z = (x',T1') # ?\<Gamma>2" using False by auto
          hence H:"(x',T1') # ?\<Gamma>2 \<turnstile> t3 : T3 ; F3" using `?\<Gamma> |- TE U z \<turnstile> t3 : T3 ; F3` by auto
          hence K:"valid ?\<Gamma>2" using envop_valid `valid \<Gamma>'` by auto
          have J:"?\<Gamma>2 \<turnstile> e'' : T0' ; G'" using K `valid \<Gamma>'` closed_any_env `closed e''` Iff by blast
          have "x' \<sharp> ?\<Gamma>2" using Iff valid_elim[of x' T1' \<Gamma>'] envop_fresh[of x' \<Gamma>' remove z U] `valid \<Gamma>'` by auto
          hence "valid ((x',T1')#?\<Gamma>2)" using `valid ?\<Gamma>2` by auto
          hence ex2:"\<exists>S3 G3. ?\<Gamma>2  \<turnstile> t3[x'::=e''] : S3 ; G3  \<and> \<turnstile> S3 <: T3 \<and> \<turnstile> G3 <e: F3"
            using H J K Iff by auto

          from ex1 obtain S2 G2 where 1:"?\<Gamma>1  \<turnstile> t2[x'::=e''] : S2 ; G2"" \<turnstile> S2 <: T'" using `\<turnstile> T2 <: T'` by auto
          from ex2 obtain S3 G3 where 2:"?\<Gamma>2  \<turnstile> t3[x'::=e''] : S3 ; G3"" \<turnstile> S3 <: T'" using `\<turnstile> T3 <: T'`  by auto
          have 4:"?\<Gamma>1 = \<Gamma>' |+ (TE U z)" by auto
          have 5:"?\<Gamma>2 = \<Gamma>' |- (TE U z)" by auto
          have X:"!! G G' e T F. G = G' \<Longrightarrow> G \<turnstile> e : T ; F \<Longrightarrow> G' \<turnstile> e : T ; F" by auto
          from 1 4 have 6:"\<Gamma>' |+ (TE U z) \<turnstile> t2[x'::=e''] : S2 ; G2" using X[of ?\<Gamma>1 "\<Gamma>' |+ (TE U z)" " t2[x'::=e'']" S2 G2]
            by blast
          from 2 5 have 7:"\<Gamma>' |- (TE U z) \<turnstile> t3[x'::=e''] : S3 ; G3" using X[of ?\<Gamma>2 "\<Gamma>' |- (TE U z)" " t3[x'::=e'']" S3 G3]
            by blast
          
          from typetst 1 2 6 7 have "\<Gamma>' \<turnstile> (Iff t1 t2 t3)[x'::=e''] : T' ; eff.NE" by auto
	  thus ?thesis  using `F' = NE` by auto
	qed
      qed
    }
    moreover
    {
      assume "\<exists> T1 T3 F3. (?\<Gamma> \<turnstile> t1 : T1 ; FF) \<and> ?\<Gamma> \<turnstile> t3 : T3 ; F3 \<and> \<turnstile> T3 <: T' \<and> F' = NE"
      then obtain T1 T3 F3 where "?\<Gamma> \<turnstile> t1 : T1 ; FF" "?\<Gamma> \<turnstile> t3 : T3 ; F3" "\<turnstile> T3 <: T'" "F' = NE"
	by auto
      hence "\<exists>S1 G1.  \<Gamma>' \<turnstile> t1[x'::=e''] : S1 ; G1  \<and> \<turnstile> S1 <: T1 \<and> \<turnstile> G1 <e: FF" using Iff by auto
      then obtain S1 G1 where B:"\<Gamma>' \<turnstile> t1[x'::=e''] : S1 ; G1  "" \<turnstile> S1 <: T1 "" \<turnstile> G1 <e: FF" by auto
      hence  C:"\<Gamma>' \<turnstile> t1[x'::=e''] : S1 ; FF  " using B no_sub_FF by auto
      from prems have "\<exists>S3 G3.  \<Gamma>' \<turnstile> t3[x'::=e''] : S3 ; G3  \<and> \<turnstile> S3 <: T3 \<and> \<turnstile> G3 <e: F3" using Iff by auto
      then obtain S3 G3 where D:"\<Gamma>' \<turnstile> t3[x'::=e''] : S3 ; G3 ""\<turnstile> S3 <: T3" by auto
      from B C D have "\<Gamma>' \<turnstile> (Iff  (t1[x'::=e'']) (t2[x'::=e'']) (t3[x'::=e''])) : S3 ; eff.NE" by auto
      hence ?thesis  using `\<turnstile> T3 <: T'` `\<turnstile> S3 <: T3` `F' = NE` by auto
    }
    moreover
    {
      assume "\<exists> T1 T2 F2. (?\<Gamma> \<turnstile> t1 : T1 ; TT) \<and> ?\<Gamma> \<turnstile> t2 : T2 ; F2 \<and> \<turnstile> T2 <: T'  \<and> F' = NE"
      then obtain T1 T2 F2 where "?\<Gamma> \<turnstile> t1 : T1 ; TT" "?\<Gamma> \<turnstile> t2 : T2 ; F2" "\<turnstile> T2 <: T'" "F' = NE"
	by auto
      hence "\<exists>S1 G1.  \<Gamma>' \<turnstile> t1[x'::=e''] : S1 ; G1  \<and> \<turnstile> S1 <: T1 \<and> \<turnstile> G1 <e: TT" using Iff by auto
      then obtain S1 G1 where B:"\<Gamma>' \<turnstile> t1[x'::=e''] : S1 ; G1  "" \<turnstile> S1 <: T1 "" \<turnstile> G1 <e: TT" by auto
      hence  C:"\<Gamma>' \<turnstile> t1[x'::=e''] : S1 ; TT  " using B no_sub_TT by auto
      from prems have "\<exists>S2 G2.  \<Gamma>' \<turnstile> t2[x'::=e''] : S2 ; G2  \<and> \<turnstile> S2 <: T2 \<and> \<turnstile> G2 <e: F2" using Iff by auto
      then obtain S2 G2 where D:"\<Gamma>' \<turnstile> t2[x'::=e''] : S2 ; G2 ""\<turnstile> S2 <: T2" by auto
      from B C D have "\<Gamma>' \<turnstile> (Iff  (t1[x'::=e'']) (t2[x'::=e'']) (t3[x'::=e''])) : S2 ; eff.NE" by auto
      hence ?thesis  using `\<turnstile> T2 <: T'` `\<turnstile> S2 <: T2` `F' = NE` by auto
    }
    ultimately show ?thesis using A by blast
  qed
qed

inductive_cases beta_cases:"App (Abs x b T) v \<hookrightarrow> e "
thm beta_cases

lemma preserve_red:
  assumes typed:"\<Gamma> \<turnstile> e : t ; eff" and cl:"closed e"
  and red:"e \<hookrightarrow> e'" and val:"valid \<Gamma>"
  shows "EX t' eff'. \<Gamma> \<turnstile> e' : t' ; eff' \<and> \<turnstile> t' <: t \<and> \<turnstile> eff' <e: eff "
  using red typed cl val red
  thm reduce_induct
  proof (nominal_induct e e' avoiding: \<Gamma> t rule: reduce_induct)
    case (e_delta p v' v)
    thm app_ty_elim[of \<Gamma> "(BI p)" v' t eff]
    hence "\<exists>T0 T0' T1 le eff' eff''.  \<Gamma> \<turnstile> BI p : T0 \<rightarrow> T1 : le ; eff'  \<and>  \<Gamma> \<turnstile> v' : T0' ; eff''  \<and> \<turnstile> T0' <: T0 \<and> T1 = t"
      using app_ty_elim[of \<Gamma> "(BI p)" v' t eff] by simp
    then obtain T0 T0' T1 le eff' eff'' where " \<Gamma> \<turnstile> BI p : T0 \<rightarrow> T1 : le ; eff'" and  "\<Gamma> \<turnstile> v' : T0' ; eff''" and "\<turnstile> T0' <: T0" and "T1 = t"
      by auto
    hence "(T0 \<rightarrow> T1 : le) = \<Delta>\<^isub>\<tau> p" using e_delta typing_bi[of \<Gamma> p "(T0 \<rightarrow> T1 : le)" eff'] by simp
    hence "EX F. \<Gamma> \<turnstile> v : T1 ; F \<and> \<turnstile> F <e: eff" using delta_soundness[of p T0 T1 le v' \<Gamma> T0' eff'' eff v] e_delta `T1 = t` `\<Gamma> \<turnstile> v' : T0' ; eff''` `\<turnstile> T0' <: T0`
      by auto
    hence "EX F. \<Gamma> \<turnstile> v : t ; F \<and> \<turnstile> F <e: eff" using `T1 = t` by auto
    thus ?case by auto
  next
    case (e_if_false thn els \<Gamma>' t') 
    have "eff = NE" using if_false_ty_elim[of _ _ _ _ eff] e_if_false by auto
    have " \<exists>T0 eff'.  \<Gamma>' \<turnstile> els : T0 ; eff'  \<and> \<turnstile> T0 <: t' " using   if_false_ty_elim[of \<Gamma>' thn els t' eff] e_if_false by auto
    then obtain T0 eff' where  f:"\<Gamma>' \<turnstile> els : T0 ; eff'"  and g:"\<turnstile> T0 <: t'" by auto
    have "closed els" using e_if_false closed_def trm.supp by auto
    hence "simple_eff eff'" using closed_eff f by auto
    hence h:"\<turnstile> eff' <e: eff" using simple_eff_below_ne `eff = NE` by auto
    thus ?case using f g  by auto
  next
    case (e_if_true v thn els \<Gamma>' t') 
    have "eff = NE" using if_true_ty_elim[of \<Gamma>' v thn els _ eff] e_if_true by auto
    have " \<exists>T0 eff'.  \<Gamma>' \<turnstile> thn : T0 ; eff'  \<and> \<turnstile> T0 <: t' " using   if_true_ty_elim[of \<Gamma>' v thn els t' eff] e_if_true by auto
    then obtain T0 eff' where  f:"\<Gamma>' \<turnstile> thn : T0 ; eff'"  and g:"\<turnstile> T0 <: t'" by auto
    have "closed thn" using e_if_true closed_def trm.supp by auto
    hence "simple_eff eff'" using closed_eff f by auto
    hence h:"\<turnstile> eff' <e: eff" using `eff = NE` by auto
    thus ?case using f g  by auto
  next
    case (e_beta x b v T \<Gamma>' T')
    thm app_ty_elim[of \<Gamma>' "(Lam[x:T].b)" v t eff]
    hence "eff = NE" using app_abs_ty_elim_eff by auto
    from e_beta have "\<exists>T0 T0' T1 le eff' eff''.  \<Gamma>' \<turnstile> Abs x b T : T0 \<rightarrow> T1 : le ; eff'  \<and>  \<Gamma>' \<turnstile> v : T0' ; eff''  \<and> \<turnstile> T0' <: T0 \<and> T1 = T'"
      using app_ty_elim[of \<Gamma>' "Abs x b T" v T' eff] by simp
    then obtain T0 T0' T1 le eff' eff'' where " \<Gamma>' \<turnstile> Lam[x:T].b : T0 \<rightarrow> T1 : le ; eff'" and "\<Gamma>' \<turnstile> v : T0' ; eff''" 
      and "\<turnstile> T0' <: T0" and "T1 = T'" by auto
    thm abs_ty_elim[of \<Gamma>' x b T "T0 \<rightarrow> T1 : le" eff']
    hence "\<exists>T1a eff2.  (x,T)#\<Gamma>' \<turnstile> b : T1a ; eff2  \<and> T0 \<rightarrow> T1 : le = T \<rightarrow> T1a : latent_eff.NE"
      using abs_ty_elim[of \<Gamma>' x b T "T0 \<rightarrow> T1 : le" eff'] e_beta `x \<sharp> \<Gamma>'` by auto
    then obtain T1a eff2 where  "(x,T)#\<Gamma>' \<turnstile> b : T1a ; eff2" and "T0 \<rightarrow> T1 : le = T \<rightarrow> T1a : latent_eff.NE"
      by auto
    have "closed v" using e_beta closed_def trm.supp by auto
    have "v : values" using e_beta beta_cases[of _ _ _ v _ "v : values"]  trm.inject by auto
    have "T0 = T" using `T0 \<rightarrow> T1 : le = T \<rightarrow> T1a : latent_eff.NE` ty.inject by simp
    hence "T1a = T1" using `T0 \<rightarrow> T1 : le = T \<rightarrow> T1a : latent_eff.NE` ty.inject by simp
    hence "T1a = T'" using `T1 = T'` by simp
    hence "(x,T)#\<Gamma>' \<turnstile> b : T' ; eff2" using `(x,T)#\<Gamma>' \<turnstile> b : T1a ; eff2` by simp
    then have " \<exists>T'a F'.  \<Gamma>' \<turnstile> b[x::=v] : T'a ; F'  \<and> \<turnstile> T'a <: T'"
      using preserve_subst[of x T \<Gamma>' b T' eff2 v T0' eff''] `\<Gamma>' \<turnstile> v : T0' ; eff''` ` \<turnstile> T0' <: T0` `T0=T` `x \<sharp> \<Gamma>'` `valid \<Gamma>'` 
      `closed v` `v : values`
      by auto
    then obtain T'a F' where a:"\<Gamma>' \<turnstile> b[x::=v] : T'a ; F'" and b:"\<turnstile> T'a <: T'" by auto
    have "closed (b[x::=v])" using e_beta reduce_closed by blast
    hence c:"simple_eff F'" using a closed_eff by auto
    from a b c have "\<turnstile> F' <e: eff" using `eff = NE` simple_eff_below_ne by auto
    thus ?case using a b by auto
  qed

lemma value_no_ctxt:
  assumes "v : values" and "v = E t" and "E : ctxt"
  shows "E = (% t . t)"
  using prems
  proof (induct)
    case bi_value show ?case using `E : ctxt` bi_value
      by (induct E rule: ctxt.induct) (auto simp add: trm.inject)
  next
    case num_value show ?case using `E : ctxt` num_value
      by (induct E rule: ctxt.induct) (auto simp add: trm.inject)
  next
    case abs_value show ?case using `E : ctxt` abs_value
      by (induct E rule: ctxt.induct) (auto simp add: trm.inject)
  next
    case bool_value show ?case using `E : ctxt` bool_value
      by (induct E rule: ctxt.induct) (auto simp add: trm.inject)
  qed


lemma subst_in_ctxt_preserves_type:
  assumes a:"\<Gamma> \<turnstile> u : T ; F"
  and b:"C : ctxt"
  and c:"u = C e"
  and "~ (e : values)"
  and "closed (C e)" and "closed (C e')"
  and "!! T0 F0  . \<Gamma> \<turnstile> e : T0 ; F0 \<Longrightarrow> EX T1 F1. \<Gamma> \<turnstile> e' : T1 ; F1 \<and> \<turnstile> T1 <: T0 \<and> \<turnstile> F1 <e: F0"
  shows "EX S G. \<Gamma> \<turnstile> C e' : S ; G \<and> \<turnstile> S <: T \<and> \<turnstile> G <e: F"
  using b prems
  proof (induct C arbitrary: u e e' T F rule: ctxt.induct)
    case C_Hole
    hence "\<Gamma> \<turnstile> e : T ; F" using C_Hole by simp
    hence "EX S G. \<Gamma> \<turnstile> e' : S; G \<and> \<turnstile> S <: T \<and> \<turnstile> G <e: F" using C_Hole by auto
    thus ?case by simp
  next
    case (C_App1 E arg u' t t' T' F')
    have A:"closed (E t)" and B:"closed (E t')" using C_App1 closed_def trm.supp by auto
    have C:"\<Gamma> \<turnstile> App (E t) arg : T' ; F'" using C_App1 by auto
    hence D:"simple_eff F'" using C_App1 closed_eff by auto
    thus ?case using C_App1 A B C
      proof (induct rule: simple_eff_cases)
        case NE
        hence "EX T0 T0' T1 le eff' eff''.  \<Gamma> \<turnstile> E t : T0 \<rightarrow> T1 : le ; eff'  \<and>  \<Gamma> \<turnstile> arg : T0' ; eff'' \<and> \<turnstile> T0' <: T0 \<and> T1 = T'"
          using app_ty_elim by auto
        then obtain T0 T0' le eff' eff'' 
          where  a:"\<Gamma> \<turnstile> E t : T0 \<rightarrow> T' : le ; eff'" and b:"\<Gamma> \<turnstile> arg : T0' ; eff''" and c:"\<turnstile> T0' <: T0" by auto
        have  "\<exists>S G.  \<Gamma> \<turnstile> E t' : S ; G  \<and> \<turnstile> S <: T0 \<rightarrow> T' : le \<and> \<turnstile> G <e: eff'"
          using C_App1(2)[of "E t" "T0 \<rightarrow> T' : le" eff' t t']  `E : ctxt` `closed (E t)` `closed (E t')` C_App1(8) a
	  `t \<notin> values` C_App1 by auto
        then obtain S G where et'ty:"\<Gamma> \<turnstile> E t' : S ; G " and subarr:" \<turnstile> S <: T0 \<rightarrow> T' : le " and "\<turnstile> G <e: eff'" by auto
        from subarr have "EX A0 A1. S = A0 \<rightarrow> A1 : le \<and> \<turnstile> T0 <: A0 \<and> \<turnstile> A1 <: T'" using subtype_arr_elim by auto
        then obtain A0 A1 where seq:"S = A0 \<rightarrow> A1 : le "" \<turnstile> T0 <: A0 "" \<turnstile> A1 <: T'" by auto
        hence "\<turnstile> T0' <: A0" using c by auto
        have "\<Gamma> \<turnstile> E t' : A0 \<rightarrow> A1 : le ; G" using seq et'ty by auto
        thus ?case  using `\<turnstile> A1 <: T'` b `\<turnstile> T0' <: A0` by auto
      next
        case FF
        have "EX S T0 T0' le F1 F2.  \<Gamma> \<turnstile> E t : T0 \<rightarrow> T' : le ; F1  \<and>  \<Gamma> \<turnstile> arg : T0' ; F2 \<and> \<turnstile> T0' <: T0 \<and> le = Latent S \<and> 
	  ~ (\<turnstile> T0' <: S) \<and> arg : values \<and> closed arg"
          using `\<Gamma> \<turnstile> App (E t) arg : T' ; FF` app_ty_ff_elim[of \<Gamma> "E t" arg T'] by auto
        then obtain S T0 T0' F1 F2 where  a:"\<Gamma> \<turnstile> E t : T0 \<rightarrow> T' : Latent S ; F1" and  b:"\<Gamma> \<turnstile> arg : T0' ; F2 " and c:"\<turnstile> T0' <: T0 " and d:" ~ (\<turnstile> T0' <: S)"  "closed arg" "arg : values"
          by auto
        have  "\<exists>S' G.  \<Gamma> \<turnstile> E t' : S' ; G  \<and> \<turnstile> S' <: T0 \<rightarrow> T' : Latent S \<and> \<turnstile> G <e: F1"
          using C_App1(2)[of "E t" "T0 \<rightarrow> T' : Latent S" F1 t t']  `E : ctxt` `closed (E t)` `closed (E t')` C_App1(8) a C_App1 by auto
        then obtain S' G where et'ty:"\<Gamma> \<turnstile> E t' : S' ; G " and subarr:" \<turnstile> S' <: T0 \<rightarrow> T' : Latent S " and "\<turnstile> G <e: F1" by auto
        from subarr have "EX A0 A1. S' = A0 \<rightarrow> A1 : Latent S \<and> \<turnstile> T0 <: A0 \<and> \<turnstile> A1 <: T'" using subtype_arr_elim by auto
        then obtain A0 A1 where seq:"S' = A0 \<rightarrow> A1 : Latent S "" \<turnstile> T0 <: A0 "" \<turnstile> A1 <: T'" by auto
        hence "\<turnstile> T0' <: A0" using c by auto
        have no:"~ (\<turnstile> T0' <: S)" using c d by auto
        have "\<Gamma> \<turnstile> E t' : A0 \<rightarrow> A1 : Latent S ; G" using seq et'ty by auto
        thus ?case  using `\<turnstile> A1 <: T'` b d no `\<turnstile> T0' <: A0` by auto
      next
        case TT
        have "EX S T0 T0' le F1 F2.  \<Gamma> \<turnstile> E t : T0 \<rightarrow> T' : le ; F1  \<and>  \<Gamma> \<turnstile> arg : T0' ; F2 \<and> \<turnstile> T0' <: T0 \<and> le = Latent S \<and> \<turnstile> T0' <: S"
          using `\<Gamma> \<turnstile> App (E t) arg : T' ; TT` app_ty_tt_elim[of \<Gamma> "E t" arg T'] by auto
        then obtain S T0 T0' F1 F2 where  a:"\<Gamma> \<turnstile> E t : T0 \<rightarrow> T' : Latent S ; F1" and  b:"\<Gamma> \<turnstile> arg : T0' ; F2 " and c:"\<turnstile> T0' <: T0 " and d:"\<turnstile> T0' <: S"
          by auto
        have  "\<exists>S' G.  \<Gamma> \<turnstile> E t' : S' ; G  \<and> \<turnstile> S' <: T0 \<rightarrow> T' : Latent S \<and> \<turnstile> G <e: F1"
          using C_App1(2)[of "E t" "T0 \<rightarrow> T' : Latent S" F1 t t']  `E : ctxt` `closed (E t)` `closed (E t')` C_App1 a by auto
        then obtain S' G where et'ty:"\<Gamma> \<turnstile> E t' : S' ; G " and subarr:" \<turnstile> S' <: T0 \<rightarrow> T' : Latent S " and "\<turnstile> G <e: F1" by auto
        from subarr have "EX A0 A1. S' = A0 \<rightarrow> A1 : Latent S \<and> \<turnstile> T0 <: A0 \<and> \<turnstile> A1 <: T'" using subtype_arr_elim by auto
        then obtain A0 A1 where seq:"S' = A0 \<rightarrow> A1 : Latent S "" \<turnstile> T0 <: A0 "" \<turnstile> A1 <: T'" by auto
        hence "\<turnstile> T0' <: A0" using c by auto
        have "\<Gamma> \<turnstile> E t' : A0 \<rightarrow> A1 : Latent S ; G" using seq et'ty by auto
        thus ?case  using `\<turnstile> A1 <: T'` b c d `\<turnstile> T0' <: A0` by auto
      qed
    next
      case (C_App2 E v u' t t' T' F')
      have A:"closed (E t)" and B:"closed (E t')" using C_App2 closed_def trm.supp by auto
      have C:"\<Gamma> \<turnstile> App v (E t) : T' ; F'" using C_App2 by auto
      hence D:"simple_eff F'" using C_App2 closed_eff by auto
      thus ?case using C_App2 A B C
      proof (induct rule: simple_eff_cases)
        case NE
	have "\<exists>T0 T0' T1 le eff' eff''.  \<Gamma> \<turnstile> v : T0 \<rightarrow> T1 : le ; eff'  \<and>  \<Gamma> \<turnstile> E t : T0' ; eff''  \<and> \<turnstile> T0' <: T0 \<and> T1 = T'"
	  using  app_ty_elim[of \<Gamma> v "E t" T' F'] `\<Gamma> \<turnstile> App v (E t) : T' ; F'`by auto
	then obtain T0 T0' le eff' eff'' 
	  where  a:"\<Gamma> \<turnstile> v : T0 \<rightarrow> T' : le ; eff'"  " \<Gamma> \<turnstile> E t : T0' ; eff'' " "\<turnstile> T0' <: T0" by auto
	hence "\<exists>S G.  \<Gamma> \<turnstile> E t' : S ; G  \<and> \<turnstile> S <: T0' \<and> \<turnstile> G <e: eff''" using NE(2)[of "E t" T0' eff'' t t'] NE by auto
	then obtain S G where  "\<Gamma> \<turnstile> E t' : S ; G "" \<turnstile> S <: T0'" by auto
	hence "\<Gamma> \<turnstile> App v (E t') : T' ; eff.NE" using a `\<turnstile> T0' <: T0` by auto
	thus ?case by auto
      next
        case FF 
	have "\<exists>S T0 T0' le eff' eff''.  \<Gamma> \<turnstile> v : T0 \<rightarrow> T' : le ; eff'  \<and>  \<Gamma> \<turnstile> E t : T0' ; eff''  \<and> \<turnstile> T0' <: T0  \<and> le = Latent S \<and> ~ (\<turnstile> T0' <: S) \<and> E t : values \<and> closed (E t)"	  
	  using  app_ty_ff_elim[of \<Gamma> v "E t" T'] `\<Gamma> \<turnstile> App v (E t) : T' ; FF` by auto
	then obtain S T0 T0' le eff' eff'' 
	  where "\<Gamma> \<turnstile> v : T0 \<rightarrow> T' : Latent S ; eff'  "" \<Gamma> \<turnstile> E t : T0' ; eff''  "" \<turnstile> T0' <: T0 " " ~ (\<turnstile> T0' <: S) "
	  " E t : values "" closed (E t)"
	  by auto
	hence "E = (% t. t)" using  value_no_ctxt[of "E t" E t] `E : ctxt` by simp
	hence "t : values" using `E t : values` by simp
	thus ?case using `t \<notin> values` by auto
      next
        case TT
	have "\<exists>S T0 T0' le eff' eff''.  \<Gamma> \<turnstile> v : T0 \<rightarrow> T' : le ; eff'  \<and>  \<Gamma> \<turnstile> E t : T0' ; eff''  \<and> \<turnstile> T0' <: T0  \<and> le = Latent S \<and> \<turnstile> T0' <: S"
	  using  app_ty_tt_elim[of \<Gamma> v "E t" T'] `\<Gamma> \<turnstile> App v (E t) : T' ; TT` by auto
	then obtain S T0 T0' le eff' eff'' 
	  where "\<Gamma> \<turnstile> v : T0 \<rightarrow> T' : Latent S ; eff'  "" \<Gamma> \<turnstile> E t : T0' ; eff''  "" \<turnstile> T0' <: T0 " " \<turnstile> T0' <: S"
	  by auto
	hence "\<exists>S' G.  \<Gamma> \<turnstile> E t' : S' ; G  \<and> \<turnstile> S' <: T0' \<and> \<turnstile> G <e: eff''" using TT(2)[of "E t" T0' eff'' t t'] TT by auto
	then obtain S' G where  "\<Gamma> \<turnstile> E t' : S' ; G "" \<turnstile> S' <: T0'" by auto
	have "\<turnstile> S' <: S" using ` \<turnstile> S' <: T0'` `\<turnstile> T0' <: S` by auto
	hence "\<Gamma> \<turnstile> App v (E t') : T' ; TT" using `\<Gamma> \<turnstile> E t' : S' ; G ` `\<Gamma> \<turnstile> v : T0 \<rightarrow> T' : Latent S ; eff'`
	  T_AppPredTrue[of \<Gamma> v T0 T' S eff' "E t'" S' G] `\<turnstile> S' <: T0'` `\<turnstile> T0' <: T0` by auto
	thus ?case by auto
      qed
    next
      case (C_Iff E els thn u' t t' T' F')
      have A:"closed (E t)" and B:"closed (E t')" using C_Iff closed_def trm.supp by auto
      have C:"\<Gamma> \<turnstile> Iff (E t) thn els: T' ; F'" using C_Iff by auto
      hence
	bigor:
	"(\<exists>T1 T2 T3 F1 F2 F3. \<Gamma> \<turnstile> E t : T1 ; F1  \<and> \<Gamma> |+ F1 \<turnstile> thn : T2 ; F2  \<and>  \<Gamma> |- F1 \<turnstile> els : T3 ; F3  \<and> \<turnstile> T2 <: T' \<and> \<turnstile> T3 <: T' \<and> F' = eff.NE) \<or>
	(\<exists>T1 T3 F3.  \<Gamma> \<turnstile> E t : T1 ; FF  \<and>  \<Gamma> \<turnstile> els : T3 ; F3  \<and> \<turnstile> T3 <: T' \<and> F' = eff.NE) \<or>
	(\<exists>T1 T2 F2.  \<Gamma> \<turnstile> E t : T1 ; TT  \<and>  \<Gamma> \<turnstile> thn : T2 ; F2  \<and> \<turnstile> T2 <: T' \<and> F' = eff.NE)"
	using if_ty_elim[of \<Gamma> "(E t)" thn els T' F'] by auto
      thus ?case
	proof -
	  {
	    assume "(\<exists>T1 T2 T3 F1 F2 F3. \<Gamma> \<turnstile> E t : T1 ; F1  \<and> \<Gamma> |+ F1 \<turnstile> thn : T2 ; F2  \<and>  \<Gamma> |- F1 \<turnstile> els : T3 ; F3  \<and> \<turnstile> T2 <: T' \<and> \<turnstile> T3 <: T' \<and> F' = eff.NE)"
	    then obtain T1 T2 T3 F1 F2 F3 where 
	      P:"\<Gamma> \<turnstile> E t : T1 ; F1""\<Gamma> |+ F1 \<turnstile> thn : T2 ; F2""\<Gamma> |- F1 \<turnstile> els : T3 ; F3""\<turnstile> T2 <: T'""\<turnstile> T3 <: T'""F' = eff.NE"
	      by auto
	    have "closed (E t)" and "closed (E t')" using prems trm.supp closed_def by auto
	    hence "EX T1' F1'. \<Gamma> \<turnstile> E t' : T1' ; F1' \<and> \<turnstile> T1' <: T1 \<and> \<turnstile> F1' <e: F1"
	      using C_Iff(2)[of "E t" T1 F1 t t'] C_Iff P by auto
	    then obtain T1' F1' where Q:"\<Gamma> \<turnstile> E t' : T1' ; F1' "" \<turnstile> T1' <: T1 "" \<turnstile> F1' <e: F1" by auto
	    have "simple_eff F1'" and "simple_eff F1" using `closed (E t)` `closed (E t')` P Q closed_eff by auto
	    hence "\<Gamma> |+ F1 = \<Gamma>" "\<Gamma> |- F1 = \<Gamma>" "\<Gamma> |+ F1' = \<Gamma>" "\<Gamma> |- F1' = \<Gamma>" by (auto simp add: env_plus_simple_eff)
	    hence "\<Gamma> |+ F1' \<turnstile> thn : T2 ; F2 " "\<Gamma> |- F1' \<turnstile> els : T3 ; F3" using P by auto
	    hence "\<Gamma> \<turnstile> Iff (E t') thn els : T'; NE" using `\<Gamma> \<turnstile> E t' : T1' ; F1'` ` \<turnstile> T2 <: T' `` \<turnstile> T3 <: T'` by auto
	    hence ?thesis using `F' = NE` by auto
	  }
	  moreover
	  {
	    assume "(\<exists>T1 T3 F3.  \<Gamma> \<turnstile> E t : T1 ; FF  \<and>  \<Gamma> \<turnstile> els : T3 ; F3  \<and> \<turnstile> T3 <: T' \<and> F' = eff.NE)"
	    then obtain T1 T3 F3 where P:"\<Gamma> \<turnstile> E t : T1 ; FF "" \<Gamma> \<turnstile> els : T3 ; F3  "" \<turnstile> T3 <: T'"" F' = eff.NE"
	      by auto
	    have "closed (E t)" and "closed (E t')" using prems trm.supp closed_def by auto
	    hence "EX T1' F1'. \<Gamma> \<turnstile> E t' : T1' ; F1' \<and> \<turnstile> T1' <: T1 \<and> \<turnstile> F1' <e: FF"
	      using C_Iff(2)[of "E t" T1 FF t t'] C_Iff P by auto
	    then obtain T1' F1' where Q:"\<Gamma> \<turnstile> E t' : T1' ; F1' "" \<turnstile> T1' <: T1 "" \<turnstile> F1' <e: FF" by auto
	    have "F1' = FF" using Q no_sub_FF[of F1' FF] by simp
	    hence "\<Gamma> \<turnstile> E t' : T1' ; FF " using Q by auto
	    hence ?thesis using P by auto
	  }
	  moreover
	  {
	    assume "(\<exists>T1 T2 F2.  \<Gamma> \<turnstile> E t : T1 ; TT  \<and>  \<Gamma> \<turnstile> thn : T2 ; F2  \<and> \<turnstile> T2 <: T' \<and> F' = eff.NE)"
	    then obtain T1 T2 F2 where P:"\<Gamma> \<turnstile> E t : T1 ; TT "" \<Gamma> \<turnstile> thn : T2 ; F2  "" \<turnstile> T2 <: T'"" F' = eff.NE"
	      by auto
	    have "closed (E t)" and "closed (E t')" using prems trm.supp closed_def by auto
	    hence "EX T1' F1'. \<Gamma> \<turnstile> E t' : T1' ; F1' \<and> \<turnstile> T1' <: T1 \<and> \<turnstile> F1' <e: TT"
	      using C_Iff(2)[of "E t" T1 TT t t'] C_Iff P by auto
	    then obtain T1' F1' where Q:"\<Gamma> \<turnstile> E t' : T1' ; F1' "" \<turnstile> T1' <: T1 "" \<turnstile> F1' <e: TT" by auto
	    have "F1' = TT" using Q no_sub_TT[of F1' TT] by simp
	    hence "\<Gamma> \<turnstile> E t' : T1' ; TT " using Q by auto
	    hence ?thesis using P by auto
	  }
	  ultimately show ?thesis using bigor by blast
	qed
      qed        
        

lemma typing_ctxt:
  assumes a:"\<Gamma> \<turnstile> C L : T ; eff"
  and b:"C : ctxt"
  shows "EX T' eff'. \<Gamma> \<turnstile> L : T' ; eff'"
  using b a
  proof(induct C arbitrary: T eff rule: ctxt.induct )
    case C_Hole thus ?case by auto
  next
    case (C_App1 C' arg S)
    hence ih: "!! T0 eff. \<Gamma> \<turnstile> C' L : T0 ; eff  \<Longrightarrow> \<exists>T' a.  \<Gamma> \<turnstile> L : T' ; a" by simp
    obtain T0 T0' T1 le eff' eff'' where "\<Gamma> \<turnstile> C' L : T0 \<rightarrow> T1 : le ; eff'" "\<Gamma> \<turnstile> arg : T0' ; eff''" "\<turnstile> T0' <: T0 \<and> T1 = S"    
      using app_ty_elim[of \<Gamma> "C' L" arg S eff] ` \<Gamma> \<turnstile> App (C' L) arg : S ; eff` by auto
    thus ?case using ih by auto
  next
    case (C_App2 C' rator S F)
    hence ih: "!! T0 eff. \<Gamma> \<turnstile> C' L : T0 ; eff  \<Longrightarrow> \<exists>T' a.  \<Gamma> \<turnstile> L : T' ; a" by simp
    obtain T0 T0' T1 le eff' eff'' where "\<Gamma> \<turnstile> rator : T0 \<rightarrow> T1 : le ; eff'" "\<Gamma> \<turnstile> C' L : T0' ; eff''" "\<turnstile> T0' <: T0 \<and> T1 = S"    
      using app_ty_elim[of \<Gamma> rator "C' L" S F] ` \<Gamma> \<turnstile> App rator (C' L)  : S ; F` by auto
    thus ?case using ih by auto
  next
    case (C_Iff C' els thn S F)
    hence ih: "!! T0 eff. \<Gamma> \<turnstile> C' L : T0 ; eff  \<Longrightarrow> \<exists>T' a.  \<Gamma> \<turnstile> L : T' ; a" by simp
    obtain T0 eff' where  "\<Gamma> \<turnstile> C' L : T0 ; eff'"
      using if_ty_elim[of \<Gamma> "C' L" thn els S F] ` \<Gamma> \<turnstile> Iff (C' L) thn els : S ; F` by auto
    thus ?case using ih by auto
  qed

inductive_cases2 step_cases: "(e::trm) \<longrightarrow> e'"


inductive_cases bi_reduce:"BI b \<hookrightarrow> x"
inductive_cases bool_reduce:"Bool b \<hookrightarrow> x"
inductive_cases abs_reduce:"(Lam[a:T].b) \<hookrightarrow> x"
inductive_cases num_reduce:"Num n \<hookrightarrow> x"

lemma value_reduce_step:
  assumes A:"v : values" and B:"v \<longrightarrow> v'"
  shows "v \<hookrightarrow> v'"
  using B A
  proof(induct)
    fix E L R
    assume "E : ctxt" "L \<hookrightarrow> R" "E L \<in> values"
    hence "E L = L" and "E R = R" using value_no_ctxt by auto
    thus "E L \<hookrightarrow> E R" using prems by auto
  qed

lemma value_not_step:
  assumes "v : values"
  shows "~ (EX v'. v \<hookrightarrow> v')"
proof(rule ccontr, simp)
  assume "\<exists>v'. v \<hookrightarrow> v'"
  then obtain v' where A:"v \<hookrightarrow> v'" by auto
  show False using `v : values` A
    proof (induct v rule: values.induct)
      case (bi_value b) thus ?case using bi_reduce by auto
    next
      case num_value thus ?case using num_reduce by auto
    next
      case abs_value thus ?case using abs_reduce by blast
    next
      case bool_value thus ?case using bool_reduce by auto
    qed
  qed


lemma value_not_reduce:
  assumes "v : values"
  shows "~ (EX v'. v \<longrightarrow> v')"
proof (rule ccontr)
  assume "\<not> \<not> (\<exists>v'.  v \<longrightarrow> v')"
  then obtain v' where "v \<longrightarrow> v'" by auto
  hence A:"v \<hookrightarrow> v'" using value_reduce_step prems by auto
  show False using `v : values` A value_not_step by auto
qed


theorem preservation:
  assumes typed:"\<Gamma> \<turnstile> e : t ; eff" and cl:"closed e"
  and red:"e \<longrightarrow> e'"
  shows "EX t' eff'. \<Gamma> \<turnstile> e' : t' ; eff' \<and> \<turnstile> t' <: t \<and> \<turnstile> eff' <e: eff"
  using red typed cl
proof -
  have val:"valid \<Gamma>" using typing_valid typed by auto
  obtain C L R where "e = C L" "e' = C R" and "L \<hookrightarrow> R" and "C : ctxt" using red step_cases[of e e' thesis] by auto
  hence f:"EX T F. \<Gamma> \<turnstile> L : T ; F" using typed typing_ctxt by auto
  have "L \<notin> values" using `L \<hookrightarrow> R` value_not_step by auto
  have "closed L" and "closed_ctxt C" using closed_in_ctxt_closed_ctxt[of e C L] `C : ctxt`  cl `e = C L` by auto
  hence "closed R" using reduce_closed[of L R] `L  \<hookrightarrow> R` by auto
  hence "closed (C R)" and "closed (C L)"  using `closed_ctxt C` ctxt_closed[of C L] ctxt_closed[of C R] `closed L` by auto
  have " \<And>T0 F0. \<Gamma> \<turnstile> L : T0 ; F0  \<Longrightarrow> \<exists>T1 F1.  \<Gamma> \<turnstile> R : T1 ; F1  \<and> \<turnstile> T1 <: T0 \<and> \<turnstile> F1 <e: F0"
  proof -
    fix T0 F0
    show "\<Gamma> \<turnstile> L : T0 ; F0 \<Longrightarrow>  (\<exists>T1 F1.  \<Gamma> \<turnstile> R : T1 ; F1  \<and> \<turnstile> T1 <: T0 \<and> \<turnstile> F1 <e: F0)"
      using `e = C L` `C : ctxt` `L \<hookrightarrow> R` closed_in_ctxt[of C L] cl preserve_red[of \<Gamma> L T0 F0 R] `closed L` val by auto
  qed
  hence "\<exists>S G.  \<Gamma> \<turnstile> C R : S ; G  \<and> \<turnstile> S <: t \<and> \<turnstile> G <e: eff"
    using `C : ctxt` subst_in_ctxt_preserves_type[of \<Gamma> e t eff C L R] typed `e = C L` `closed (C L)` `closed (C R)`
      `L \<notin> values`by auto
  thus ?thesis using `e' = C R` by auto
qed

inductive2
step_multi :: "trm \<Rightarrow> trm \<Rightarrow> bool" (" _ \<longrightarrow>\<^sup>* _" [80,80] 80)
where 
  sm_refl:"a \<longrightarrow>\<^sup>* a"
| sm_trans:"a \<longrightarrow> b \<Longrightarrow> b \<longrightarrow>\<^sup>* c \<Longrightarrow> a \<longrightarrow>\<^sup>* c"

text {* soundness *}



lemma SE_Trans[intro]: 
  assumes"\<turnstile> F1 <e: F2 "and "\<turnstile> F2 <e: F3 " and "simple_eff F1" and "simple_eff F2" and "simple_eff F3"
  shows " \<turnstile> F1 <e: F3"
  using `simple_eff F3` prems
  proof (induct F3 rule: simple_eff_cases)
    case NE thus ?case using simple_eff_below_ne by auto
  next
    case FF thus ?case using no_sub_FF by auto
  next
    case TT thus ?case using no_sub_TT by auto
qed

lemma step_closed:
  assumes A:"closed e" and B:"e \<longrightarrow> e'"
  shows "closed e'"
proof - 
  from B obtain E L R where C:"E : ctxt"  "e = E L"  "L \<hookrightarrow> R"  "e' = E R" by induct auto
  hence D:"closed L" "closed_ctxt E" using A closed_in_ctxt_closed_ctxt[of e E L] by auto
  hence "closed R" using C reduce_closed[of L R] by auto
  hence "closed e'" using C D ctxt_closed[of E R] by auto
  thus ?thesis .
qed

lemma multi_step_closed:
  assumes A:"closed e" and B:"e \<longrightarrow>\<^sup>* e'"
  shows "closed e'"
  using B A step_closed
  by induct auto
  

theorem soundness:
  assumes A:"\<Gamma> \<turnstile> e : T ; F" and B:"e \<longrightarrow>\<^sup>* e'" and C:"~ (EX e''. e' \<longrightarrow> e'')" and E:"closed e"
  shows "EX T' F'. (e' : values \<and> \<Gamma> \<turnstile> e' : T' ; F' \<and> \<turnstile> T' <: T \<and> \<turnstile> F' <e: F)"
  using B prems
proof (induct arbitrary: \<Gamma> T F rule: step_multi.induct)
  case (sm_refl v)
  have "v : values" using sm_refl progress[of \<Gamma> v T F] by auto
  thus ?case using sm_refl by auto
next
  case (sm_trans a b c)
  have "closed b" "closed c" using `closed a` `b \<longrightarrow>\<^sup>* c` `a \<longrightarrow> b` step_closed[of a b] multi_step_closed[of b c] by auto
  then obtain T' F' where 1:"\<Gamma> \<turnstile> b : T' ; F'"  "\<turnstile> T' <: T" "\<turnstile> F' <e: F"
    using preservation[of \<Gamma> a T F b] sm_trans by auto
  then obtain T'' F'' where 2:"\<Gamma> \<turnstile> c : T'' ; F''"  "\<turnstile> T'' <: T'"  "\<turnstile> F'' <e: F'" "c : values"
    using  sm_trans(3)[of \<Gamma> T' F'] sm_trans `closed b` by blast
  have "\<turnstile> T'' <: T" using 1 2 by auto
  have 3:"simple_eff F" using prems closed_eff by auto
  have 4:"simple_eff F'" using 1 prems closed_eff `closed b` by auto
  have 5:"simple_eff F''" using  prems closed_eff `closed c` by auto
  from 3 4 5 have "\<turnstile> F'' <e: F" using SE_Trans[of F'' F' F] 1 2 by auto
  thus ?case using 2 `\<turnstile> T'' <: T`  by auto
qed


lemma unique_decomposition: 
  assumes a:"closed e"
  shows "\<lbrakk>E : ctxt; E t = e; E' : ctxt; E' t' = e\<rbrakk> \<Longrightarrow> E = E'"
  using a
  proof (nominal_induct e rule: trm.induct)
    case (Var v)
    have f1:"E = (%t. t)" using Var by cases auto
    have f2:"E'= (%t. t)" using `E' : ctxt` Var by cases auto
    from f1 f2 show ?case by simp
  next
    case (Bool c)
    have f1:"E = (%t. t)" using Bool by cases auto
    have f2:"E'= (%t. t)" using `E' : ctxt` Bool by cases auto
    from f1 f2 show ?case by simp
  next
    case (Num c)
    have f1:"E = (%t. t)" using Num by cases auto
    have f2:"E'= (%t. t)" using `E' : ctxt` Num by cases auto
    from f1 f2 show ?case by simp
  next
    case Abs
    have f1:"E = (%t. t)" using `E : ctxt` Abs by cases auto
    have f2:"E'= (%t. t)" using `E' : ctxt` Abs by cases auto
    from f1 f2 show ?case by simp
  next
    case (Iff tst thn els)
    {
      assume "tst \<notin> values"
      hence "EX E L R. tst = E L \<and> E \<in> ctxt \<and> L \<hookrightarrow> R" using decomposition 
      have f1:"E = (%t. t)" using `E : ctxt` Iff apply cases apply (auto  simp add: trm.inject)
      have f2:"E'= (%t. t)" using `E' : ctxt` Iff by cases auto
      from f1 f2 have ?case by simp
      {
    oops
    
    


