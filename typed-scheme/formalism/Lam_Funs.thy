(* $Id: Lam_Funs.thy,v 1.4 2006/11/27 13:50:21 urbanc Exp $ *)

theory Lam_Funs
imports Nominal
begin

atom_decl name

nominal_datatype lam = Var "name"
                     | App "lam" "lam"
                     | Lam "\<guillemotleft>name\<guillemotright>lam" ("Lam [_]._" [100,100] 100)

text {* depth of a lambda-term *}

consts 
  depth :: "lam \<Rightarrow> nat"

nominal_primrec
  "depth (Var x) = 1"
  "depth (App t1 t2) = (max (depth t1) (depth t2)) + 1"
  "depth (Lam [a].t) = (depth t) + 1"
  apply(finite_guess add: perm_nat_def)+
  apply(rule TrueI)+
  apply(simp add: fresh_nat)
  apply(fresh_guess add: perm_nat_def)+
  done

constdefs 
smaller_than :: "(lam * lam) set"
"smaller_than == measure depth"


lemma wf_st:"wf smaller_than" using wf_measure[of depth] smaller_than_def by auto

thm wf_induct[of smaller_than]

lemma lam_cases[case_names Var App Lam]:
  fixes P::"lam \<Rightarrow> bool"
  assumes a1:"!! name. P (Var name)"
  and a2:"!! t1 t2. P (App t1 t2)"
  and a3:"!! a b. P (Lam [a].b)"
  shows "P lam"
  using prems
  by (nominal_induct lam rule: lam.induct) auto


lemma depth_pos: 
  fixes t::lam
  shows "depth t > 0"
  proof (induct rule: wf_induct[of smaller_than])
    case 1 thus ?case using wf_st by auto
  next
    case (2 s) thus ?case
      proof (induct s rule: lam_cases)
	case (Var v)
	have "depth (Var v) = 1" by simp
	thus ?case by simp
      next
	case (App t1 t2)
	have A:"depth t1 < depth (App t1 t2)" by auto
	hence "(t1 , App t1 t2) : smaller_than "
	  by (simp add: smaller_than_def measure_def)
	hence "depth t1 > 0" using App by auto
	hence "depth (App t1 t2) > 0" using A by simp
	thus ?case by auto
      next
	case (Lam x t1)
	have A:"depth t1 < depth (Lam[x].t1)" by auto
	hence "(t1 , Lam[x].t1) : smaller_than "
	  by (simp add: smaller_than_def measure_def)
	hence "depth t1 > 0" using Lam by auto
	hence "depth (Lam[x].t1) > 0" using A by simp
	thus ?case by auto
      qed
    qed

thm lam.induct

lemma depth_eqvt:
  fixes pi :: "name prm"
  and   t  :: "lam"
  shows "depth (pi\<bullet>t) = depth t"
by (nominal_induct t rule: lam.induct) auto

lemma lam_comp_induct1[consumes 0, case_names Var App Lam]:
  fixes P::"'a::fs_name \<Rightarrow> lam \<Rightarrow> bool"
  and t::"lam"
  and x::"'a::fs_name"
  assumes a1:"!! n z. (!! x t. (t,Var n) : smaller_than \<Longrightarrow> P x t) \<Longrightarrow> P z (Var n)"
  and a2:"!! t1 t2 z. (!! x t. (t,App t1 t2) : smaller_than \<Longrightarrow> P x t) \<Longrightarrow> P z (App t1 t2)"
  and a3:"!! a b z. \<lbrakk>a \<sharp> z ; (!! x t. (t,Lam[a].b) : smaller_than \<Longrightarrow> P x t)\<rbrakk> \<Longrightarrow> P z (Lam[a].b)"
  shows "P x t"
  proof (induct arbitrary: x rule: wf_induct[of smaller_than])
    case 1 thus ?case using wf_st by auto
  next
    case (2 s x) thus ?case
      proof (induct s  rule: lam_cases)
	case (Var v) thus ?case using a1[of v x] by auto
      next
        case (App t1 t2) thus ?case using a2 by auto
      next
        case (Lam a b)
        have f: "\<exists>c::name. c\<sharp>(a,b,x)"
	  by (rule exists_fresh', simp add: fs_name1)
        then obtain c::"name" 
	  where f1: "c\<noteq>a" and f2: "c\<sharp>x" and f3: "c\<sharp>b"
	  by (force simp add: fresh_prod fresh_atm)
        have "depth b = depth (([(c,a)])\<bullet>b)" using depth_eqvt by simp
        hence "depth (Lam[a].b) = depth (Lam[c].(([(c,a)])\<bullet>b))" by simp
        hence A:"!! t. (t,Lam[c].(([(c,a)])\<bullet>b))  : smaller_than \<Longrightarrow> (t,Lam[a].b) : smaller_than"
	  by (simp add: smaller_than_def measure_def)
        have "\<And>x t. (t, Lam [a].b) \<in> smaller_than \<Longrightarrow> P x t" using Lam by auto
        hence "\<And>x t. (t, Lam [c].(([(c,a)])\<bullet>b)) \<in> smaller_than \<Longrightarrow> P x t" using A by auto
        hence x: "P x (Lam [c].(([(c,a)])\<bullet>b))" using a3 f2 by simp
        have alpha1: "(Lam [c].([(c,a)]\<bullet>(b))) = (Lam [a].b)" using f1 f3
	  by (simp add: lam.inject alpha)
        hence "P x (Lam[a].b)" using x by simp
        thus ?case by simp
      qed
    qed

lemma lam_comp_induct:
  fixes P::"'a::fs_name \<Rightarrow> lam \<Rightarrow> bool"
  and t::"lam"
  and x::"'a::fs_name"
  assumes a1:"!! n z. (!! x t. (t,Var n) : smaller_than \<Longrightarrow> P x t) \<Longrightarrow> P z (Var n)"
  and a2:"!! t1 t2 z. (!! x t. (t,App t1 t2) : smaller_than \<Longrightarrow> P x t) \<Longrightarrow> (!! x. P x t1) \<Longrightarrow> (!! x . P x t2) \<Longrightarrow> P z (App t1 t2)"
  and a3:"!! a b z. (!! x t. (t,Lam[a].b) : smaller_than \<Longrightarrow> P x t) \<Longrightarrow> (!! x . P x b) \<Longrightarrow> a \<sharp> z \<Longrightarrow> P z (Lam[a].b)"
  shows "P x t"
  proof (nominal_induct t avoiding: x rule: lam_comp_induct1)
    case App thus ?case using a2 
      by (auto simp add: smaller_than_def measure_def)
  next
    case Var thus ?case using a1
      by (auto simp add: smaller_than_def measure_def)
  next
    case Lam thus ?case using a3
      by (auto simp add: smaller_than_def measure_def)
  qed
      


text {* free variables of a lambda-term *}

consts 
  frees :: "lam \<Rightarrow> name set"

nominal_primrec (invariant: "\<lambda>s::name set. finite s")
  "frees (Var a) = {a}"
  "frees (App t1 t2) = (frees t1) \<union> (frees t2)"
  "frees (Lam [a].t) = (frees t) - {a}"
apply(finite_guess add: perm_insert perm_set_def)
apply(finite_guess add: perm_union)
apply(finite_guess add: pt_set_diff_eqvt[OF pt_name_inst, OF at_name_inst] perm_insert)
apply(simp add: perm_set_def)
apply(simp add: fs_name1)
apply(simp)+
apply(simp add: fresh_def)
apply(simp add: supp_of_fin_sets[OF pt_name_inst, OF at_name_inst, OF fs_at_inst[OF at_name_inst]])
apply(simp add: supp_atm)
apply(force)
apply(fresh_guess add: perm_insert perm_set_def)
apply(fresh_guess add: perm_union)
apply(fresh_guess add: pt_set_diff_eqvt[OF pt_name_inst, OF at_name_inst] perm_insert)
apply(simp add: perm_set_def)
done

lemma frees_equals_support:
  shows "frees t = supp t"
by (nominal_induct t rule: lam.induct)
   (simp_all add: lam.supp supp_atm abs_supp)

text {* capture-avoiding substitution *}

lemma eq_eqvt:
  fixes pi::"name prm"
  and   x::"'a::pt_name"
  shows "pi\<bullet>(x=y) = ((pi\<bullet>x)=(pi\<bullet>y))"
  apply(simp add: perm_bool perm_bij)
  done

consts
  subst :: "lam \<Rightarrow> name \<Rightarrow> lam \<Rightarrow> lam"  ("_[_::=_]" [100,100,100] 100)

nominal_primrec
  "(Var x)[y::=t'] = (if x=y then t' else (Var x))"
  "(App t1 t2)[y::=t'] = App (t1[y::=t']) (t2[y::=t'])"
  "x\<sharp>(y,t') \<Longrightarrow> (Lam [x].t)[y::=t'] = Lam [x].(t[y::=t'])"
apply(finite_guess add: eq_eqvt perm_if fs_name1)+
apply(rule TrueI)+
apply(simp add: abs_fresh)
apply(fresh_guess add: eq_eqvt perm_if fs_name1)+
done

lemma subst_eqvt[simp]:
  fixes pi:: "name prm"
  and   t1:: "lam"
  and   t2:: "lam"
  and   a :: "name"
  shows "pi\<bullet>(t1[b::=t2]) = (pi\<bullet>t1)[(pi\<bullet>b)::=(pi\<bullet>t2)]"
apply(nominal_induct t1 avoiding: b t2 rule: lam.induct)
apply(auto simp add: perm_bij fresh_prod fresh_atm fresh_bij)
done

lemma subst_supp: 
  shows "supp(t1[a::=t2]) \<subseteq> (((supp(t1)-{a})\<union>supp(t2))::name set)"
apply(nominal_induct t1 avoiding: a t2 rule: lam.induct)
apply(auto simp add: lam.supp supp_atm fresh_prod abs_supp)
apply(blast)+
done

text{* parallel substitution *}

consts
  "domain" :: "(name\<times>lam) list \<Rightarrow> (name list)"
primrec
  "domain []    = []"
  "domain (x#\<theta>) = (fst x)#(domain \<theta>)" 

consts
  "apply_sss"  :: "(name\<times>lam) list \<Rightarrow> name \<Rightarrow> lam" (" _ < _ >" [80,80] 80)
primrec  
"(x#\<theta>)<a>  = (if (a = fst x) then (snd x) else \<theta><a>)" 

lemma apply_sss_eqvt:
  fixes pi::"name prm"
  assumes a: "a\<in>set (domain \<theta>)"
  shows "pi\<bullet>(\<theta><a>) = (pi\<bullet>\<theta>)<pi\<bullet>a>"
using a
by (induct \<theta>)
   (auto simp add: perm_bij)

lemma domain_eqvt:
  fixes pi::"name prm"
  shows "((pi\<bullet>a)\<in>set (domain \<theta>)) = (a\<in>set (domain ((rev pi)\<bullet>\<theta>)))"
apply(induct \<theta>)
apply(auto)
apply(perm_simp)+
done

consts
 psubst :: "lam \<Rightarrow> (name\<times>lam) list \<Rightarrow> lam" ("_[<_>]" [100,100] 900)

nominal_primrec
  "(Var x)[<\<theta>>] = (if x\<in>set (domain \<theta>) then \<theta><x> else (Var x))"
  "(App t1 t2)[<\<theta>>] = App (t1[<\<theta>>]) (t2[<\<theta>>])"
  "x\<sharp>\<theta>\<Longrightarrow>(Lam [x].t)[<\<theta>>] = Lam [x].(t[<\<theta>>])"
apply(finite_guess add: domain_eqvt apply_sss_eqvt fs_name1)+
apply(rule TrueI)+
apply(simp add: abs_fresh)
apply(fresh_guess add: domain_eqvt apply_sss_eqvt fs_name1)+
done

end
