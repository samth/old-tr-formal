theory FMap
imports Nominal
begin

typedef ('a,'b) fmap = "{f::'a => 'b option. finite (dom f)}"
proof
 show "empty : {f. finite (dom f)}" by simp
qed

constdefs
lookup :: "('a,'b) fmap \<Rightarrow> 'a ~=> 'b" ("_@[_]" [990,990] 999)
lookup_def[simp]: "f@[a] == (Rep_fmap f) a"

insert :: "('a,'b) fmap \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a,'b) fmap" 
insert_def[simp]: "insert f a b == Abs_fmap (%x . (if x = a then Some b else f@[a]))"

defs (unchecked overloaded)
perm_fmap_def[simp]: "pi \<bullet> (f ::('a,'b) fmap) == Abs_fmap (pi \<bullet> (Rep_fmap f))"

lemma perm_fmap2:
  fixes f :: "('k, 'v) fmap" 
  and pi :: "'a prm"
  shows "pi \<bullet> f = Abs_fmap (\<lambda>(x::'k). pi\<bullet>(f@[((rev pi)\<bullet>x)]))"
  by (cases f) (auto simp add: Abs_fmap_inverse perm_fun_def)

lemma fmap_induct:
  fixes f :: "('k, 'v) fmap"
  and P :: "('k, 'v) fmap \<Rightarrow> bool"
  assumes a1:"P empty"
  and a2:"P f' \<Longrightarrow> P "

lemma perm_preserves_fmap:
  fixes pi :: "'a prm" and f :: "('k, 'v) fmap"
  shows "finite (dom (pi \<bullet> Rep_fmap f))"
proof (simp only: perm_fun_def)
  let ?f = "\<lambda>x. pi \<bullet> Rep_fmap f (rev pi \<bullet> x)"
  have "(Rep_fmap f) : fmap" using Rep_fmap by auto
  hence "finite (dom (Rep_fmap f))"  using fmap_def by auto
  thus "finite (dom ?f)"
    thm finite.induct
    proof (induct rule: finite.induct)
  have "!! x. ((?f x = None) = (Rep_fmap f (rev pi \<bullet> x) = None))"
  proof -
    fix x
    show "((?f x = None) = (Rep_fmap f (rev pi \<bullet> x) = None))"
      by (cases "Rep_fmap f (rev pi \<bullet> x) = None") auto
  qed
  also have "finite (dom (Rep_fmap f))" by fact
  ultimately 
    apply auto
  
  apply 
  apply auto
    thm Abs_fmap_inverse[of "pi \<bullet> f"]

lemma lookup_eqvt:
  fixes f :: "('k, 'v) fmap" 
  and k :: 'k
  and pi :: "'a prm"
  shows "pi \<bullet> (f@[k]) = (pi \<bullet> f)@[(pi \<bullet> k)]"
  proof (auto simp add: perm_fmap2 Abs_fmap_inverse Rep_fmap_inverse)
    have "Rep_fmap (Abs_fmap (pi \<bullet> Rep_fmap f)) = (pi \<bullet> Rep_fmap f)"
      using Abs_fmap_inverse[of "(pi \<bullet> Rep_fmap f)"]
      using Rep_fmap[of "(pi \<bullet> Rep_fmap f)"]
  apply auto



end