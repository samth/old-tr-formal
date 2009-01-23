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

atom_decl name

defs (unchecked overloaded)
perm_fmap_def[simp]: "pi \<bullet> (f ::('a,'b) fmap) == Abs_fmap (pi \<bullet> (Rep_fmap f))"

lemma perm_fmap2:
  fixes f :: "('k, 'v) fmap" 
  and pi :: "'a prm"
  shows "pi \<bullet> f = Abs_fmap (\<lambda>(x::'k). pi\<bullet>(f@[((rev pi)\<bullet>x)]))"
  by (cases f) (auto simp add: Abs_fmap_inverse perm_fun_def)

lemma perm_preserves_fmap:
  fixes 
  "finite (dom "

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