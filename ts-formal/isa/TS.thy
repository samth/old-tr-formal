(*
New Version
Started Jan 15, 2009

Using Isabelle repository snapshot 2eadbc24de8c (13-Jan-2009)

*)

theory TS
imports Nominal

begin

atom_decl name

datatype pe = Car | Cdr

datatype builtin = ADD1 | ZEROP| CAR | CDR | NOT | CONSP | NUMBERP | BOOLEANP | PROCEDUREP

(* Types *)
datatype ty =  
  Top | N | TT | FF | Arr "ty" "ty" "fh" ("_ \<rightarrow> _ : _" [100,100] 100) | Union "ty list"  
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
  "pi\<bullet>(\<tau> \<rightarrow> \<sigma> : L) = ((pi\<bullet>\<tau>) \<rightarrow> (pi\<bullet>\<sigma>) : (pi\<bullet>L))"
  "pi\<bullet>(Union l) = Union (pi\<bullet>l)" 

  "pi\<bullet>(FH l1 l2) = FH (pi\<bullet>l1)(pi\<bullet>l2)"

  "pi\<bullet>BotH = BotH"
  "pi\<bullet>(TEH t l) = TEH (pi\<bullet>t) (pi\<bullet>l)"
  "pi\<bullet>(NTEH t l) = NTEH (pi\<bullet>t) (pi\<bullet>l)"

declare perm_pe.simps[eqvt]
declare perm_ty.simps[eqvt]
declare perm_bi.simps[eqvt]

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

lemma perm_ty_F_ty_list[simp]:
  fixes pi ::"name prm"
  and   \<tau>  ::"ty"
  and   Ts ::"ty list"
  and   f  ::"fh"
  and   p  :: "ph"
  and ps :: "ph list"
  and ps2 :: "ph list"
  shows "pi\<bullet>\<tau> = \<tau>" and "pi\<bullet>f = f" and "pi\<bullet>p = p" and "pi\<bullet>Ts = Ts" and "pi\<bullet>ps = ps" and "pi\<bullet>ps2 = ps2"
  by (induct \<tau> and f and p rule: ty_fh_ph.inducts) auto

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
  fixes x ::"name"
  and   \<tau>  ::"ty"
  and   f  ::"fh"
  and   p  :: "ph"
  and  bi :: builtin
  and pe :: pe
  shows "x\<sharp>\<tau>" and "x\<sharp>f" and "x\<sharp>p" and "x\<sharp>pe" and "x\<sharp>bi"
  by (simp add: fresh_def supp_def)+

nominal_datatype trm = 
    Var "name"
  | App "trm" "trm"
  | Abs "\<guillemotleft>name\<guillemotright>trm" "ty"
  | Iff "trm" "trm" "trm"
  | Num "nat"
  | Bool "bool"
  | BI "builtin"
  | Cons "trm" "trm"

abbreviation
  "lam" :: "name \<Rightarrow> ty \<Rightarrow> trm \<Rightarrow> trm" ("Lam [_:_]._" [100,100,100] 100) where
  "Lam[x:T].b \<equiv> trm.Abs x b T"

nominal_primrec
  size :: "trm \<Rightarrow> nat"
  where
  "size (Var x) = 1"
  | "size (BI b) = 1"
  | "size (Bool b) = 1"
  | "size (Num b) = 1"
  | "size (App t1 t2) = (max (size t1) (size t2)) + 1"
  | "size (TS.Cons t1 t2) = (max (size t1) (size t2)) + 1"
  | "size (Iff t1 t2 t3) = (max (size t1) (max (size t2) (size t3))) + 1"
  | "size (Lam [a:T].e) = (size e) + 1"
  by (auto simp add: fresh_nat, finite_guess+, fresh_guess+)

 instance trm :: size ..



  
  

end