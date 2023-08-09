
theory Test
imports Nominal

begin

atom_decl a

nominal_datatype x = T a 

datatype y = Y "x list"

primrec (unchecked perm_y)
"pi \<bullet> Y xs = Y (pi \<bullet> xs)"

instance y :: pt_a
apply intro_classes
apply auto

end
