signature ESCAPE = 
sig
    type void 
    val coerce : void -> 'a 
    val escape : (('a -> void) -> 'a) -> 'a 
end

structure Escape : ESCAPE = 
struct
datatype void = VOID of void 
fun coerce (VOID v) = coerce v 

fun escape f
  = SMLofNJ.Cont.callcc (fn k => f (fn x => SMLofNJ.Cont.throw k x)) 
end

signature CONTROL = 
sig
    type ans 
    val shift : (('a -> ans) -> ans) -> 'a 
    val reset : (unit -> ans) -> ans 
end

functor Control (type ans) : CONTROL = 
struct

open Escape

exception MissingReset

val mk : (ans -> void) ref = ref (fn _ => raise MissingReset) 

fun abort x = coerce (!mk x) 

type ans = ans 

fun reset t
  = escape (fn k => 
	       let 
		   val m = !mk
	       in 
		   mk := (fn r => (mk := m; k r));
		   abort (t ()) 
	       end) 
fun shift h
  = escape 
	(fn k => 
	    abort (h (fn v => 
			 reset (fn () => coerce (k v))))) 

end 
