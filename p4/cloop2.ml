#load "q_MLast.cmo";;
#load "pa_extend.cmo";;

open Pcaml
  
let gensym =
  let cnt = ref 0 in
  fun var ->
    let x = incr cnt; !cnt in
    var ^ "_gensym" ^ string_of_int x
			
let id x = x

let gen_for loc v iv wh nx e =
  let loop_fun = gensym "iter" in
  <:expr<
  let rec $lid:loop_fun$ $lid:v$ = 
    if $wh$ then do { (id $e$); $lid:loop_fun$ $nx$ } else ()
  in
  $lid:loop_fun$ $iv$ >>

EXTEND 
    expr: LEVEL "expr1"
    [ [ "for"; v = LIDENT; iv = expr LEVEL "simple";
	wh = expr LEVEL "simple"; nx = expr LEVEL "simple";
	"do"; e = expr; "done" -> gen_for loc v iv wh nx e ] ]
    ;
END
