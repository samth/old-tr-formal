open Pcaml;;

let gensym =
  let cnt = ref 0 in
  fun var ->
    let x = incr cnt; !cnt in
    var ^ "_gensym" ^ string_of_int x

let rec gen_or loc =
  function 
      [] -> <:expr< false >>
    | [a]  -> <:expr< $a$ >>
    | a::b -> 
	 let tmp = gensym "tmp" in
	 <:expr<
	 let $lid:tmp$ = $a$ in
	 if $lid:tmp$  then $lid:tmp$ else $gen_or loc b$
	 >>


EXTEND
  expr: LEVEL "expr1"
    [ 
      [ "orr";  a = LIST0 expr LEVEL "simple"  -> gen_or loc a ]   
    ];
END
