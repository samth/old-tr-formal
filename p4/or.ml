#load "q_MLast.cmo";;
#load "pa_extend.cmo";;

open Pcaml

let gensym =
  let cnt = ref 0 in
  fun var ->
    let x = incr cnt; !cnt in
    var ^ "_gensym" ^ string_of_int x

let gen_or loc a b =
  let tmp = gensym "tmp" in
  <:expr<
    let $lid:tmp$ = $a$ in
    if $lid:tmp$  then $lid:tmp$ else $b$
   >>

EXTEND
  expr: LEVEL "expr1"
    [ [ "orr"; "("; a = expr LEVEL "simple";   b = expr LEVEL "simple"; ")" -> gen_or loc a b ] ];
END
