open Pcaml;;
  
let compose f g = fun x -> f (g x)

EXTEND
  expr: AFTER "apply"
  [[ f = expr; "o"; g = expr -> <:expr< compose $f$ $g$ >> ]];
  END;;
