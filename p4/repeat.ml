open Pcaml;;
EXTEND
expr: LEVEL "expr1"
[[ "repeat"; e1 = expr; "until"; e2 = expr ->
  <:expr<do { $e1$; while not $e2$ do { $e1$; } } >>]];
END;;
