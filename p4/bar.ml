let main () = 
  let i = ref 0 in
  repeat print_int !i; incr i until !i = 10;
  print_newline ()
let _ = main()
