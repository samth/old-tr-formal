(module libc mzscheme
  (require (lib "foreign.ss"))
  (unsafe!)

  (define _FILE _int)
  
  (define fopen (get-ffi-obj "fopen" #f (_fun _string _string -> _FILE)))

  (define fclose (get-ffi-obj "fclose" #f (_fun _FILE -> _int)))

  (provide _FILE fopen fclose)
  
  )
