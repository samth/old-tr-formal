(module libc mzscheme
  (require (lib "foreign.ss"))
  (unsafe!)

  (define _FILE _int)
  
  (define fopen (get-ffi-obj "fopen" "" (_fun _string _string -> _FILE)))

  (define fclose (get-ffi-obj "fclose" "" (_fun _FILE -> _int)))

  (provide (all-defined))
  
  )
