(module useful mzscheme 
  (require (lib "match.ss") (lib "etc.ss") (lib "list.ss"))
  (provide (all-defined))

  (define s->s symbol->string)
  
  ; sort order: 
  ; symbol
  ; empty list
  ; list
  ; struct
  
  ; alts is a list of types
  (define-struct union-ty (alts) (make-inspector))
  
  ; name is a symbol
  (define-struct ty-ref (name) (make-inspector))
  
  ; args is a list of types, result is a type
  (define-struct fun-ty (args result) (make-inspector))
  
  (define (compare/r a b) (compare b a))
  
  (define (compare a b)
    (cond
      [(symbol? a)
       (if (symbol? b) (compare-sym a b) #t)]
      [(symbol? b) #f]
      [(null? a) 
       (if (null? b) #t #t)]
      [(null? b) #f]
      [(cons? a)
       (if (cons? b) (compare-list a b) #t)]
      [(list? b) #f]
      [(ty-ref? a)
       (if (ty-ref? b) (compare-ty-ref a b) #t)]
      [(ty-ref? b) #f]
      [(fun-ty? a)
       (if (fun-ty? b) (compare-fun-ty a b) #t)]
      [(fun-ty? b) #f]
      [(union-ty? a)
       (if (union-ty? b) (compare-union-ty a b) #t)]
      [(union-ty? b) (error "impossible")]
      [else (error "wtf")]; this should never happen
      )
    )
  
  (define compare-ty-ref
    (match-lambda*
      [(($ ty-ref t1) ($ ty-ref t2)) (compare-sym t1 t2)]))
  
  (define compare-union-ty 
    (match-lambda*
      [(($ union-ty alts1) ($ union-ty alts2))
       (compare-list alts1 alts2)]))
       
  
  (define compare-fun-ty 
    (match-lambda*
      [(($ fun-ty args1 ret1) ($ fun-ty args2 ret2))
       (if (compare-list args1 args2) 
           (compare ret1 ret2) #f)]))
  
  (define (compare-sym s1 s2)
    (string<=? (s->s s1) (s->s s2)))
  
  (define (compare-list l1 l2)
    (and (compare (car l1) (car l2))
         (compare (cdr l1) (cdr l2))))
  
  )