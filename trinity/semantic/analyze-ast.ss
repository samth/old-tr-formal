(module analyze-ast mzscheme
  (require (lib "match.ss"))
  (require "../syntactic/ast.ss")

  (define (analyze-ast ast)
    (match ast
      [($ compilation-unit _ package imports classes)
       (printf "visiting: ~a~n" (map (lambda (decl)
                                       (and decl (decl-name decl)))
                                     classes))
       #f]))

  (provide analyze-ast))
