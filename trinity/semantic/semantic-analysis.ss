(module semantic-analysis mzscheme
  (require (lib "class.ss"))
  (require (prefix ast: "../syntactic/ast.ss"))
  (require "analyze-ast.ss")
  (require "class-resolver.ss")
  (require "class-resolver-impl.ss")
  (require "../syntactic/parser.ss")
  (require "../config.ss")
  (require "../transform/select.ss")
  (require (lib "pretty.ss"))
  (require (lib "match.ss"))
  
  (current-classpath (list (build-path "/tmp")))

  (current-class-resolver (new class-resolver%))

  (define (semantic-analysis asts)
    ;(lookup-type (build-type-name '(java lang Object)))
    (for-each analyze-ast asts)
    #;(current-class-resolver))
  
  (define (resolve t)
    (printf "resolve: ~a~n" t)
    (lookup-type (build-type-name t)))
  
  (define (id x) x)
  
  (define (type-name->list tn)
    (append (type-name-package tn) (list (type-name-type tn))))
  
  (define (really-resolve imports t)
    (printf "really-resolve ~a~n" t)
    (cond 
      [(resolve (type-name->list t))]
      ;[(not (null? (type-name-package t))) #f]
      [else (let loop ((imps (cons '(java lang) imports)))
              (cond 
                [(null? imps) #f]
                [(resolve (append (car imps) (type-name->list t)))]
                [else (loop (cdr imps))]))]))
  
  (define x (parse "import java.util.Collects ;
class C{int x;java.lang.Object y;Object z;}"))
            
  
  ;(semantic-analysis x)
  
  (define (type-spec->type-name nm)
    (match (ast:type-spec-base-type nm)
      [(? ast:primitive-type? nm) (build-type-name (list nm))]
      [($ ast:name _ (($ ast:id _ pkgs) ...) ($ ast:id _ nm))
       (build-type-name (append pkgs (list nm)))]))
  
  (define (import->list imp)
    (match imp
      [($ ast:import _ ($ ast:name _ (($ ast:id _ pkgs) ...) ($ ast:id _ last)) _)
       (append pkgs (list last))]))
  
  
  (define (all-types ast)
    (let ((imports (ast:compilation-unit-imports ast))
          (types (select ast:type-spec? ast)))
      (printf "Imports ~n")
      ;(pretty-print imports)
      (pretty-print (map import->list imports))
      (printf "Types ~n")
;      (pretty-print types)
      (pretty-print (map type-spec->type-name types))
      (pretty-print (map (lambda (t) (really-resolve (map import->list imports) t)) (map type-spec->type-name types)))
      ))
  
  (all-types x)

  (provide semantic-analysis))
