(module semantic-analysis mzscheme
  (require (lib "class.ss"))
  (require (prefix ast: "../syntactic/ast.ss"))
  (require "analyze-ast.ss")
  (require "class-resolver.ss")
  (require "class-resolver-impl.ss")
  (require "semantic-object.ss")
  (require "../syntactic/parser.ss")
  (require "../config.ss")
  (require "../transform/select.ss")
  (require (lib "pretty.ss"))
  (require (lib "match.ss"))
  (require (lib "etc.ss"))
  (require (lib "list.ss"))
  (require (planet "pathlike.ss" ("ryanc" "scripting.plt" 1 0)))
  
  (current-classpath (list (build-path "/tmp")))
  ;(current-classpath (list (build-path "/usr/java/jdk1.5.0_01/jre/lib/rt.jar")))

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
    (let* ((imports (ast:compilation-unit-imports ast))
          (imports-list (map import->list imports))
          (types (select ast:type-spec? ast)))
      ;(printf "Imports ~n")
      ;(pretty-print imports)
      ;(pretty-print (map import->list imports))
     ; (printf "Types ~n")
;      (pretty-print types)
      ;(pretty-print (map type-spec->type-name types))
      (map (lambda (t) (list (really-resolve imports-list (type-spec->type-name t))
                             t))  types)
      ))
  
  ;(define tys (all-types x))
  ;(define class-tys (filter (λ (x) (is-a?  x class%)) tys))
  
  (define (class%? x) (is-a? x class%))
  (define (class/interface-name c) (send c get-name))
  
  (define (print-some-errors ast)
    (let ((types (all-types ast)))
      (for-each 
       (match-lambda
         [((? class%? c) tyspec) (printf "Used a class ~a where you could have used interfaces ~a~n at source ~a~n~n"
                                          (class/interface-name c)
                                          (map class/interface-name (send c get-interfaces))
                                          (ast:ast-src tyspec))]
         [_ (void)])
       types)))
  
  (define (check pl)
    (print-some-errors (parse (open-input-file (pathlike->path pl)))))


  
  )
