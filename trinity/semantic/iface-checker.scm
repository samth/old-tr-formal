(module iface-checker mzscheme
  (require (lib "class.ss"))
  (require (prefix ast: "../syntactic/ast.ss"))
  ;(require "analyze-ast.ss")
  (require "class-resolver.ss")
  (require "class-resolver-impl.ss")
  (require "semantic-object.ss")
  (require "../syntactic/parser.ss")
  (require "../config.ss")
  (require "../transform/select.ss")
  ;(require (lib "pretty.ss"))
  (require (lib "match.ss"))
  (require (lib "etc.ss"))
  (require (lib "list.ss"))
  (require (planet "pathlike.ss" ("ryanc" "scripting.plt" 1 0)))
  
  (current-classpath (list (build-path "/tmp")))
  ;(current-classpath (list (build-path "/usr/java/jdk1.5.0_01/jre/lib/rt.jar")))

  (current-class-resolver (new class-resolver%))
  
  (define (really-resolve imports t)
    ;(printf "really-resolve ~a~n" t)
    (cond 
      [(lookup-type t)]
      ;[(not (null? (type-name-package t))) #f]
      [else (let loop ((imps (cons '(java lang) imports)))
              (cond 
                [(null? imps) #f]
                [(lookup-type (make-type-name (car imps) (type-name-type t)))]
                [else (loop (cdr imps))]))]))
  
            
  
  ;(semantic-analysis x)
  
  (define (type-spec->type-name nm)
    (match (ast:type-spec-base-type nm)
      [(? ast:primitive-type? nm) (build-type-name (list nm))]
      [($ ast:name _ (($ ast:id _ pkgs) ...) ($ ast:id _ nm))
       (make-type-name pkgs nm)]))
  
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
  
  (define (collect f . l)
    (filter (lambda (x) x) (apply map f l)))
  
  (define (find-errors ast)
    (let ((types (all-types ast)))
      (collect 
       (match-lambda
         [((? class%? c) tyspec) (let ((ifaces (send c get-interfaces)))
                                   (if (null? ifaces) #f
                                       (list 
                                        (class/interface-name c)
                                        (map class/interface-name (send c get-interfaces))
                                        (ast:ast-src tyspec))))]
         [_ #f])
       types)))
  
  (define check (compose find-errors parse open-input-file pathlike->path))

  (define check-str (compose find-errors parse))
  
  (provide check check-str find-errors)

  
  )
