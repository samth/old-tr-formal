;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; ast.ss
;; $Id: ast.ss,v 1.10 2005/02/02 15:06:47 cobbe Exp $
;;
;; Defines the AST types used for the ClassicJava system.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(module ast mzscheme

  (require (lib "contract.ss")
           )
  (require (lib "utils.ss" "reduction-semantics" "examples" "classic-java"))

  #| ID ::= any symbol except those in RESERVED-WORDS, BINARY-PRIMS, and
            UNARY-PRIMS below

     Class-Name ::= ID | 'Object
     Defn-Name ::= ID     ;; those names legal for user-defined classes
     Type-Name ::= Class-Name | 'int | 'bool
     Method-Name ::= ID
     Field-Name ::= ID
     Arg-Name ::= ID

     Unary-Prim ::= 'zero? | 'not
     Binary-Prim ::= '+ '- '* 'and 'or '=
  |#

  (define BINARY-PRIMS '(+ - * == and or))
  (define UNARY-PRIMS '(zero? not))
  (define RESERVED-WORDS '(class Object new ref send super this cast
                            int bool true false))

  ;; reserved? :: x -> Boolean
  ;; recognizes FJ reserved words
  (define reserved?
    (lambda (x)
      (or (and (memq x RESERVED-WORDS) #t)
          (binary-prim-name? x)
          (unary-prim-name? x))))

  ;; binary-prim-name? unary-prim-name? :: x -> Boolean
  ;; recognize FJ binary and unary primitives
  (define binary-prim-name? (lambda (x) (and (memq x BINARY-PRIMS) #t)))
  (define unary-prim-name? (lambda (x) (and (memq x UNARY-PRIMS) #t)))

  ;; id? :: x -> Boolean
  ;; recognizes legal identifiers
  (define id? (lambda (x) (and (symbol? x) (not (reserved? x)))))

  ;; type-name? :: x -> Boolean
  ;; recognizes legal class names
  (define type-name?
    (lambda (x)
      (or (eq? x 'int)
          (eq? x 'bool)
          (class-name? x))))

  ;; field-name? method-name? :: x -> Boolean
  ;; recognize legal field names, method names
  (define field-name? id?)
  (define method-name? id?)

  ;; defn-name? class-name? :: x -> Boolean
  ;; recognizes legal definition names and class names
  (define defn-name? id?)
  (define class-name?
    (lambda (x)
      (or (eq? x 'Object) (defn-name? x))))

  ;; arg-name? :: x -> Boolean
  ;; recognizes legal method argument names
  (define arg-name? id?)

  (with-public-inspector
   (define-struct program (classes main))
   ;; Program ::= (make-program (Hash-Table Class-Name Class) Expr)

   (define-struct class (name superclass fields methods))
   ;; Class ::= (make-class Type[Class] (Union Class #f)
   ;;                       (Listof Field) (Listof Method))

   (define-struct field (type class name))
   ;; Field ::= (make-field Type Type[Class] Field-Name)
   ;;   class is class in which field is declared.

   (define-struct method (type name arg-names arg-types body))
   ;; Method ::= (make-method Type Method-Name (Listof Arg-Name)
   ;;                         (Listof Type) Expr)

   (define-struct expr ())
   (define-struct (new expr) (type args))
   (define-struct (var-ref expr) (var))
   (define-struct (ref expr) (object field))
   (define-struct (send expr) (object method args))
   (define-struct (cast expr) (type object))
   (define-struct (num-lit expr) (val))
   (define-struct (bool-lit expr) (val))
   (define-struct (unary-prim expr) (rator rand))
   (define-struct (binary-prim expr) (rator rand1 rand2))
   (define-struct (if-expr expr) (test then else))
   ;; Expr     ::= (make-new Type[Class])
   ;;            | (make-var-ref Arg-Name)
   ;;            | (make-ref Src-Expr Field-Name)
   ;;            | (make-send Src-Expr Method-Name (Listof Src-Expr))
   ;;            | (make-cast Type[Class] Src-Expr)
   ;;            | (make-num-lit Integer)
   ;;            | (make-bool-lit Boolean)
   ;;            | (make-unary-prim Unary-Prim Src-Expr)
   ;;            | (make-binary-prim Binary-Prim Src-Expr Src-Expr)
   ;;            | (make-if-expr Src-Expr Src-Expr Src-Expr)


   (define-struct type ())
   (define-struct (ground-type type) (name))
   (define-struct (class-type type) (name))
   (define-struct (arrow-type type) (args result))   
   ;; Type ::= (make-ground-type (Union 'int 'bool))
   ;;        | (make-class-type Class-Name)
   ;;        | (make-arrow-type (List NotArrowType) NotArrowType)
   )

  ;; type=? :: Type Type -> Boolean
  ;; compares two types for (nominal) equality
  (define type=? equal?)


  ;; type->sexpr :: Type -> Sexp
  ;; formats a type for easy manipulation
  (define (type->sexpr type)
    (cond
      [(ground-type? type) (ground-type-name type)]
      [(class-type? type) (class-type-name type)]))

  (provide/contract
   [struct program         ([classes hash-table?]
                            [main expr?])]
   [struct class           ([name class-type?]
                            [superclass (union false/c class?)]
                            [fields (listof field?)]
                            [methods (listof method?)])]

   [struct field           ([type type?]
                            [class class-type?]
                            [name field-name?])]
   [struct method          ([type type?]
                            [name method-name?]
                            [arg-names (listof arg-name?)]
                            [arg-types (listof type?)]
                            [body expr?])]

   [type?                  predicate/c]
   [struct ground-type     ([name (symbols 'int 'bool)])]
   [struct class-type      ([name class-name?])]

   [expr?                  predicate/c]
   [struct new             ([type class-type?])]
   [struct var-ref         ([var (union id? (symbols 'this))])]
   [struct ref             ([object expr?]
                            [field field-name?])]
   [struct send            ([object expr?]
                            [method method-name?]
                            [args (listof expr?)])]
   [struct cast            ([type class-type?]
                            [object expr?])]
   [struct num-lit         ([val integer?])]
   [struct bool-lit        ([val boolean?])]
   [struct unary-prim      ([rator unary-prim-name?]
                            [rand expr?])]
   [struct binary-prim     ([rator binary-prim-name?]
                            [rand1 expr?]
                            [rand2 expr?])]
   [struct if-expr         ([test expr?]
                            [then expr?]
                            [else expr?])]

   [type=?                 (-> type? type? boolean?)]

   [type->sexpr            (-> type? sexp/c)]

   [class-name?            predicate/c]
   [defn-name?             predicate/c]
   [type-name?             predicate/c]
   [field-name?            predicate/c]
   [method-name?           predicate/c]
   [arg-name?              predicate/c]
   [binary-prim-name?      predicate/c]
   [unary-prim-name?       predicate/c]
   [id?                    predicate/c]))
