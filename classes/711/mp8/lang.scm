;;;;;;;;;;;;;;;; grammatical specification ;;;;;;;;;;;;;;;;

(define the-lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier
      (letter (arbno (or letter digit "_" "-" "?")))
      symbol)
    (number (digit (arbno digit)) number)))

(define the-grammar
  '((program (expression) a-program)
    (expression (number) lit-exp)
    (expression ("true") true-exp)
    (expression ("false") false-exp)
    (expression (identifier) var-exp) 
    (expression
      (primitive "(" (separated-list expression ",") ")")
      primapp-exp)
    (expression
      ("if" expression "then" expression "else" expression)
      if-exp)
   (expression
      ("let" (arbno  identifier "=" expression) "in" expression)
      let-exp)
    (expression                         
      ("proc" "(" (separated-list optional-type-exp identifier ",") ")" expression)
      proc-exp)
    (expression
      ("(" expression (arbno expression) ")")
      app-exp)

    (expression
      ("letrec"
        (arbno optional-type-exp identifier
          "(" (separated-list optional-type-exp identifier ",") ")"
          "=" expression) "in" expression) 
      letrec-exp)

    (expression
      ("lettype" identifier "=" type-exp
        (arbno type-exp identifier
          "(" (separated-list type-exp identifier ",") ")"
          "=" expression)
        "in" expression)
      lettype-exp)

    (primitive ("+")     add-prim)
    (primitive ("-")     subtract-prim)
    (primitive ("*")     mult-prim)
    (primitive ("add1")  incr-prim)
    (primitive ("sub1")  decr-prim)
    (primitive ("zero?") zero-test-prim)

    (type-exp ("int") int-type-exp)             
    (type-exp ("bool") bool-type-exp)           
    (type-exp                               
      ("(" (separated-list type-exp "*") "->" type-exp ")")
      proc-type-exp)
    (type-exp (identifier) tid-type-exp)        

    (optional-type-exp                           ; new for 4-4
      ("?")
      no-type-exp)
    (optional-type-exp
      (type-exp)
      a-type-exp)
    (expression
      (effect "(" (separated-list expression ",") ")")
      effect-exp)


    (effect ("pair") pair-effect)
    (effect ("left") left-effect)
    (effect ("right") right-effect)
    (effect ("setleft") setleft-effect)
    (effect ("setright") setright-effect)


    
    ))

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define show-the-datatype
  (lambda () (sllgen:list-define-datatypes the-lexical-spec the-grammar)))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

(define just-scan
  (sllgen:make-string-scanner the-lexical-spec the-grammar))

(define list-find-position
  (lambda (sym los)
    (list-index (lambda (sym1) (eqv? sym1 sym)) los)))

(define list-index
  (lambda (pred ls)
    (cond
      ((null? ls) #f)
      ((pred (car ls)) 0)
      (else (let ((list-index-r (list-index pred (cdr ls))))
              (if (number? list-index-r)
                (+ list-index-r 1)
                #f))))))

(define iota
  (lambda (end)
    (let loop ((next 0))
      (if (>= next end) '()
        (cons next (loop (+ 1 next)))))))

(define difference
  (lambda (set1 set2)
    (cond
      ((null? set1) '())
      ((memq (car set1) set2)
       (difference (cdr set1) set2))
      (else (cons (car set1) (difference (cdr set1) set2))))))

(define union
  (lambda (set1 set2)
    (cond
      ((null? set1) set2)
      ((memq (car set1) set2) (union (cdr set1) set2))
      (else (cons (car set1) (union (cdr set1) set2))))))


(define bigunion
  (lambda (lists)
    (if (null? lists) '()
      (union (car lists) (bigunion (cdr lists))))))