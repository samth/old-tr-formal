(load "test-harness.scm")

(define-datatype M-tree M-tree?
  (one)
  (M-node
    (left M-tree?)
    (right M-tree?)))

(define zero
   (M-node (one) (one)))

; M-tree -> number
; returns the number represented by the M-tree
(define (mt->num mt)
  (cases M-tree mt
    (one () 1)
    (M-node (l r)
            (- (mt->num l)
               (mt->num r)))))

; M-tree -> boolean
; returns true if mtree represents 0, false otherwise
(define (is-zero? mtree)
  (= 0 (mt->num mtree)))

; M-tree -> M-tree
; returns the predecessor of mt
(define (pred mt)
  (M-node mt (one)))

(define minus-one
  (pred zero))

; M-tree -> M-tree
; given mt representing n, returns the M-tree representing -n
(define (negate mt)
  (cases M-tree mt
    (one () (M-node zero (one)))
    (M-node (l r)
            (M-node r l))))
  
; M-tree M-tree -> M-tree
; given two M-trees, returns the M-tree representation of their sum
(define (add mt1 mt2)
  (M-node mt1 (negate mt2)))

; M-tree -> M-tree
; returns the successor of mtree
(define (succ mtree)
  (M-node mtree minus-one))

; the lexer spec for our arithmetic language
(define arith-lex
  '((whitespace (whitespace) skip)
    (number (digit (arbno digit)) number)
    ))

;;Expr ::= Term {Additive-Op Term}*
;;Term ::= Factor {Multiplicative-Op Factor}*
;;Factor ::= number | ( Expr ) | -Factor
;;Additive-Op ::= + | -
;;Multiplicative-Op ::= * | /

; the grammar for our language
(define arith-gram
  '((expr
     (term (arbno additive-op term)) sum)
    (term
     (factor (arbno mul-op factor)) product)
    (factor (number) const-factor)
    (factor ("(" expr ")") paren-exp)
    (factor ("-" factor) unary-minus)
    (additive-op ("+") plus-op)
    (additive-op ("-") minus-op)
    (mul-op ("*") times-op)
    (mul-op ("/") divide-op)))

; the sllgen boilerplate
(sllgen:make-define- datatypes arith-lex arith-gram)

(define scan&parse (sllgen:make-string-parser arith-lex arith-gram))

; run : string -> number
; parses and evaluates a string
(define (run str)
  ; run-expr -> expression -> number
  ; evaluates an expression
  (define (run-expr e)
    (cases expr e
        (sum (initial ops terms)
               (do-ops (run-term initial) ops (map run-term terms))))) 
  ; run-term : term-> number
  ; evaluates a single term
  (define (run-term trm)
    (cases term trm
        (product (initial ops factors)
                 (do-ops (run-factor initial) ops (map run-factor factors)))))
  ; run-factor : factor -> number
  ; evaluates a single factor
  (define (run-factor fac)
    (cases factor fac
      (const-factor (n)
           n)
      (paren-exp (p) (run-expr p))
      (unary-minus (f) (* -1 (run-factor f))))) 
  ; do-ops : number (list-of ops) (list-of number) -> number
  ; applies the operations to the numbers, in left-to-right order
  (define (do-ops initial-value ops-list num-list)
    ; do-op : number op number ->  number
    ; does the operation number op number
    (define (do-op init op num)
      (if (additive-op? op) 
          (cases additive-op op
            (plus-op () (+ init num))
            (minus-op () (- init num)))
          (cases mul-op op
            (times-op () (* init num))
            (divide-op () (/ init num)))))
    (if (null? ops-list) initial-value 
        (do-ops (do-op initial-value (car ops-list) (car num-list)) 
                (cdr ops-list) (cdr num-list))))
      
  (let ((exp (scan&parse str)))
    (run-expr exp))
    )
      

; tests for M-trees
(define mtree-tests
  `((zero-1 ,is-zero? ,zero #t)
    (zero-2 ,is-zero? ,(one) #f)
    (zero-3 ,is-zero? ,minus-one #f)
    (pred ,is-zero? ,(pred (one)) #t)
    (pred-succ ,is-zero? ,(pred (succ (one))) #f)
    (add ,mt->num ,(add (one) zero) 1)
    (negate ,mt->num ,(negate (one)) -1)
    ))


(define test2
  (lambda (test-cases)
    (run-tests2 test-cases))) 

(test2 mtree-tests)
   
(load "mp2-test-harness-ind.scm")
(test-all)