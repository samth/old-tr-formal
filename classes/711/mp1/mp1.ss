(load "~/init.scm")

(define this-assignment 'mp1)

; like string-append for symbols
(define (concat-syms a b)
  (string->symbol (string-append (symbol->string a)  "_" (symbol->string b) )))

; adds a list of tests to the current assignment
(define (add-tests func test-list)
  (for-each
   (lambda (a)
     (add-test! (list this-assignment func) (concat-syms func  (car a)) (cadr a) (caddr a)))
   test-list))

; list -> number
; sums the numbers in the list
(define sum
  (lambda (l)
    (if (null? l) 0
        (+ (car l) (sum (cdr l))))))

;(add-tests 'sum
;           `((one ((1 2 3)) 6)
;             (two (()) 0)))

; eopl 1.15.1
; number slist -> slist
; produces a list with n copies of x
(define duple 
  (lambda (n x)
    (cond
      ((zero? n) '())
      (else (cons x (duple (- n 1) x))))))

(add-tests 'duple
           '((one (3 a) (a a a))
             (two (2 3) (3 3))
             (three (4 (ho ho)) ((ho ho) (ho ho) (ho ho) (ho ho)))
             (four (0 (blah)) ())))  

; eopl 1.15.2
; list -> list
; takes a list of two-element-lists and reverses each
(define (invert lst) 
  (map reverse lst))

(add-tests 'invert
           '((one (((a 1) (a 2) (b 1) (b 2))) ((1 a) (2 a) (1 b) (2 b)))
             (two (()) ())
             ;(three ((a b c)) (a b c))
           ))
  
; eopl 1.15.3
; predicate list -> list
; removes elements of the list that don't match pred
(define (filter-in pred lst)
  (if (null? lst) '()
      (if (pred (car lst)) (cons (car lst) (filter-in pred (cdr lst)))
          (filter-in pred (cdr lst)))))

(add-tests 'filter-in
           `((one (,number? (1 2 a b 5)) (1 2 5))
             (two (,number? ()) ())
             (three (,number? (a b c)) ())
             (four (,symbol? (1 2 a b 5)) (a b))))

; eopl 1.15.4
; predicate list -> bool
; #t if pred returns #t for any elements, #f otherwise
(define (every? pred lst)
  (or (null? lst) (and (pred (car lst)) (every? pred (cdr lst)))))

(add-tests 'every?
           `((one (,number? (a b c 3 e)) #f)
             (two (,number? (1 b c 3 e)) #f)
             (three (,symbol? ()) #t)
             (four (,number? (1 2 3)) #t)))

; eopl 1.15.5
; predicate list -> bool
; #t if pred returns #t for all elements, #f otherwise
(define (exists? pred lst)
  (and (not (null? lst)) (or (pred (car lst)) (exists? pred (cdr lst)))))

(add-tests 'exists?
           `((one (,number? (a b c 3 e)) #t)
             (two (,number? (1 b c 3 e)) #t)
             (three (,symbol? ()) #f)
             (four (,symbol? (1 2 3)) #f)))

; eopl 1.15.7
(define (list-set lst n x)
  (cond
    ((null? lst) '())
    ((zero? n) (cons x (cdr lst)))
    (else (cons (car lst) (list-set (cdr lst) (- n 1) x)))))

(add-tests 'list-set
           `((one (() 3 a) ())
             (two ((a b c d e) 2 (1 2)) (a b (1 2) d e))
             (three ((a b c d) 3 (1 5 10)) (a b c (1 5 10) ))))

; eopl 1.15.8
; list list -> list
; the cartesian product of los1 x los2
(define (product los1 los2)
  (cond 
    ((null? los1) '())
    (else (append
           (map (lambda (x) (list (car los1) x)) los2)
           (product (cdr los1) los2)))))

; eopl 1.16.1
; list -> list
; removes the outer layer of parens from each element in slist
(define (up lst)
  (cond ((null? lst) '())
      ((pair? (car lst)) (append (car lst) (up (cdr lst))))
      (else (cons (car lst) (up (cdr lst))))))

(add-tests 'up
           `((one (()) ())
             (two (((1 2) (3 4))) (1 2 3 4))
             (three ((1 2 (3 (((4)))))) (1 2 3 (((4)))))))

; eopl 1.16.2
; symbol symbol slist -> slist
; replaces s1 with s2 (and vice versa) in slist (even nested)
(define (swapper s1 s2 slist)
  (define (swap-element e)
    (cond ((pair? e) (swapper s1 s2 e))
          ((eqv? e s1) s2)
          ((eqv? e s2) s1)
          (else e)))
  (map swap-element slist))

(add-tests 'swapper
           `((one (a d (a b c d)) (d b c a))
             (two (a d (a d () c d)) (d a () c a))
             (three (x y ((x) y (z (x)))) ((y) x (z (y))))))

; eopl 1.16.3
; symbol slist -> number
; counts the occurences of s in slist
(define count-occurrences
  (lambda (s slist)
    (cond 
      ((null? slist) 0)
      ((pair? slist) (sum (map (lambda (e) (count-occurrences s e)) slist)))
      ((eqv? slist s) 1)
      (else 0))))

(add-tests 'count-occurrences
           `((one (x ((f x) y (((x z) x)))) 3)
             (two (w ((f x) y (((x z) x)))) 0)
             (three (z ()) 0)))

; eopl 1.16.4
; slist -> slist
; removes all inner parens from slist
(define (flatten slist)
  (cond
    ((null? slist) slist)
    ((symbol? (car slist)) (cons (car slist) (flatten (cdr slist))))
    (else (append (flatten (car slist)) (flatten (cdr slist))))))

(add-tests 'flatten
          `((one ((a b c)) (a b c))
            (two (((a) () (b ()) () (c))) (a b c))            ))

; eopl 1.16.5
; list-of-numbers list-of-numbers -> list-of-numbers
; preforms the merge portion of mergesort
(define (merge lon1 lon2)
  (cond
    ((null? lon1) lon2)
    ((null? lon2) lon1)
    ((< (car lon1) (car lon2)) (cons (car lon1) (merge (cdr lon1) lon2)))
    (else (cons (car lon2) (merge lon1 (cdr lon2))))))

(add-tests 'merge
           `((one ((1 2 3 4 5) (6 7 8 9 10)) (1 2 3 4 5 6 7 8 9 10))
             (two ((1 2 3 4 5) ()) (1 2 3 4 5))
             (three ((1 3 5) (2 4 6)) (1 2 3 4 5 6))             ))

; remove-all: symbol slist -> slist
; removes all occurences of syn in slist, even nested ones
(define (remove-all sym slist)
  (cond
   ((null? slist) slist)
   ((symbol? (car slist)) (if (eqv? (car slist) sym) 
			   (remove-all sym (cdr slist))
			   (cons (car slist) (remove-all sym (cdr slist)))))
   (else (cons (remove-all sym (car slist)) (remove-all sym (cdr slist))))))

(add-tests `remove-all 
           `((one (x ()) ())
             (two (x (x x x)) ())
             (three (y (x (y x) z)) (x (x) z))
             (four (x (((x)) (y x y) x)) ((()) (y y) ))             ))
                    
                  

			
; definition of tree datatype
(define-datatype tree tree?
                 (a-tree (root subtree?)))

(define-datatype subtree subtree?
                 (red-node
                  (l subtree?)
                  (r subtree?))
                 (blue-node
                  (children (list-of subtree?)))
                 (leaf-node
                   (datum number?)))

; rbt -> number
; sums the leaf nodes in rbt
(define (leaf-sum rbt)
  (cases tree rbt
      (a-tree (root) (leaf-sum-st root))))

; subtree -> number
; sums the leaf nodes in st
(define (leaf-sum-st st)
  (cases subtree st
    (red-node (r l)
              (+ (leaf-sum-st r) (leaf-sum-st l)))
    (blue-node (children)
               (sum (map leaf-sum-st children)))
    (leaf-node (datum)
               datum)))

(define t1 (a-tree (leaf-node 1)))
(define t2 (a-tree (red-node (red-node (leaf-node 1) (leaf-node 2)) (blue-node (list (leaf-node 3) (leaf-node 4) (leaf-node 5))))))

(add-tests `leaf-sum
           `((one (,t1) 1)
             (two (,t2) 15))) 

; rbt number number -> rbt
; replaces old with new in rbt
(define (subst-in-tree rbt old new)
  (cases tree rbt
      (a-tree (root) (a-tree (subst-in-st root old new)))))

; subtree number number -> subtree
; replaces old with new in rbt
(define (subst-in-st st old new)
  (cases subtree st
    (red-node (r l)
              (red-node (subst-in-st r old new) (subst-in-st l old new)))
    (blue-node (children)
               (blue-node (map (lambda (x) (subst-in-st x old new)) children)))
    (leaf-node (datum)
               (leaf-node (if (= old datum) new datum)))))
                  
(define t3 (a-tree (leaf-node 1)))
(define t4 (a-tree (red-node (red-node (leaf-node 1) (leaf-node 2)) (blue-node (list (leaf-node 3) (leaf-node 5) (leaf-node 2))))))

(add-tests 'subst-in-tree
           `((one (,t3 1 2) ,(a-tree (leaf-node 2)))
             (two (,t4 2 7) ,(a-tree (red-node (red-node (leaf-node 1) (leaf-node 7)) (blue-node (list (leaf-node 3) (leaf-node 5) (leaf-node 7))))))))
              
(test-mp1)