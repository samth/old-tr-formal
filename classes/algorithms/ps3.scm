(module ps3 (planet "qstr-lang.ss" ("jacob" "quasistring.plt" 1 0))
  (require "../../scheme-tex.scm")
  
  (require  (lib "list.ss") (lib "match.ss"))
  
  (define (math . args) (ensuremath (apply group args)))
  
  (define (function nm)
    (lambda args
      (let ((sep ", "))
        "$(math nm)($(apply string-append (interleave sep (map math args))))")))
  
  (define-values (i j k l m n x y z a b A B C S)
    (apply values (map math '(i j k l m n x y z a b A B C S))))
  
  (define nlogn (math "n \\log n"))

  (predefs0 Omega omega Theta)
  (predefs lg)
  
  (define-values (Om om o O Th xi xk) 
    (values
     (function Omega)
     (function omega)
     (function "o")
     (function "O")
     (function Theta)
     (sub x i)
     (sub x k)))
  
  (define (binop op) (lambda (a b) (math "$a $op $b")))

  (define-values (plus minus eq le)
    (apply values
           (map binop (list '+ "-" '= '<)))) 
  
  (define (index arr i) (math "$arr[$i]"))
  
  
  (define ps3
    (tex 
     "ps3.tex"
     (documentclass 'article 12)
     (title "Problem Set 3")
     (author "Sam Tobin-Hochstadt")
     (document
      (section 
       "Problem 1"
       (lines "This problem exhibits optimal substructre as follows.  Imagine an optimal solution for a board $B with $k columns.  Then this solution is also optimal for the same problem on the first $(minus k 1) columns, with the square next to the $(values k)th pebble excluded.  To see this, imagine that there existed a better solution for this problem.  Then it could be used, along with the position of the last pebble, to make a new solution.  The last pebble would have the same score, and the new portion would have a higher score, contradicting the assumption of an optimal solution."
           (group "We define $(index C i j) to be the optimal solution for the first i columns of board A, with the jth square in column $i excluded.  Note that $j ranges from 1 to 3.  Then" $((index C i j) . eq . (MAX ))
           )
       ))))
  )