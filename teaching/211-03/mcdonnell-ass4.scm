;;Assignment 4

;; 12.2.2)
#|
;;a list of numbers is one of
;; -empty
;; -(cons n alon) where alon is a list of numbers

;;search-sorted : number alon -> boolean
;; to search a sorted list of numbers to determine if n is part of the list
(define (search-sorted n alon)
  (cond
    [(empty? alon) false]
    [else ... (first alon) ... (search-sorted n (rest alon)...)]))    
    


(define list1 (list 1 3 2))
(define list2 (list 3 4 9 30 21 15))

(equal? (search-sorted 9 empty) false)
(equal? (search-sorted 2 list1) true)
(equal? (search-sorted 13 list2) false)

|#

;; 14.1.3)

(define-struct child (f m n d e))

;; a family-tree-node (ftn) is either
;; -empty
;; -(make-child f m na da ec)
;;   where f and m are ftns, na and ec are symbols, and da is a number

;;count-persons : ftn -> number
;; consumes a family tree node and produces the number of people in the corresponding family tree
(define (count-persons aftn)
  (cond
    [(empty? aftn) 0]
    [else (cond
            [(equal? empty (child-f aftn)) 0]
            [(equal? empty (child-m aftn)) 0]
            [else (+ (+ (count-persons (child-f aftn)) 1) (+ (count-persons (child-m aftn)) 1))])]))

;; example family tree

(define Carl (make-child empty empty 'Carl 1926 'green))
(define Bettina (make-child empty empty 'Bettina 1926 'green))

(define Adam (make-child Carl Bettina 'Adam 1950 'yellow))
(define Dave (make-child Carl Bettina 'Dave 1955 'black))
(define Eva (make-child Carl Bettina 'Eva 1965 'blue))
(define Fred (make-child empty empty 'Fred 1966 'pink))

(define Gustav (make-child Fred Eva 'Gustav 1988 'brown))

;; count-persons examples

(equal? (count-persons empty) 0)
(equal? (count-persons Adam) 2)
(equal? (count-persons Gustav) 4)

;; 14.1.4)

;; a family-tree-node (ftn) is either
;; -empty
;; -(make-child f m n d e)
;;   where f and m are ftns, na and ec are symbols, and da is a number


;; average-age : ftn year -> number
;; consumes a ftn and the year and produces the average age of all people in a family tree
(define (average-age aftn year)
  (cond
    [(empty? aftn) 0]
    [else (/ (+ (age (child-d) year) (age (child-f) year) (age (child-m) year)) (count-persons aftn))]))
      
      
;; age : child year -> number
;; consumes a child and a year and produces the age of the child
(define (age child year)
  (- year (child-d child)))

;;examples for age:

(equal? (age Gustav 1998) 10)
(equal? (age Adam 2000) 50)


;; count-persons examples

(equal? (count-persons empty) 0)
(equal? (count-persons Adam) 2)
(equal? (count-persons Gustav) 4)

;; 14.1.5)

;; a loec (list of eye colors) is one of
;; - empty
;; - (cons (child-e) loec))

;;eye-colors: ftn -> loec
;; consumes a ftn and produces a list of all eye colors that occur in the ftn
(define (eye-colors aftn)
  (cond
    [(empty? aftn) empty]
    [else (cons (child-e aftn) (cons (eye-colors (child-f aftn)) (eye-colors (child-m aftn))))])) 

;; examples for eye-colors:

(equal? (eye-colors Carl) (list 'green))
(equal? (eye-colors empty) empty)
(equal? (eye-colors Gustav) (list 'brown 'pink 'blue 'green 'green))


;;14.2.1)

(define-struct node (soc pn lft rgt))

;; a binary-tree (bt) is either
;; -false, or
;; -(make-node soc pn lft rgt)
;; where soc is a number pn is a symbol and lft and rgt are bts

;; contains-bt : number bt -> boolean
;; consumes a number and a bt and determines whether the number occurs in the bt
(define (contains-bt number abt)
  (cond
    [(equal? false abt) false]
    [else (or (equal? (node-soc abt) number) (contains-bt number (node-lft abt)) (contains-bt number (node-rgt abt)))]))

;; example bts:

(define bt1 (make-node 15 'd false (make-node 24 'i false false)))
(define bt2 (make-node 15 'd (make-node 87 'h false false) false))

;; example contains-bt

(equal? (contains-bt 24 bt1) true)
(equal? (contains-bt 30 bt1) false)

;; 14.2.2)

;;search-bt : number abt -> node-pn or false
;; consumes a number and abt and determines whether the node structure whose soc field is n is part of the bt. if it is it produces the nodes pn if not it ;; produces false
(define (search-bt number abt)
  (cond
    [(contains-bt number abt) (node-pn abt)]
    [(search-bt number (node-lft abt)) (node-pn (node-lft abt))]
    [(search-bt number (node-rgt abt)) (node-pn (node-rgt abt))]))

(equal? (search-bt 15 bt1) 'd)
(equal? (search-bt 87 bt2) 'h)


;;14.2.3)

;;inorder : bt -> lossn
;; consumes a bt and produces a list of all the ssn in the tree
(define (inorder abt)
  (cond
    [(equal? false abt) ...]
    [else (node-soc)
          (node-pn)
          (inorder (node-lft))
          (inorder (node-rgt)) ...]))

;;14.3.2)

;;occurs1 : webpage symbol -> number
;; consumes a webpage and a symbol and produces the number of times the 
;; symbol occurs in the web page ignoring nested webpages
(define (occurs1 webpage symbol)
  )

;;occurs2 : webpage symbol -> number
;;consumes a webpage and a symbol and produces the number of times the symbol occurs
;;counting all occurances (including embedded webpages)
(define (occurs2 webpage symbol)
  )

