;;Exercise 12.2.2

;; search: number list-of-numbers ---> boolean
	(define (search n alon)
	 (cond
	 [(empty? alon) false]
	 [else (or (= (first alon) n ) (search n (rest alon)))]))

;********************************

;Exercise 14.1.3

;; Data Defintion
(define-struct child(father mother name date))

;A family-tree-node (short: ftn) is either
;  1. empty
;  2. (make-child f m na da ec)


;; Contract, Purpose & Header
;; count-persons: ftn ---> number
;; to count the number of persons in a ftn


;; Examples
;; Oldest Generation
;	(define Andrew (make-child empty empty ' Andrew 1943))
;	(define Julia (make-child empty empty 'Julia 1960))

;; Middle Generation
;	(define Lacrecia (make-child Andrew Julia 'Lacrecia 1985))
;	(define Faith ( make-child Andrew Julia 'Faith 1987))
;	(define Marcus (make-child Andrew Julia ' Marcus 1988))

;; Youngest Generation
;	(define Isaiah (make-child empty Lacrecia 'Isaiah 1998))


;;Template
;; count-persons ---> Number
;; to count the number of people in a ftn

;; fun-for-a-ftn
	
;(define (fun-for-a-ftn)
;	(cond
;	[(empty? a-ftn)...]
;	[else; (child? a-ftn)
;	...]))

;; fun-for-a-ftn

;	(define fun-for-a-ftn)
;	(cond
;
;	[(empty? a-ftn ...]
;	[( else
;	...(f a-ftn (child-father a-ftn))...
;	...(f a-ftn (child-mother a-ftn))...
;	...(child-name a-ftn)... 	                   
;	...(child-date a-ftn)...[))

;; Definition
;I got stuck here........


;*****************************

;Exercise 14.1.4


;; Data Defintion
(define-struct child(father mother name age date))

;A family-tree-node (short: ftn) is either
;  1. empty
;  2. (make-child f m na da ec)


;; Contract, Purpose & Header
;; average-age: ftn ---> number
;; produces the average age of all people it the family tree


;; Examples
;; Oldest Generation
;	(define Andrew (make-child empty empty ' Andrew 60 1943))
;	(define Julia (make-child empty empty 'Julia 43 1960))

;; Middle Generation
;	(define Lacrecia (make-child Andrew Julia 'Lacrecia 18 1985))
;	(define Faith ( make-child Andrew Julia 'Faith 16 1987))
;	(define Marcus (make-child Andrew Julia ' Marcus 15 1988))

;; Youngest Generation
;	(define Isaiah (make-child empty Lacrecia 'Isaiah 5 1998))


;;Template
;; average-age ---> Number
;; produce the average age of all people in the family tree

;; fun-for-average-age-a-ftn
	
;(define (fun-for-average-age-a-ftn)
;	(cond
;	[(empty? a-ftn)...]
;	[else; (child? a-ftn)
;	...]))

;; fun-for-average-age-a-ftn

;	(define;; fun-for-average-age-a-ftn)
;	(cond
;
;	[(empty? a-ftn ...]
;	[( else
;	...(f a-ftn (child-father a-ftn))...
;	...(f a-ftn (child-mother a-ftn))...
;	...(child-name a-ftn)...
;	...(child-age a-ftn)... 	                   
;	...(child-date a-ftn)...[))

;; Definition
;I got stuck here again....


;*****************************************

;Exercise 14.2.1

 
;Exercise 14.2.3 
;(define-struct node (ssn)

;A binary-tree (short: BT) is either:
; 1. false; or
; 2. (make node soc)

;Function: Binary Tree

;(append (list 15 24 29) (list 33 63 87) (list 89 95 99))

;Evaluates to 

;(list 15 24 29 33 63 87 89 95 99)

;For a Binary Search Tree:

;(append (list 10 15 24 29 63) (list 77 89 95 99))

;Evaluates to

;(list 10 15 24 29 63 77 89 95 99)

;**Inorder produces the numbers from right to left in a binary search tree. The numbers on the left are larger and get smaller as it goes to the right.**


;Exercise 14.3.2

;For occurs1

;A Web-page (short: WP) is either

 ;1. empty;
 ;2. (cons s wp) 
  ;    where s is a symbol and wp is a Web page; or
 ;3. (cons ewp wp)
      where both ewp and wp are Web pages.

;;size: occurs1 ---> number
;; to count the number of symbols that occur in a-wp
	(define (size a-wp)
	(cond
	[(empty? a-wp) 0]
	[(symbol? (first a-wp)) (+1(size(rest a-wp)))]
	[else(+(size(first a-wp)) (size(rest a-wp)))]))


;For occurs2
;
;A Web-page (short: WP) is either
;
; 1. empty;
; 2. (cons s wp) 
;      where s is a symbol and wp is a Web page; or
; 3. (cons ewp wp)
;      where both ewp and wp are Web pages.

;;size: occurs2 ---> number
;; to count the number of symbols that occur in a-ewp 
	(define (size2 a-ewp)
	(cond
	[(empty? a-ewp) 0]
	[(symbol? (first a-ewp)) (+1(size2(rest a-ewp)))]
	[else(+(size2(first a-ewp)) (size2(rest a-ewp)))]))

