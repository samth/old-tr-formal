;; Please grade the following four problems. Take off the number of points 
;; indicated per item. When something is worth N points, it's an up-or-down
;; grading system. Either you get all N points or you lose them all. No partial
;; credit for an item. Of course, there is partial credit for a problem. 

;; total points: 28
;; problem points: 24
;; it executes in drscheme points: 2
;; it runs some test cases as it executes: 2 

;; -----------------------------------------------------------------------------
;; 2.2.5 
;; 2 points total
;; 1 point for correct function transliteration, 1 for examples 
;; 2.

;; Number -> Number 
(define (f n)
  (+ (* 1/2 n n) 20))
(f 2) "should be" 22
(f 9) "should be" 60.5 

;; -----------------------------------------------------------------------------
;; 4.4.1 
;; 5 points total
;; 1 point each for contract, purpose, examples -- 2 points for 3-pronged cond
;; if they get the function wrong otherwise, mark but don't take off points

;; interest : number -> number
;; calculates the amount of interest for d dollars.
(define (interest d)
  (cond
    [(<= d 1000) (* d 4/100)]
    [(<= d 5000) (* d 45/1000)]
    [(> d 5000) (* d 5/100)]))

;; EXAMPLES TURNED INTO TESTS
(interest 500) "should be" 20
(interest 2000) "should be" 90
(interest 10000) "should be" 500 

;; -----------------------------------------------------------------------------
;; 5.1.2
;; 5 points total
;; 1 point each for contract, purpose, examples -- 2 points for 3-pronged cond
;; if they get the function wrong otherwise, mark but don't take off points

;; check-guess : number number -> symbol
;; to determine whether guess is larger, smaller, or equal to target
(define (check-guess guess target)
  (cond
    ((= guess target) 'Perfect)
    ((< guess target) 'TooSmall)
    ((> guess target) 'TooLarge)))

;; EXAMPLES TURNED INTO TESTS:
(check-guess 1 1) "should be" 'Perfect
(check-guess 1 2) "should be" 'TooSmall
(check-guess 1 0) "should be" 'TooLarge

;; after setting teachpack to guess.ss
;(repl check-guess) 

;; -----------------------------------------------------------------------------
;; 5.1.5

;; 5 points total
;; 1 point each for contract, purpose, examples -- 2 points for 4-pronged cond
;; if they get the function wrong otherwise, mark but don't take off points

;; check-color : symbol symbol symbol symbol -> symbol 
;; to determine how well  the target-colors match with the guess-colors
(define (check-color target-1 target-2 guess-1 guess-2)
  (cond
    ((and (symbol=? guess-1 target-1) (symbol=? guess-2 target-2))
     'perfect!)
    ((or  (symbol=? guess-1 target-1) (symbol=? guess-2 target-2)) 
     'One_Color_At_Correct_Position)
    ((or  (symbol=? guess-1 target-2) (symbol=? guess-2 target-1))
     'The_Colors_Occur)
    (else
     'Nothing_Correct)))

;; Examples turned into Tests:
;; at least one example per case: 
(check-color 'red 'green 'red 'green)  "should be" 'perfect!
(check-color 'red 'green 'red 'purple) "should be" 'One_Color_At_Correct_Position
(check-color 'red 'green 'purple 'red) "should be" 'The_Colors_Occur
(check-color 'green 'red 'red 'purple) "should be" 'The_Colors_Occur
(check-color 'green 'blue 'red 'purple) "should be" 'Nothing_Correct

;; uncomment the following line
;; and use the master.ss teachpack
;; to play the game!
;(master check-color) 