;; Posns and Images

;; A Posn is (make-posn Number Number)

;; A List-of-Posns is one of:
;; - empty
;; - (cons Posn List-of-Posns)



;; Design the function largest-x that finds the posn with the largest x coordinate in a List-of-Posns
;; The function max is provided to you:
;; Produces the larger of two numbers
;; max : Number Number -> Number

(equal? (max 0 1) 1)
(equal? (max 4 -4) 4)
(equal? (max 99 99) 99)

;; Design a function that, given a list of posns, determines if all of them have a positive y coordinate.  
;; Your function should return a boolean.

;; Design a function incr that increases the x coordinate of every posn in a list by 10.  Use a helper function.

;; Design a function world-scene that given a list of posns and a color, draws circles of that color at each posn

;; Test your functions with the following code.  You should see circles move across the screen.  

;; World -> World
(define (world-new list-of-posns)
  (update (world-scene list-of-posns) produce (incr list-of-posns)))

(big-bang 600 200 .1 (cons 1 (cons 10 (cons 50 empty))))
(on-tick-event world-new)





