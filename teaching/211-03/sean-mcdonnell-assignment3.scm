;;Assignment 3

;;9.5.2)

;;a list-of-symbols is either
;; - the empty list, empty, or
;; - (cons s los) where s is a symbol and los is a list of symbols

;; how-many-symbols : los -> number
;; consumes a list of symbols and returns the number of symbols on the list
(define (how-many-symbols alos)
  (cond
    [(empty? alos) 0]
    [else (+ (how-many-symbols (rest alos)) 1)]))

(equal? (how-many-symbols empty) 0)
(equal? (how-many-symbols (cons 'a (cons 'asl (cons 'woeu (cons 'uu empty))))) 4)


;;a list-of-numbers is either
;; - the empty list, empty, or
;; - (cons s lon) where s is a number and lon is a list of numbers

;; how-many-numbers : lon -> number
;; consumes a list of numbers and returns the number of numbers on the list
(define (how-many-numbers alon)
  (cond
    [(empty? alon) 0]
    [else (+ (how-many-numbers (rest alon)) 1)]))

(equal? (how-many-numbers empty) 0)
(equal? (how-many-numbers (cons 6 (cons 3.45 (cons 6.7 (cons 2 empty))))) 4)

;;the two functions differ very slightly.  Where it says symbols in the first function it now says numbers and instead of inputing a los you now input
;;alon


;;9.5.3)

;; a list-of-prices is either
;; - the empty list, empty
;; - or (cons p lon ) where p is a number and lon is a list-of-numbers

;; dollar-store? : list-of-prices number -> boolean
;; consumes a list-of-prices and a threshold number and checks if all the numbers in the list are below the threshold
(define (dollar-store? list-of-prices threshold)
  (cond
    [(empty? list-of-prices) true]
    [else (and (< (first list-of-prices) threshold) (dollar-store? (rest list-of-prices) threshold))]))

(equal? (dollar-store? empty 1) true)
(equal? (dollar-store? (cons 8 (cons 7 (cons 11 empty))) 10) false)
(equal? (dollar-store? (cons 8 (cons 7 (cons 11 empty))) 12) true)

;;9.5.7)

;; a list-of-toy-prices is either
;; - empty
;; - (cons p lotp) where p is a number and alotp is a list-of-toy-prices

;; sum : alotp -> number
;; to compute the sum of the numbers on alotp
(define (sum alotp)
  (cond
    [(empty? alotp) 0]
    [else (+ (first alotp) (sum (rest alotp)))]))

(equal? (sum empty) 0)
(equal? (sum (cons 8 (cons 8 (cons 10 empty)))) 26)

;; how-many-prices : alotp -> number
;; consumes a list of toy prices and returns the number of prices on the list
(define (how-many-prices alotp)
  (cond
    [(empty? alotp) 0]
    [else (+ (how-many-numbers (rest alotp)) 1)]))

(equal? (how-many-prices empty) 0)
(equal? (how-many-prices (cons 6 (cons 3.45 (cons 6.7 (cons 2 empty))))) 4)

;; average-price : lotp -> number
;; to find the average price (the total of all prices divided by the number of toy prices) of a list-of-toy-prices
(define (average-price alotp)
  (cond
    [(empty? alotp) 0]
     [else (/ (sum alotp) (how-many-prices alotp))]))
            
(equal? (average-price empty) 0)
(equal? (average-price (cons 4 (cons 6 (cons 20 empty)))) 10) 

;;2.5.1)

;;prerequisites from assignment 2:

;;a shot is a posn

;;create-shot : posn -> shot
;;consumes a Posn, representing the position of the AUP, and produces the representation of a shot that has just left the AUP
(define (create-shot aupposn)
  (make-posn (posn-x aupposn) (- (posn-y aupposn) 1)))

(equal? (create-shot (make-posn 20 500)) (make-posn 20 499)) 
(equal? (create-shot (make-posn 134 500)) (make-posn 134 499)) 

;;move-shot : shot -> shot
;;consumes a Shot (representation) and produces one that has risen 5 pixels
(define (move-shot shot)
 (make-posn (posn-x shot) (- (posn-y shot) 5)))

(equal? (move-shot (create-shot (make-posn 20 500))) (make-posn 20 494))
(equal? (move-shot (make-posn 59 499)) (make-posn 59 494))

;; end of prereqs.

;; a list-of-shots is either
;; - the empty list, empty
;; - (cons (create-shot aupposn) alos) where (create-shot aupposn)is a shot and alos is a list-of-shots

;;2.5.2)

;;move-all-shots : alos -> alos
;;consumes a list of shots and produces one where each shot has been moved with move-shot
(define (move-all-shots alos)
  (cond
    [(empty? alos) empty]
     [else (cons (move-shot (first alos)) (move-all-shots (rest alos)))]))

(equal? (move-all-shots empty) empty)
(equal? (move-all-shots (cons (make-posn 59 499) (cons (make-posn 60 499) empty))) (cons (make-posn 59 494) (cons (make-posn 60 494) empty)))

;;2.5.4)

;;prereqs.

(define height 500)

;; create-ufo: number -> posn
;; consumes a number n and produces a UFO whose anchor point is at the top of the canvas n pixels to the right of the canvas origin.
(define (create-ufo n)
  (make-posn n 0))
  

(equal? (create-ufo 9) (make-posn 9 0))

;;hit-by-shot : alos ufo -> boolean
;;consumes a list of Shots and a ufo. It produces true if one of the Shots has hit the UFO; it produces false if none of the Shots has hit the UFO.
(define (hit-by-shot alos ufo)
  (cond
    [(empty? alos) false]
    [else (or (equal? (first alos) ufo) (hit-by-shot (rest alos) ufo))]))

(equal? (hit-by-shot empty (create-ufo 80)) false)
(equal? (hit-by-shot (cons (make-posn 90 435) (cons (make-posn 80 0) empty)) (create-ufo 80)) true)



