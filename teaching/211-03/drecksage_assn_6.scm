;; 19.1.5

;; A List-of-Numbers is one of
;; -empty
;; -(cons Number List-of-Numbers)

;; min-max: List-of-Numbers (Number Number -> Boolean) -> Number
;; compares the List-of-Numbers with a comparison function
(define (min-max alon cmp)
  (cond
    [(empty? (rest alon)) (first alon)]
    [else (local ((define first-list (first alon))
                  (define rest-list (min-max (rest alon) cmp)))
                  (cond
                    [(cmp first-list rest-list) first-list]
                    [else rest-list]))]))

;; min1: List-of-Numbers -> Number
;; outputs the largest number in a List-of-Numbers
(define (min1 alon)
  (min-max alon <))
(equal? (min1 (list 20 19 18 17 16 15 14 13 12 11 10 9 8 7 6 5 4 3 2 1)) 1)
;; max1: List-of-Numbers -> Number
;; outputs the smallest number in a List-of-Numbers
(define (max1 alon)
  (min-max alon >))
(equal? (max1 (list 20 19 18 17 16 15 14 13 12 11 10 9 8 7 6 5 4 3 2 1)) 20)

;; 19.1.6

;; A List-of-Numbers is one of
;; -empty
;; -(cons Number List-of-Numbers)
;; sort: List-of-Numbers (Number Number -> Boolean) -> List-of-Numbers
;; to construct a list with all items from a list-of-numbers in descending order
(define (sort alon f)
  (local ((define (sort alon f)
            (cond
              [(empty? alon) empty]
              [else (insert (first alon) (sort (rest alon) f))]))
          (define (insert an alon)
            (cond
              [(empty? alon) (list an)]
              [else (cond
                      [(f an (first alon)) (cons an alon)]
                      [else (cons (first alon) (insert an (rest alon)))])])))
    (sort alon f)))
(equal? (sort (list 2 3 1 5 4) >) (list 5 4 3 2 1))
(equal? (sort (list 2 3 1 5 4) <) (list 1 2 3 4 5))

;; 21.2.1

;; 1
;; zero-three: Number -> List-of-Numbers
;; consumes a number and produces a list of numbers from 0 to one less than the number
(define (zero-three a-number)
  (local ((define (f x)
            (- (+ 1 x) 1)))
    (build-list a-number f)))
(equal? (zero-three 4) (list 0 1 2 3))
;; one-four: Number -> List-of-Numbers
;; consumes a number and produces a list of numbers from 1 to the number
(define (one-four a-number)
  (local ((define (g x)
            (+ x 1)))
    (build-list a-number g)))
(equal? (one-four 4) (list 1 2 3 4))
;; 2
;; tenths: Number -> List-of-Numbers
;; consumes a number and produces a list of numbers getting exponentially smaller by 10
(define (tenths a-number)
  (local ((define (h x)
            (/ 1 (expt 10 (+ x 1)))))
    (build-list a-number h)))
(equal? (tenths 4) (list .1 .01 .001 .0001))
;; 3
;; evens: Number -> List-of-Numbers
;; produces a certain number of even numbers in a list
(define (evens a-number)
  (local ((define (j x)
            (* 2 x)))
    (build-list a-number j)))
(equal? (evens 4) (list 0 2 4 6))
;; 4
;; tabulate: Number (Number -> Number) -> List-of-Numbers
(define (tabulate a-number fnc)
  (local ((define (p x)
            (fnc x)))
    (build-list a-number p)))
(equal? (tabulate 2 sqrt) (list 0 1))
;; 5
;; diagonal: Number -> List-of-Lists
;; to create a list of list of numbers representing a diagonal pattern of 1's
(define (diagonal a-number)
  (build-list a-number (lambda (x)
                         (build-list a-number (lambda (y)
                                                (local ((define (f a b)
                                                          (cond
                                                            [(equal? a b) 1]
                                                            [else 0]))) (f x y)))))))
(equal? (diagonal 3) (list (list 1 0 0) (list 0 1 0) (list 0 0 1)))
(equal? (diagonal 4) (list (list 1 0 0 0) (list 0 1 0 0) (list 0 0 1 0) (list 0 0 0 1)))

;; 21.2.2(2)

;; convertFC: List-of-Numbers -> List-of-Numbers
;; to convert a list of farenheit measurements into a list of celcius measurements
(define (convertFC alof)
     (map (lambda (an-f) (* (- an-f 32) (/ 5 9))) alof))
(equal? (convertFC (list 32)) (list 0))
(equal? (convertFC (list 32 122)) (list 0 50))

;; ------------------------------------------------------------------------------------------
;; Online Problems

;; 2.6.2

(define UFO-WIDTH 20)
(define UFO-HEIGHT 3)
(define UFO-RADIUS 3)
(start 500 500)

;; Posn Posn -> Posn 
;; pointwise addition of posn's
(define (posn+ p q)
  (make-posn (+ (posn-x p) (posn-x q)) (+ (posn-y  p) (posn-y  q))))

;; toggle-ufo : function function UFO -> true
;; to draw or clear the ufo 
(define (toggle-ufo fnc1 fnc2 aufo)
  (and 
   (fnc1 aufo UFO-WIDTH UFO-HEIGHT 'green)
   (fnc2 (posn+ aufo (make-posn (/ UFO-WIDTH 2) 1)) UFO-RADIUS 'green)))
(toggle-ufo draw-solid-rect draw-solid-disk (make-posn 200 200))
(toggle-ufo draw-solid-rect draw-solid-disk (make-posn 100 150))

;; 2.6.6

;; List-of-Shots is one of
;; -empty
;; -(cons Shot List-of-Shots)

;; List-of-shots -> List-of-Shots
;; to take a list of shots and move all of them
(define (move-all-shots shots)
  (map (lambda (a-shot)
         (make-posn (posn-x a-shot) (+ (posn-y a-shot) 1)))
          shots))
(equal? (move-all-shots (list (make-posn 200 150) (make-posn 200 200))) (list (make-posn 200 151) (make-posn 200 201)))

;; 2.6.7

;; draw-shot: Shot -> true
;; to take a shot and draw it, producing true
(define (draw-shot a-shot)
  (draw-solid-rect a-shot 1 5 'red))

;; clear-shot: Shot -> true
(define (clear-shot a-shot)
  (clear-solid-rect a-shot 1 5 'red))

;; toggle-all-shots: List-of-shots -> true
(define (toggle-all-shots shots fnc)
          (cond
            [(empty? shots) true]
            [else (andmap fnc shots)]))
(equal? (toggle-all-shots (list (make-posn 200 140) (make-posn 230 170)) draw-shot) true)
(equal? (toggle-all-shots (list (make-posn 200 140) (make-posn 230 170)) clear-shot) true)
(equal? (toggle-all-shots empty draw-shot) true)

;; 2.6.8

;; List-of-shots: UFO -> Boolean
;; hit-by-shot?: LoS UFO -> Boolean
;; consumes a list of shots and a ufo and returns true if any of the shots hit the ufo, false otherwise
(define (hit-by-shot? alos aufo)
  (ormap (lambda (a-shot)
           (cond
             [(cons? alos) (cond
                             [(equal? a-shot aufo) true]
                             [else (hit-by-shot? (rest alos) aufo)])])) alos))
(equal? (hit-by-shot? (list (make-posn 151 200) (make-posn 200 100)) (make-posn 200 100)) true)
(equal? (hit-by-shot? (list (make-posn 100 200)) (make-posn 150 230)) false)
(equal? (hit-by-shot? empty (make-posn 270 180)) false)
