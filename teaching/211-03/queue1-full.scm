#| -----------------------------------------------------------------------------
   A Task Queue Manager 
 
   Manage a task queue. Add items to a queue, remove them, show the first
   N via a GUI. Allow people to remove a task.
|#

;; (Listof X)
;; the items in the queue (front-to-back)
(define the-queue empty)

;; String -> Void
(define (add-queue str) 
  (set! the-queue (append the-queue (list str))))

;; Number -> (Listof String)
(define (shw-queue n)
  (show n the-queue))

;; N (Listof X) -> (Listof X)
;; the first n items of l
(define (show n l)
  (cond
    [(and (zero? n) (empty? l)) empty]
    [(and (positive? n) (empty? l)) empty]
    [(and (zero? n) (cons? l)) empty]
    [else (cons (first l) (show (sub1 n) (rest l)))]))

;; -> Boolean
(define (mt?-queue)
  (empty? the-queue))

;; -> Void
(define (rem-queue)
  (set! the-queue (rest the-queue)))

;; Tests (you probably need to skip the tests for the imperative functions)
(equal? (show 0 '(a b c)) '())
(equal? (show 2 '(a b c)) '(a b))
(equal? (show 5 '(a b c)) '(a b c))

#| =============================================================================
   Assume: 
     add-queue ; String -> Void
     shw-queue ; Number -> (Listof String)
     mt?-queue ; -> Boolean 
     rem-queue ; -> Void
|#

#| A Task Queue GUI
 
   _______________________________________________________________________
   | xxxxxxxx Entry (field) xxxxxxxxx [ Enter (button) ] [Done (button)] |
   _______________________________________________________________________
   |       [ Task 1 (message) ]                                          |
   |       [ Task 2 (message) ]                                          |
   |       [ Task 3 (message) ]                                          |
   _______________________________________________________________________   
 

|#

;; -> true
(define (main)
  (create-window 
   (cons (list entry enter done)
         (map list next-tasks))))

;; Event -> true
;; effect: add the task in entry (GUI item) to the queue, refresh display
(define (add-entry e)
  (begin 
    (add-queue (text-contents entry))
    (refresh next-tasks (shw-queue (length next-tasks)))))

;; entry: TextField
(define entry (make-text "Enter new task:")) 

;; enter: Button
(define enter (make-button "Okay" add-entry))

;; Event -> true 
;; effect: remove first task from queue, refresh display
(define (done-task e)
  (begin
    (if (mt?-queue) (void) (rem-queue))
    (refresh next-tasks (shw-queue 3))))

;; done: Button
(define done (make-button "Done" done-task))

;; (Listof MessageField) (Listof String) -> true
;; draw the messages from msgl into the corresponding message fields from (flds),
;; or blank spaces if there are none
;; structural recursion, simultaneous traversal (section 17)
(define (refresh msgl flds)
  (cond
    [(and (empty? msgl) (empty? flds)) true]
    [(and (cons? msgl) (empty? flds)) 
     (and (draw-message (first msgl) " -- none --")
          (refresh (rest msgl) empty))]
    [(and (empty? msgl) (cons? flds)) true]
    [else 
     (and (draw-message (first msgl) (first flds)) 
          (refresh (rest msgl) (rest flds)))]))

;; next-tasks : (Listof Message)
(define next-tasks
  (list 
   (make-message (make-string 80 #\space))
   (make-message (make-string 80 #\space))
   (make-message (make-string 80 #\space))))

;; run, program, run
(main)