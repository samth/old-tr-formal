#| -----------------------------------------------------------------------------
   A Task Queue Manager 
 
   Manage a task queue. Add items to a queue, remove them, show the first
   N via a GUI. Allow people to remove a task.
    
   A QueueInterface is: 
       'add-queue ; String -> Void
       'shw-queue ; Number -> (Listof String)
       'mt?-queue ; -> Boolean 
       'rem-queue ; -> Void
|#

;; -> QueueInterface
;; create a queue via a "service manager" (see Section 39)
(define (make-queue)
  (local (;; --- the existing solution when one queue was enough ----------
          (define the-queue empty)
          (define (add-queue str) 
            (set! the-queue (append the-queue (list str))))
          (define (shw-queue n)
            (local ([define (show n l)
                      (cond
                        [(and (zero? n) (empty? l)) empty]
                        [(and (positive? n) (empty? l)) empty]
                        [(and (zero? n) (cons? l)) empty]
                        [else (cons (first l) (show (sub1 n) (rest l)))])])
              (show n the-queue)))
          (define (mt?-queue)
            (empty? the-queue))
          (define (rem-queue)
            (set! the-queue (rest the-queue)))
          ;; --------------------------------------------------------------
          ;; schematic service manage (a kludge, will go away in HtDP/2e)
          (define (service-manager msg)
            (cond
              [(symbol=? 'add-queue msg) add-queue]
              [(symbol=? 'shw-queue msg) shw-queue]
              [(symbol=? 'rem-queue msg) rem-queue]
              [(symbol=? 'mt?-queue msg) mt?-queue]
              [else (error 'queue "message not understood")])))
  service-manager))

;; QueueInterface
(define low-priority (make-queue))

;; QueueInterface
(define high-priority (make-queue))

#| =============================================================================
   Assume: 
     high-priority, low-priority : QueueInterface
|#


#| A Task Queue GUI
 
   _______________________________________________________________________
   | xxxx Entry xxxxx [ Enter/high ] [Enter/low] [Done/high Done/low ]   |
   _______________________________________________________________________
   |       [ Task 1 high (message) ]       [ Task 1 low      (message) ] |
   |       [ Task 2 high (message) ]       [ Task 2 low      (message) ] |
   |       [ Task 3 high (message) ]       [ Task 3 low      (message) ] |
   _______________________________________________________________________   
 
|#

;; -> true
(define (main)
  (create-window 
   (cons (list entry
               (make-entry-button 
                "Add as high priority task" next-tasks-high high-priority) 
               (make-entry-button 
                "Add as low priority task" next-tasks-low low-priority) 
               (make-done-task-button
                "Done high priority task" next-tasks-high high-priority)
               (make-done-task-button
                "Done low priority task" next-tasks-low low-priority))
         (map list next-tasks-high next-tasks-low))))

;; String Queue -> Button
;; effect: add the task in entry (GUI item) to the queue, refresh display
(define (make-entry-button msg next-tasks q)
  (make-button
   msg 
   (lambda (e)
     (begin 
       ([q 'add-queue] (text-contents entry))
       (refresh next-tasks ([q 'shw-queue] (length next-tasks)))))))

;; entry: TextField
(define entry (make-text "Enter new task:")) 

;; String (Listof Messae) Queue -> Button
;; effect: remove first task from queue, refresh display
(define (make-done-task-button msg next-tasks q)
  (make-button
   msg
   (lambda (e)
     (begin
       (if ([q 'mt?-queue])
           (void)
           ([q 'rem-queue]))
       (refresh next-tasks ([q 'shw-queue] 3))))))

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

;; next-tasks : -> (Listof Message)
(define (make-next-tasks)
  (list 
   (make-message (make-string 80 #\space))
   (make-message (make-string 80 #\space))
   (make-message (make-string 80 #\space))))

;; (Listof Message)
(define next-tasks-high (make-next-tasks))

;; (Listof Message)
(define next-tasks-low (make-next-tasks))

;; run, program, run
(main)