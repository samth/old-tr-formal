; pad->gui : String Gui-table -> (listof (listof gui-item))
; create a gui from a title and a pad of numbers and symbols
(define (pad->gui title gui-table)
  (local ((define t (make-message title))
          (define msg (make-message "N"))
          (define (x->string x)
            (cond
              [(symbol? x) (symbol->string x)]
              [(number? x) (number->string x)]))
          )
    (cons (list t)
         (cons (list msg) 
               (map (lambda (x) 
                      (map (lambda (y) (make-button (x->string y) (lambda (e) (draw-message msg (x->string y))))) x)) gui-table)))))

(create-window (pad->gui "calc" '((1 2 3  +)
                                  (4 5 6  -)
                                  (7 8 9  *)
                                  (0 = \. /))))



(equal? (pad->gui "foo" '()) (list (list (make-message "foo")) (list (make-message "N"))))