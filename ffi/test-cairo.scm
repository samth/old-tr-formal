(load "cairo.scm")

(define-syntax test-cairo
  (syntax-rules ()
    [(test-cairo file w h code ...)
     (let ([fn (fopen file "w")]
           )
       (begin
         (current-cairo-state (create))
         (set-target-png fn 'format-argb32 w h)
         (set-rgb-color 0 0 0)
         code ...
         (destroy)
         (fclose fn)))]))


(test-cairo "test2.png" 40 40
            (move-to 0.0 0.0)
            (line-to 40.0 40.0)
            (stroke))

(test-cairo "arc.png" 100 100
            (let*
                ([xc (* 100 0.5)]
                 [yc (* 100 0.5)]
                 [radius (* 100 0.4)]
                 [pi 3.14159265358979]
                 [pi/180 (/ pi 180)]
                 [angle1  (* 45.0 pi/180)]
                 [angle2  (* 180.0 pi/180)])
              
              (begin
                (arc xc yc radius angle1 angle2)
                (stroke)

                ;; draw helping lines 
                (set-rgb-color  1.0 0.2 0.2)
                (set-alpha 0.6)
                (arc xc yc 5.0 0.0 (* 2 pi))
                (fill)
                (set-line-width 3.0)
                (arc xc yc radius angle1 angle1)
                (line-to xc yc)
                (arc xc yc radius angle2 angle2)
                (line-to xc yc)
                (stroke))))

(test-cairo "fill.png" 100 100
            (move-to 50 10)
            (line-to 90 90)
            (rel-line-to -40 0)
            (curve-to 20 90 20 50 50 50)
            (close-path)

            (move-to 25 10)
            (rel-line-to 20 20)
            (rel-line-to -20 20)
            (rel-line-to -20 -20)
            (close-path)

            (save/restore
             (set-rgb-color 0 0 1)
             (fill))
            (stroke))


