(module my-draw mzscheme
  (require (lib "mred.ss" "mred")
           (lib "class.ss")
           (rename (lib "htdp-beginner.ss" "lang") make-posn make-posn)
           (rename (lib "htdp-beginner.ss" "lang") posn-x posn-x)
           (rename (lib "htdp-beginner.ss" "lang") posn-y posn-y)
           )
  (provide start stop 
           clear-solid-line clear-circle clear-solid-disk clear-solid-rect
           draw-solid-line draw-circle draw-solid-disk draw-solid-rect
           draw-solid-string clear-solid-string
           clear-all
           )
  
  (define the-error
    (lambda x
      (error "evaluate (start <num> <num>) first"))) 
  
  (define draw-solid-line the-error)
  (define draw-line-mred the-error)
  (define draw-circle the-error)
  (define draw-solid-disk the-error)
  (define draw-solid-rect the-error)
  
  (define clear-solid-line the-error)
  (define clear-circle the-error)
  (define clear-solid-disk the-error)
  (define clear-solid-rect the-error)
  
  (define clear-solid-string the-error)
  (define draw-solid-string the-error)
  
  (define clear-all the-error)
  
  (define bmp #f)
  (define bdc #f)
  
  (define the-filename "/home/samth/web/server/web-root/htdocs/foo.jpg")
  
  ;; symbol->color : symbol -> color
  ;; to convert symbol to 
  (define (symbol->color s)
    (case s 
      ((white)   (make-object color% 255 255 255))
      ((yellow)  (make-object color% 255 255 0))
      ((red)     (make-object color% 255 0 0))
      ((green)   (make-object color% 0 255 0))
      ((blue)    (make-object color% 0 0 255))
      ((black)   (make-object color% 0 0 0))
      (else (error 'draw.ss "The symbol ~e is not a legal color in draw.ss." s))))
  
  (define (set-color color-sym solid)
    (let* ((brush-style (if solid 'solid 'transparent))
           (color-obj (symbol->color color-sym))
           (pen (make-object pen% color-obj 0 'solid))
           (brush (make-object brush% color-obj brush-style)))
      (send bdc set-pen pen)
      (send bdc set-brush brush)
      ))
  
  
  
  (define (start width height)
    (set! bmp (make-object bitmap% width height #f))
    (set! bdc (new bitmap-dc% (bitmap bmp)))
    (set! draw-line-mred
          (lambda (x1 y1 x2 y2)
            (send bdc draw-line x1 y1 x2 y2)
            (write-the-file)))
    (set! draw-solid-line
          (lambda (p1 p2 c)
            (set-color c #f)
            (send bdc draw-line (posn-x p1) (posn-y p1) (posn-x p2) (posn-y p2))
            (write-the-file)))
    
    (set! clear-solid-line
          (lambda (p1 p2 c)
            (draw-solid-line p1 p2 'white)))
    (set! clear-solid-disk
          (lambda (p1 r c)
            (draw-solid-disk p1 r 'white)))
    (set! clear-circle
          (lambda (p1 r c)
            (draw-circle p1 r 'white)))
    (set! clear-solid-rect
          (lambda (p1 p2 c)
            (draw-solid-rect p1 p2 'white)))
    
    (set! draw-circle
          (lambda (p r c)
            (set-color c #f)
            (send bdc draw-ellipse 
                  (- (posn-x p) r)
                  (- (posn-y p) r)
                  (* 2 r)
                  (* 2 r))
            (write-the-file)))
    
    (set! draw-solid-disk
          (lambda (p r c)
            (set-color c #t)
            (send bdc draw-ellipse 
                  (- (posn-x p) r)
                  (- (posn-y p) r)
                  (* 2 r)
                  (* 2 r))
            (write-the-file)))
    
    (set! draw-solid-rect
          (lambda (p1 p2 c)
            (set-color c #t)
            (send bdc draw-rectangle
                  (posn-x p1)
                  (posn-y p1)
                  (- (posn-x p2) (posn-x p1))
                  (- (posn-y p2) (posn-y p1)))
            (write-the-file)))
    
    (set! draw-solid-string
          (lambda (pos str)
            (let ((x (posn-x pos))
                  (y (posn-y pos)))
              (send bdc set-text-foreground (symbol->color 'black))
              (send bdc draw-text str x y)
              (write-the-file)
              )))
    
    (set! clear-solid-string
          (lambda (pos str)
            (let ((x (posn-x pos))
                  (y (posn-y pos)))
              (send bdc set-text-foreground (symbol->color 'white))
              (send bdc draw-text str x y)
              (write-the-file)
              )))
    
    (set! clear-all
          (lambda ()
            (send bdc clear)
            (write-the-file)
            
            (send bdc clear)
            (set-color 'white #f)
            (write-the-file)
            (display "wrote the file")
            ))
    (clear-all)
    )      
  
  
  (define stop
    (lambda ()
      (send bdc clear)
      (write-the-file)
      
      
      (set! bmp the-error)
      
      (set! clear-all the-error)
      
      (set! draw-solid-line the-error)
      (set! clear-solid-line the-error)
      
      (set! draw-solid-rect the-error)
      (set! clear-solid-rect the-error)
      
      (set! draw-solid-disk the-error)
      (set! clear-solid-disk the-error)
      
      (set! draw-circle the-error)
      (set! clear-circle the-error)

      #t))
      
  
  (define (write-the-file)
    (send bmp save-file the-filename 'jpeg))
  
  )

