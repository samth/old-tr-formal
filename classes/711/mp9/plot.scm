(require (lib "plot.ss" "plot"))


(define bp-times '((1 46 18) (5 276 78) (10 566 156) (30 3071 710) (50 8278 1695) (70 15534 3196) (90 26672 5415) (120 46523 9688) (150 73849 15140) (300 303051 60972)))
(define x-vals (map car bp-times))
(define results1 (map cadr bp-times))
(define results2 (map caddr bp-times))
 

 
(plot (mix (line (lambda (x) (* 1.2 (expt x 2.2))))
           (points (map vector x-vals results1))
           (line (lambda (x) (* .22 (expt x 2.2))))
           (points (map vector x-vals results2))
           )
      (x-min 0) (y-min 0) (x-max 350) (y-max 350000))