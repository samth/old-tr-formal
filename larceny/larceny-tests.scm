(define map1 '(map add1 (map sub1 (list 1 2 3))))
(define recur1 '(letrec ((f (lambda (x) (if (<= x 0) 1 (+ x (f (- x 1))))))) (f 50)))