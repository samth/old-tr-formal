(define-syntax for 
  (syntax-rules (do)
    [(for v iv wh nx do e)
     (let loop ((v iv))
       (if wh
           (begin e
                  (loop nx))))]))

(for c 1 (< c 10) (add1 c) do (display c))

(define-syntax or
  (syntax-rules ()
    [(or a b)
     (let ((tmp a)) 
       (if tmp tmp b))]))

(or true false)