(require (lib "defmacro.ss"))

(define-macro (for v iv wh nx do e)
  (if (eq? do 'do)
      (let ((loop-fun (gensym "iter")))
        `(let ,loop-fun ((,v ,iv))
              (if ,wh (begin ,e (,loop-fun ,nx)))))
      (error "bad keyword")))

(for c 1 (< c 10) (add1 c) do (display c))

(define-macro (or a b)
  (let ((tmp (gensym "tmp")))
    `(let ((,tmp ,a))
       (if ,tmp ,tmp ,b))))

(or true false)
      
