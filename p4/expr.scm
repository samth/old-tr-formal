(define-syntax expr
  (syntax-rules (+ - * /)
    [(expr a + b) (+ a b)]
    [(expr a * b) (* a b)]
    [(expr a - b) (- a b)]
    [(expr a / b) (/ a b)]
    [(expr a) a]
    ))

(expr (expr 3) + (expr 4))
(expr 3 * 4)
