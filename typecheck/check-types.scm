(require (lib "match.ss"))

(define-struct contract () (make-inspector))

(define-struct (simple-ct contract) (name)(make-inspector))

(define-struct (arr-ct contract)  (inputs output)(make-inspector))

(define-syntax ct
  (syntax-id-rules (->)
    [(_ a) (make-simple-ct a)]
    [(_ a ... -> b)
     (make-arr-ct (list a ...) b)]
    [_ (lambda (x) (ct x))]))

(define-syntax cwv
  (syntax-rules ()
    [(_ vals fun) (call-with-values (lambda () vals) fun)]))

(define num (ct 'number))
(define sym (ct 'symbol))
(define str (ct 'string))
(define bool (ct 'boolean))

(define initial-env
  `(
    (+ ,(ct num num -> num))
    (- ,(ct num num -> num))
    (* ,(ct num num -> num))
    (/ ,(ct num num -> num))
    (< ,(ct num num -> bool))
    (= ,(ct num num -> bool))
    (> ,(ct num num -> bool))
  ))



(define (add-binding nm contract env)
  (cons (list nm contract) env))

(define (add-bindings nms cts env)
  (if (null? nms) env (add-bindings (cdr nms) (cdr cts) (add-binding (car nms) (car cts) env))))

(define (parse-cont c)
  (if (symbol? c) (ct c)
      (cwv 
       (let loop ((c c) (acc '()))
         (if (eq? '-> (car c)) (values (map parse-cont (reverse acc)) (parse-cont (cadr c))) (loop (cdr c) (cons (car c) acc))))
       make-arr-ct)))

(define (check-exp-help exp env)
  bool)

(define (check-exp exp env goal)
  (let* ((t (check-exp-help exp env)))
    (if (equal? t goal) (void) (printf "expected: ~a to produce a ~a but instead it produced a ~a." exp goal t)))
  )
  
(define (check exp env)
  (match exp
    [`(define (,nm ,args ...) ,cont ,body) 
      (let*
          (
           (function-ct (parse-cont cont))
           (inputs (arr-ct-inputs function-ct))
           (output (arr-ct-output function-ct))
           (out-env (add-binding nm function-ct env))
           (inner-env (add-bindings args (map ct inputs) out-env))
           )
        (begin
          (check-exp body inner-env output)
          out-env))
        ]))


  