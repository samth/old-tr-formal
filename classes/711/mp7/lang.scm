;;; threads/lang.scm

(let ((time-stamp "Time-stamp: <2003-10-28 14:59:32 wand>"))
  (eopl:printf "threads/lang.scm ~a~%"
    (substring time-stamp 13 29)))

;;; like implicit-store/lang.scm, but with lists and multiple threads

;;;;;;;;;;;;;;;; syntax ;;;;;;;;;;;;;;;;

(define the-lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier
      (letter (arbno (or letter digit "_" "-" "?")))
      make-symbol)
    (number (digit (arbno digit)) make-number)
    (number ("-" digit (arbno digit)) make-number)
    ))

(define the-grammar
  '((program (expression) a-program)

;; numeric computations, but with many primitives
    (expression (number) const-exp)
    (expression
      (primitive "(" (separated-list expression ",") ")")
      primapp-exp)

    (primitive ("+")     add-prim)
    (primitive ("-")     subtract-prim)
    (primitive ("*")     mult-prim)
    (primitive ("add1")  incr-prim)
    (primitive ("sub1")  decr-prim)
    (primitive ("zero?") zero-test-prim) 

    ;; list primitives
    (primitive ("list")  list-prim)
    (primitive ("null?") null?-prim)
    (primitive ("car")   car-prim)
    (primitive ("cdr")   cdr-prim)

    ;; booleans: producers and consumers
    (expression ("true") true-exp)
    (expression ("false") false-exp)

    (expression
      ("if" expression "then" expression "else" expression)
      if-exp)

    ;; multi-argument procedures
    (expression (identifier) var-exp) 
    (expression
      ("proc" "(" (separated-list identifier ",") ")" expression)
      proc-exp)
    (expression
      ("(" expression (arbno expression) ")")
      app-exp)

    ;; let and letrec
    (expression
      ("let" (arbno identifier "=" expression) "in" expression)
      let-exp)
    (expression                         ; letrec is restricted to procs, sorry
      ("letrec"
        (arbno identifier
          "=" "proc" "(" (separated-list identifier ",") ")" expression)
        "in" expression) 
      letrec-exp)
    
    ;; variable assignment
    (expression
      ("set" identifier "=" expression)
      varassign-exp)

    (expression
      (effect "(" (separated-list expression ",") ")")
      effect-exp)

; leave these out to keep it small.  Easy to add them back.
;     (effect ("pair") pair-effect)
;     (effect ("left") left-effect)
;     (effect ("right") right-effect)
;     (effect ("setleft") setleft-effect)
;     (effect ("setright") setright-effect)

;; new effects:
    (effect ("print") print-effect)
    (effect  ("spawn") spawn-effect)
    
    (effect ("lock") lock-effect)
    (effect ("acquire") acquire-effect)
    (effect ("release") release-effect)
    

    ))

;;;;;;;;;;;;;;;; expressed values ;;;;;;;;;;;;;;;;

(define-datatype expval expval?
  (num-val
    (number number?))
  (bool-val (bool boolean?))
  (closure-val
    (ids  (list-of symbol?))
    (body expression?)
    (env  environment?))
  (pair-val 
    (pairval pairval?))
  ;; add list values in dumbest possible way
  (list-val
    (list (list-of expval?)))
  ;; tid vals, disjoint from nums for now.
  (tid-val
    (tid number?))
  (lock-val 
   (lck location?))
  )


(define-datatype lockt lock?
                 (lock
                  (current-thread (lambda (x) (or (thread? x) (equal? x #f))))
                  (wait-q list?)))
;;;;;;;;;;;;;;;; environments ;;;;;;;;;;;;;;;;

(define-datatype environment environment?
  (empty-env)
  (extend-env
    (ids     (list-of symbol?))
    (vals    (list-of location?))
    (old-env environment?)))

(define apply-env
  (lambda (env sym)
    (cases environment env
      (empty-env ()
        (eopl:error 'apply-env "unbound variable ~s" sym))
      (extend-env (vars vals old-env)
        (cond
          ((list-find-position sym vars)
           => (lambda (n) (list-ref vals n)))
          (else (apply-env old-env sym)))))))

(define extend-env-recursively
  (lambda (proc-names idss proc-bodies old-env)
    (extend-env proc-names
      (map
        (lambda (ids proc-body)
          (closure-val ids 
            (letrec-exp proc-names idss proc-bodies proc-body)
            old-env))
        idss
        proc-bodies)
      old-env)))

;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes the-lexical-spec the-grammar)))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

(define just-scan
  (sllgen:make-string-scanner the-lexical-spec the-grammar))

;;;;;;;;;;;;;;;; misc reductions ;;;;;;;;;;;;;;;;
      
(define reduce-delta-redex
  (lambda (prim vals)
    (cases primitive prim
        (add-prim  ()
          (num-val (+ (expval->num (car vals)) (expval->num (cadr vals)))))
        (subtract-prim ()
          (num-val (- (expval->num (car vals)) (expval->num (cadr vals)))))
        (mult-prim  ()
          (num-val (* (expval->num (car vals)) (expval->num (cadr vals)))))
        (incr-prim  () (num-val (+ (expval->num (car vals)) 1)))
        (decr-prim  () (num-val (- (expval->num (car vals)) 1)))
        (zero-test-prim ()
          (bool-val (zero? (expval->num (car vals)))))
        (list-prim () (list-val vals))
        (null?-prim ()
          (bool-val (null? (expval->list (car vals)))))
        (car-prim ()
          (car (expval->list (car vals))))
        (cdr-prim ()
          (list-val (cdr (expval->list (car vals)))))
        )))

(define expval->num
  (lambda (v)
    (cases expval v
      (num-val (n) n)
      (else (eopl:error 'expval-to-num "Not a num-val: ~s" v)))))

(define expval->list
  (lambda (v)
    (cases expval v
      (list-val (l) l)
      (else (eopl:error 'expval-to-list "Not a list-val: ~s" v)))))

(define reduce-if-redex
  (lambda (val0 e1 e2)
    (cases expval val0
      (bool-val (b) (if b e1 e2))
      (else
        (eopl:error 'reduce-if-redex "non-boolean test: ~s" val0)))))

