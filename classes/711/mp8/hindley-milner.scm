(define filename "hindley-milner.scm")
(define file-description "type inference with polymorphic let")
(define time-stamp "Time-stamp: <2003-11-03 15:09:50 wand>")
(define reload (lambda () (load filename)))

(load "test-harness.scm")
(load "store2.scm")
(load "pairval2.scm")
(load "lang.scm")

(eopl:printf "~a: ~a ~a~%"
  filename file-description (substring time-stamp 13 29))

;;;;;;;;;;;;;;;; top level interface ;;;;;;;;;;;;;;;;


(define run
  (lambda (string)
    (eval-program (scan&parse string))))

(define all-groups '(lang4-2 lang4-3 lang4-4 poly-let pairs))

(define run-all
  (lambda ()
    (run-experiment run use-execution-outcome
      all-groups all-tests equal-external-reps?)))

(define run-one
  (lambda (test-name)
    (run-test run test-name)))

(define check-all
  (lambda ()
    (run-experiment type-check use-checker-outcome
      all-groups all-tests equal-up-to-gensyms?)))

(define check-one
  (lambda (test-name)
    (run-test type-check test-name)))

(define equal-external-reps?
  (lambda (actual-outcome correct-outcome)
    (equal? actual-outcome (sloppy-to-expval correct-outcome))))

;; equal-up-to-gensyms is defined in test-harness.scm



(load "types.scm")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;; the interpreter ;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;; expressed values ;;;;;;;;;;;;;;;;

(define-datatype expval expval?
  (num-val (datum number?))
  (bool-val (datum boolean?))
  (pair-val 
   (pairval pairval?))
  (closure-val
    (ids (list-of symbol?)) 
    (body expression?)
    (env environment?)))

(define expval->num
  (lambda (v)
    (cases expval v
      (num-val (n) n)
      (else (eopl:error 'expval->num "Not a num-val: ~s" v)))))
      
(define expval->bool
  (lambda (v)
    (cases expval v
      (bool-val (b) b)
      (else (eopl:error 'expval->bool "Not a bool-val: ~s" v)))))

;;;;;;;;;;;;;;;; the interpreter ;;;;;;;;;;;;;;;;

(define eval-program 
  (lambda (pgm)
    (cases program pgm
      (a-program (body)
        (car (eval-expression body (empty-env) (empty-store)))))))

(define eval-expression                 ; exp x env -> expval
  (lambda (exp env store)
    (cases expression exp
      (lit-exp (datum) (list (num-val datum) store))
      (true-exp () (list (bool-val #t) store))
      (false-exp () (list (bool-val #f) store))
      (var-exp (id) (list (apply-env env id) store))
      (primapp-exp (prim rands)
        (let* ((r (eval-expressions rands env store))
               (args (car r))
               (new-store (cadr r)))
          (list (apply-primitive prim args) new-store)))
      (if-exp (test-exp true-exp false-exp) ;\new4
              (let* ((rt (eval-expression test-exp env store))
                     (new-s1 (cadr rt)))
                (if (expval->bool (car rt))
                    (eval-expression true-exp env new-s1)
                    (eval-expression false-exp env new-s1))))

      (proc-exp (texps ids body) (list (closure-val ids body env) store))
      (app-exp (rator rands)            ;\new7
        (let* ((r1 (eval-expression rator env store))
               (ns (cadr r1))
               (proc (car r1))
               ;(dd (eopl:printf "proc1: ~v~n " rator))
               (r2 (eval-expressions rands env ns))
               (ns2 (cadr r2))
               (args (car r2))
               ;(d (eopl:printf "proc: ~v~n args: ~v~n" proc args))
               )
          (cases expval proc
            (closure-val (ids body env) 
              (eval-expression body (extend-env ids args env) ns2))
            (else 
              (eopl:error 'eval-expression
                "Attempt to apply non-procedure ~s" proc)))))
      (let-exp (ids rands body)
        (let* ((r (eval-expressions rands env store))
               ;(d (eopl:pretty-print r))
               (args (car r))
              (s (cdr r)))
          (eval-expression body (extend-env ids args env) s)))
      (letrec-exp (res-texps proc-names texpss idss bodies letrec-body) ;\new3
        (eval-expression letrec-body
          (extend-env-recursively proc-names idss bodies env) store))
      (lettype-exp (type-name texp
                     result-texps proc-names texpss
                     idss bodies lettype-body)
        (eval-expression lettype-body
          (extend-env-recursively proc-names idss bodies env) store))
      (effect-exp (name args) 
                  (let* ((v (eval-expressions args env store))
                        (ns (if (list? (cadr v)) (car (cadr v)) (cadr v)))
                        (vals (car v))
                        (d (eopl:pretty-print v))
                        )
                    (apply-effect name vals env ns)))
      (else (eopl:error 'eval-expression "Unimplemented expression: ~s" exp))

      )))

(define (foldr f init l)
  (cond
    [(null? l) init]
    [else (f (car l) (foldr f init (cdr l)))]))

(define (foldl f init l)
  (foldr f init (reverse l)))

(define (eval-expressions exps env store)
  (let* ((k (eval-expressions2 exps env store  (list '() store)))
        (l (if (list? (cadr k)) (car (cadr k)) (cadr k)))
        )
    
    (list (reverse (car k))  l)))

(define eval-expressions2
  (lambda (rands env store acc)
    (cond 
      [(null? rands) acc]
      [else (let* ((v (eval-expression (car rands) env store))
                  ;(d (eopl:pretty-print v))
                   (new-s (cadr v))
                   (new-val (car v))
                   (old-vals (car acc))
                  )
              (eval-expressions2 (cdr rands) env new-s (list (cons new-val old-vals) new-s)))]))) 

(define apply-primitive
  (lambda (prim args)
    (let ((args (map expval->num args)))
      (cases primitive prim
        (add-prim  () (num-val (+ (car args) (cadr args))))
        (subtract-prim () (num-val (- (car args) (cadr args))))
        (mult-prim  () (num-val (* (car args) (cadr args))))
        (incr-prim  () (num-val (+ (car args) 1)))
        (decr-prim  () (num-val (- (car args) 1)))
        (zero-test-prim () (bool-val (zero? (car args))))
        ))))

(define apply-effect
  (lambda (eff vals env store)
    (cases effect eff

      (pair-effect ()
        (new-pair (car vals) (cadr vals) store
          (lambda (p new-store)
            (list (pair-val p)  new-store))))


      (left-effect ()
        (cases expval (car vals)
          (pair-val (p)
                    (begin 
                      (eopl:pretty-print p)
                      (list
                       (left p store)
                       store)))
          (else (eopl:error "foo"))))

      (setleft-effect ()
        (cases expval (car vals)
          (pair-val (p)
            (list
             (num-val 13)
             (setleft p (cadr vals) store)))
          (else (eopl:error "foobar"))))

      (right-effect ()
        (cases expval (car vals)
          (pair-val (p)
            (list
              (right p store)
              store))
          (else (eopl:error))))

      (setright-effect ()
        (cases expval (car vals)
          (pair-val (p)
                    (list
                     (num-val 13)
                     (setright p (cadr vals) store)))
          (else (eopl:error))))
)))

;;;;;;;;;;;;;;;; environments ;;;;;;;;;;;;;;;;

(define-datatype environment environment?
  (empty-env-record)
  (extended-env-record
    (syms (list-of symbol?))
    (vec vector?)              ; can use this for anything.
    (env environment?))
  )

(define empty-env
  (lambda ()
    (empty-env-record)))

(define extend-env
  (lambda (syms vals env)
    (extended-env-record syms (list->vector vals) env)))

;; use circular-link implementation.  Load 3-6-letrec{1,2}.scm on top
;; of this to override.

(define extend-env-recursively
  (lambda (proc-names idss bodies old-env)
    (let ((len (length proc-names)))
      (let ((vec (make-vector len)))
        (let ((env (extended-env-record
                     proc-names vec old-env)))
          (for-each
            (lambda (pos ids body)
              (vector-set! vec pos (closure-val ids body env)))
            (iota len) idss bodies)
          env)))))

(define apply-env
  (lambda (env sym)
    (cases environment env
      (empty-env-record ()
        (eopl:error 'apply-env "No binding for ~s" sym))
      (extended-env-record (syms vals env)
        (let ((position (env-find-position sym syms)))
          (if (number? position)
              (vector-ref vals position)
              (apply-env env sym)))))))

(define env-find-position 
  (lambda (sym los)
    (list-find-position sym los)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; additional test items
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; tests for poly-let

(add-typed-test! 'poly-let 'code-pairs-1 "
let pair2 = proc(? x, ?y) proc (?p) (p x y)
    fst  = proc (?z) (z  proc (? x, ? y) x)
    snd  = proc (?z) (z  proc (? x, ? y) y)
in let d1 = (pair2 true false)
       d2 = (pair2 0 1)
   in (snd d2)" 'int 1)
    

(add-typed-test! 'poly-let 'code-pairs-2 "
let pair2 = proc(? x, ?y) proc (?p) (p x y)
    fst  = proc (?z) (z  proc (? x, ? y) x)
    snd  = proc (?z) (z  proc (? x, ? y) y)
in let d1 = (pair2 fst snd)
       d2 = (pair2 0 1)
   in ((snd d1) d2)" 'int 1)


(add-typed-test! 'poly-let 'heterogeneous-pairs-2 "
let pair2 = proc(? x, ?y) proc (?p) (p x y)
    fst  = proc (?z) (z  proc (? x, ? y) x)
    snd  = proc (?z) (z  proc (? x, ? y) y)
in let d1 = (pair2 0 snd)
       d2 = (pair2 true 1)
   in ((snd d1) d2)" 'int 1)

(add-typed-test! 'poly-let 'ho-lists-3 "
let nil = proc(?a, ?f) a
    cons = proc(?x, ?y) proc(?a, ?f) (f x (y a f))
    reduce = proc (?l, ?z, ?s) (l z s)
    pair2 = proc(? x, ?y) proc (?p) (p x y)
    fst  = proc (?z) (z  proc (? x, ? y) x)
    snd  = proc (?z) (z  proc (? x, ? y) y)
    or   = proc (?b1, ?b2) if b1 then b1 else b2
in let p = (pair2 
            (reduce (cons 11 (cons 12 nil)) 0  proc(?x,?y)+(x,y))
            (reduce (cons true (cons false nil)) false or))
in (fst p)
"
'int  23)

(add-typed-test! 'poly-let 'dont-generalize-non-generic-vble-1 "
let pair = proc(?x,?y) proc(?p) (p x y)
in proc (? g) (pair (g 11) (g true))
"
'error 'dontrun)

(add-typed-test! 'poly-let 'generalize-generic-vble-2 "
let pair2 = proc(?x,?y) proc(?p) (p x y)
    fst = proc(?p) (p proc(?x,?y)x)
    g = proc(?x) x
in (fst (pair2 (g 11) (g true)))
"
'int 11)

;;; this should fail because it uses 'zorch' at different types, 
(add-typed-test! 'poly-let 'generic-vbles-1 "
proc (? zorch) % 
 let nil = proc(?z, ?s) z
     cons = proc(?x, ?y) proc(?z, ?s) (s (zorch x) (y z s))
     car = proc(?l,?e)(l e proc(?a,?v)a)
     pair2 = proc(? x, ?y) proc (?p) (p x y)
     fst = proc(?p) (p proc(?x,?y)x)
 in (car (fst (pair2 (cons 12 nil) (cons false nil))) 13)
" 'error 'dontrun)

(add-typed-test! 'pairs 'pair1
               "let g = let count = pair(0,0) in proc() 
                        let d = setleft(count,add1(left(count)))
                        in left(count)
in +((g), (g))" 'int 3   )

(add-typed-test! 'pairs 'complicated
"let f = proc(?x,?g) (g left(x)) 
      % f: (t1,t2,t3)(pair(t1,t2) * (t1->t3) -> t3)
    h = proc(?x) pair(x,33)    
      % h: (t1)(t1 -> pair(t1,int))
    id = proc(?z)z             
      % id: (t1)(t1 -> t1)
in if zero?((f (h 0) id)) 
   then (f (h true) id) 
   else false" 'bool #t)

(add-typed-test! 'pairs 'val-restrict
               "let p = pair(0,proc(?x) x) 
                        in if (right(p) true) 
                              then (right(p) 2) 
                              else (right(p) 3)" 'error 'dontrun   )
