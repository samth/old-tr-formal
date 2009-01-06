#lang scheme/base

(require redex/reduction-semantics "opsem.ss")

(provide (all-defined-out))

(define t1 (term ((lambda ([x : top]) x) 3)))
(define t2 (term ((lambda ([x : N]) (add1 x)) 3)))

(define t3 (term ((lambda ([x : top]) (if (number? x) (add1 x) 12)) #t)))

(define t4 (term ((lambda ([x : (U N #t #f)]) (if (number? x) (add1 x) 99)) #t)))
(define t5 (term ((lambda ([x : (U N #t #f)]) (if (number? x) (zero? x) (not x))) #t)))

;; these use the experimental features

;; T-AbsPred
(define t6 (term ((lambda ([x : top]) (if ((lambda ([y : top]) (number? y)) x) (add1 x) 14)) #t)))
;; T-IfAnd
(define t7 (term ((lambda ([x : top]) (if (if (boolean? x) x #f) (not x) #t)) 15)))

;; breaks T-IfAnd
(define t8 (term ((lambda ([x : (U N #t #f)]) 
                    (if 
                     (if (boolean? x) ((lambda ([y : top]) #f) x) #f)
                     3
                     (add1 x)))
                  #f)))

;; T-IfOr
(define t10 (term ((lambda ([x : top]) 
                     (if 
                      (if (boolean? x) #t (number? x))
                      (if (boolean? x) 1 (add1 x))
                      12))
                   9)))
(define t10* (term ((lambda ([x : top]) 
                      (if 
                       (if (boolean? x) #t (number? x))
                       (if (boolean? x) 1 (add1 x))
                       12))
                    #f)))



;; shows red
(define t9 (term (if #f (add1 #f) 77)))

(define t11 (term ((lambda ([v : (U N #t #f)]) (if (boolean? v) 58 (add1 v))) #f)))

;; more examples

(define t12 (term ((if 12 (lambda ([x : top]) 5) (lambda ([x : top]) 40)) 11)))
(define t13 (term ((lambda ([v : top]) ((if v (lambda ([x : top]) 5) (lambda ([x : top]) 41)) 11)) #f)))

(define bad 
  (term
   ((((lambda ([x : (N -> (U N #t #f) : (() ()) : 0)])
        (lambda ([y : (U #t #f)])
          (if y
              x
              (lambda ([z : N]) 0))))
      (lambda ([x : N]) #f))
     #f)
    0)))

(define bad2
  (term
   ((((lambda ([x : (N -> (U N #t #f) : (() ()) : 0)])
        (lambda ([y : (U #t #f)])
          (if y
              x
              (lambda ([z : N]) z))))
      (lambda ([x : N]) #f))
     #t)
    0)))

(define t14
  (term ((lambda ([v : (U #f N)])
           (if v (add1 v) 6))
         12)))
(define t15
  (term ((lambda ([v : (U #f N)])
           (if v (add1 v) ((lambda ([x : (U #t #f)]) 7) v)))
         #f)))
(define t16
  (term ((lambda ([v : (U #f N)])
           (if v (add1 v) ((lambda ([x : (U #t #f)]) 7) v)))
         42)))

;; terms with multiple args
(define t17
  (term ((lambda ([x : N] [y : N]) (if (zero? y) (add1 x) x)) 1 2)))

(define t18
  (term ((lambda ([a : top])
          (if ((lambda ([x : top] [y : top]) (number? y)) 12 a)
              (add1 a)
              123))
         #f)))

;;  terms with cons

(define t-cons-1
  (term (car (cons 77 2))))

(define t-cons-2
  (term (cdr (cons 1 78))))

(define t-cons-3
  (term ((lambda ([a : top])
           (if (cons? a) (car a) 99))
         0)))
(define t-cons-4
  (term ((lambda ([a : top])
           (if (cons? a) (car a) 0))
         (cons #t #f))))

(define t-cons-5
  (term ((lambda ([a : top])
           (if (cons? a) 
               (if (number? (car a))
                   (zero? (car a))
                   #t)
               #f))
         (cons 1 2))))

(define t-cons-6
  (term ((lambda ([a : top])
           (if (cons? a) 
               (if (number? (car a))
                   (zero? (car a))
                   17)
               11))
         (cons #f 10))))

(define t-cons-7
  (term ((lambda ([a : top])
           (if (cons? a) 
               (zero? (car a))
               #f))
         (cons #f 10))))

(define fail-not-wrong
  (term ((lambda ([a : top])
           (zero? a))
         1)))

(define cons-terms (list t-cons-1 t-cons-2 t-cons-3 t-cons-4 t-cons-5 t-cons-6))

(define terms (append (list t1 t2 t3 t4 t5 t6 t7 t9 t10 t10* t11 t12 t13 t14 t15 t16 t17 t18 bad)
                      cons-terms))

(define fail-terms (list t8 t-cons-7 fail-not-wrong))
