(let ((time-stamp "Time-stamp: <2003-11-11 11:51:03 wand>"))
  (eopl:printf
    "cfa/top.scm ~a~%"
    (substring time-stamp 13 29)))

(load "lang.scm")
(load "labels.scm")
(load "datalog.scm")

;; the theory of 0cfa

;; (phi l1 l2) == l1 \in phi(l2)

(define 0cfa
  (list
    (a-formula '(l1 l2 l3)
      '((phi l1 l2) (flow l2 l3))
      '((phi l1 l3)))
    (a-formula '(l)
      '((const l))
      '((phi l l)))
    (a-formula '(l l1 l2)
      '((prim l l1 l2))
      '((phi l l)))
    
    (a-formula '(l l1 )
      '((prim1 l l1))
      '((phi l l)))
    
    (a-formula '(l l1 l2 lbad l3)
               '((prim l l1 l2)
                 (phi lbad l1)
                 (abs lbad x l3))
               '((phi error l)))
    
     (a-formula '(l l1 l2 lbad l3)
               '((prim l l1 l2)
                 (phi lbad l2)
                 (abs lbad x l3))
               '((phi error l)))
     
    
     (a-formula '(l l1 l2 )
               '((phi error l1)
                 (prim l l1 l2))
               '((phi error l)))
     
     (a-formula '(l l1 l2 )
               '((phi error l2)
                 (prim l l1 l2))
               '((phi error l)))
     
     (a-formula '(l l1 l2 )
                '((phi error l2)
                  (app l l1 l2))
                '((phi error l)))

     (a-formula '(l l1 l2 )
                '((phi error l1)
                  (app l l1 l2))
                '((phi error l)))

    
    (a-formula '(l l1 l2 l3)
               '((if l l1 l2 l3))
               '((flow l2 l)
                 (flow l3 l)))
    (a-formula '(l x)
      '((var l x))
      '((flow x l)))
    
    (a-formula '(l x l1)
               '((abs l x l1))
               '((phi l l)))
 

    (a-formula '(l lbody)
               '((let l  lbody))
               '((flow lbody l)))
    
    (a-formula '(l x)
               '((bind l x))
               '((flow l x)))
    
    (a-formula '(lapp lrator lrand lbad)
               '((app lapp lrator lrand)
                 (phi lbad lrator)
                 (const lbad))
               '((phi error lapp)))
    
    ;one arg func
    (a-formula '(lapp lrator lrand labs bv lbody)
      '((app lapp lrator lrand)
        (phi labs lrator)
        (abs labs bv lbody))
      '((flow lrand bv)
        (flow lbody lapp)))
    
    ))

(define (analyze str)
  (let* ((res (assertions str))
         (soln (begin
                 (reset-solver)
                 (map assert-formula! 0cfa)
                 (map assert! (cdr res))
                 (solve!)
                 (cadr (solver-state)))))
    (list
      (car res)
      (tabulate soln))
    ))

(define (tabulate assertions)
  (list 'phi: (rearrange-phi-table (filter-predicate 'phi assertions))
        'flow: (filter-predicate 'flow assertions)))

(define (filter-predicate sym assertions)
  (cond
    ((null? assertions) '())
    ((eqv? (car (car assertions)) sym)
     (cons (cdr (car assertions))
       (filter-predicate sym (cdr assertions))))
    (else (filter-predicate sym (cdr assertions)))))

;; (list (list a b)) -> table pairs grouped by b's:
;; guaranteed no duplicate pairs in argument
(define (rearrange-phi-table pairs)
  (define (insert-pair pair table)      ; -> table
    ;; insert these sorted!
    (let ((val (car pair)) (key (cadr pair)))
      (let loop ((table table))
        (cond
          ((or
             (null? table)
             (key<? key (caar table)))
           ;; insert the new entry here
           (cons                        
             (list key (list val))
             table))
          ((eqv? (caar table) key)
           ;; add to existing entry.  Should probably insert this
           ;; sorted, too.
           (cons
             (list (caar table) (cons val (cadar table)))
             (cdr table)))
          (else
            (cons (car table) (loop (cdr table))))))))
    (let loop ((pairs pairs) (table '()))
      (if (null? pairs) table
        (loop (cdr pairs) (insert-pair (car pairs) table)))))
           
(define (key<? key1 key2)
  (cond
    ((and (number? key1) (number? key2)) (< key1 key2))
    ((and (symbol? key1) (symbol? key2))
     (string<? (symbol->string key1) (symbol->string key2)))
    ((number? key1) #t)
    (else #f)))

; timing functions

(define (bp-help n)
  (let ((b (string-append " x" (number->string n) " = +(3,4) ")))
    (if (zero? n) b
        (string-append b (bp-help (- n 1))))))

(define (big-prog n)
  (let ((b (bp-help n)))
    (string-append "let " b " in x0")))

(define (big-prog2  n)
  (define (bp n)
    (if (zero? n) "3"
        (string-append "+(3," (bp (- n 1)) ")")))
  (string-append "let x = " (bp n) " in 4"))

(define bp1-times '((1 46 18) (5 276 78) (10 566 156) (30 3071 710) (50 8278 1695) (70 15534 3196) (90 26672 5415) (120 46523 9688) (150 73849 15140) (300 303051 60972)))