(module grades mzscheme
  (require (rename   (lib "1.ss" "srfi") take take))
  (require (rename   (lib "1.ss" "srfi") drop drop))
  (require (prefix s: "lab-grades"))
  (require "exam-grades")
  (require "grades-other.scm")
  (require (lib "list.ss") (lib "etc.ss"))
  
  
  (define string-prefix? 
    (lambda (s1 s2) 
      (if (< (string-length s2) (string-length s1))
          #f
          (let ((s (substring s2 0 (string-length s1))))
            (string=? s1 s)))))
  
  (define (find f l)
    (car (memf f l)))
  
  (define (get-hw g)
    (if (= 1 (length g))
        (car g)
        (cadr g)))
  
  (define (get-exam1-grade name gr)
    ;(display name)
    (let ((rec (find
                (lambda (x) (string-prefix? name (cadr x)))
                gr)))
      (list-ref rec 3)))
  
  (define (get-exam2-grade name gr)
;    '(0 0 0 0 0 0))
    (let ((rec (find
                (lambda (x) (string-prefix? name (cadr x)))
                gr)))
      (list-ref rec 4)))
  
  (define (get-exam1 s)
    (list-ref s 4))
  
  (define (get-exam2 s)
    (list-ref s 5))
  
  (define (get-exam1-score s)
    (begin
      ;(display (get-name s))
      (apply +  0 (reverse (get-exam1 s)))))
  
  
  (define (get-exam2-score s)
    (begin
      ;(display (get-name s))
      (apply +  0 (reverse (get-exam2 s)))))
  
  (define (get-hw/q-grades s)
    (memf (lambda (x) (and (list? x) (< (length x) 3))) s))
  
  (define (get-hw-grades s)
    (map get-hw s))
  
  
  (define (get-id-num name gr)
    (let ((rec (find
                (lambda (x) (string-prefix? name (cadr x)))
                gr)))
      (car rec)))
  
  (define (get-instr name gr)
    (let ((rec (find
                (lambda (x) (string-prefix? name (cadr x)))
                gr)))
      (list-ref rec 2)))

  (define  select-students-week-n 
    (opt-lambda (pred n [l  all-grades])
      (let ((s (filter (lambda (x) (pred x n)) l)))
        (map get-info s))))

  (define (correct-form ta)
    (lambda (s) 
      (let* 
          ((name (car s))
           ;(d(display name))
           (ex-grade1 (get-exam1-grade name exam-grades))
           (ex-grade2 (get-exam2-grade name exam-grades))

           (hw-grades (get-hw/q-grades s))
           (instructor (get-instr name exam-grades))
           (id (get-id-num name exam-grades)))
        (append (list id name  instructor ta ex-grade1 ex-grade2) hw-grades))))
  
  (define all-grades
    (quicksort 
     (append
      (map (correct-form 'daria) d:grades)
      (map (correct-form 'sam) s:grades)
      (map (correct-form 'felix) f:grades)
      (map (correct-form 'carl) c:grades)
      (map (correct-form 'jeff) j:grades)
      )
     (lambda (x y)
       (string<? (cadr x) (cadr y)))))
  
  (define (get-instructor s)
    (list-ref s 2))
  (define get-professor get-instructor)
  
  (define (get-name s)
    (list-ref s 1))
  
  (define (get-id s)
    (list-ref s 0))
  
  (define (get-ta s)
    (list-ref s 3))
  
  (define (get-grades student)
    (cddr (cddddr student)))
  
  
  
  (define (get-quiz g)
    (if (= 1 (length g))
        (if (or (equal? (car g) #f) (equal? 0 (car g))) 0 1)
        (car g)))
  
  
  
  (define get-info
    (lambda (s) 
      (list (get-name s)
            (get-instructor s)
            (get-ta s)
            )))
  
  (define (get-quiz-grades gr)
    (map get-quiz gr))
  
  
  (define (calculate-grade quiz-grade hw-grade max-grades)
    (cond
      [(symbol? hw-grade) '?]
      [(not quiz-grade) #f]
      [(not hw-grade) #f]
      [(> (get-quiz max-grades) 1) hw-grade]
      [else (* hw-grade quiz-grade)]))
  
  
  
  (define (max-hw-week-n n)
    (cadr (list-ref s:max-scores (- n 1))))
  
  (define (get-week-n st n)
    (list-ref (get-grades st) (- n 1)))
  
  (define (hw-week-n student n)
    (get-hw (get-week-n student n)))
  
  (define (got-max-hw-week-n n)
    (define (f s week)
      (eqv? (hw-week-n s week) (max-hw-week-n week)))
    (select-students-week-n f n))
  
  (define (bad-hw-week-n n)
    (select-students-week-n
     (lambda (s week)
       (< (if (hw-week-n s week) (hw-week-n s week) (max-hw-week-n week)) (* .6 (max-hw-week-n week))))
     n))
  (define (sum-grades l)
    (foldl
     (lambda (x y) 
       (if x (+ x y) y))
     0
     l))
  
  
  (define (trunc n)
    (/ (floor (* 1000.0 n)) 1000))
  
  (define avg (lambda (l)
                (trunc (+ 0.0 (/ (sum-grades l) (length l))))))
  
  (define (avgt l)
    (avg (filter (lambda (x) x) l)))
  
  (define (bad-hw-this-week)
    (bad-hw-week-n s:this-week))
  
  (define (got-max-hw-this-week)
    (got-max-hw-week-n s:this-week))
  
  (define (median l)
    (let* ((ll (map (lambda (x) (or x 0)) l))
           (k (quicksort ll >))
           (len (length k)))
      (if (even? len)
          (avgt (list (list-ref k (/ len 2)) 
                      (list-ref k (sub1 (/ len 2)))))
          (list-ref k (/ (sub1 len) 2) ))))
  
  
  (define (median-week-n n)
    (let ((l (map (lambda (x) (hw-week-n x n)) all-grades)))
      (median l)))
  
  (define (mean-week-n n)
    (let ((l (map (lambda (x) (hw-week-n x n)) all-grades))
          )
      (avg l)))
  
  (define (fail? g)
    (if (number? g) (zero? g) (eq? g #f)))
  
  (define (avg-f f l)
    (avg (map f l)))
  
  (define (quiz-week-n student n)
    (get-quiz (get-week-n student n)))
  
  (define (quizzes-week-n n)
    (map (lambda (x) (quiz-week-n x n)) all-grades))
  
  (define (failed-quiz-week-n student n)
    (let ((q (quiz-week-n student n)))
      (or (equal? q #f) (equal? 0 q))))
  
  (define (failed-last-two-weeks-quiz student)
    (and (failed-quiz-week-n student s:this-week)
         (failed-quiz-week-n student (sub1 s:this-week))))
  
  (define (two-weeks-fail)
    (map get-info (filter failed-last-two-weeks-quiz all-grades)))
  
  (define (hws-week-n n)
    (map (lambda (x) (hw-week-n x n)) all-grades))
  
  (define (max-hw n)
    (get-hw (list-ref s:max-scores (- n 1))))
  (define (max-quiz n)
    (get-quiz (list-ref s:max-scores (- n 1))))
  
  (define (avg-hw-week-n n)
    (avgt (hws-week-n n)))
  (define (avg-quiz-week-n n)
    (avgt (quizzes-week-n n)))
  
  (define (avg-hws)
    (build-list (length s:max-scores) (lambda (x) (list (add1 x) (avg-hw-week-n (add1 x)) (max-hw (add1 x))))))
  (define (avg-quizzes)
    (build-list (length s:max-scores) (lambda (x) (list (add1 x) (avg-quiz-week-n (add1 x)) (max-quiz (add1 x))))))
  
  (define (all-avgs)
    (map (lambda (x y) (list
                        (car x)
                        (list "quiz" (cadr x) (caddr x))
                        (list "hw" (cadr x) (caddr y))
                        ))
         (avg-quizzes)
         (avg-hws)))
  
   (define (drop-lowest l)
    (define (drop-lowest-help l acc)
      (cond 
        [(empty? l) empty]
        [else (if (< (first l) acc) (drop-lowest-help (rest l) (first l))
                  (cons (first l) (drop-lowest-help (rest l) acc)))]))
    (drop-lowest-help (rest l) (first l)))
  
  (define (all-grades-week-n n) 
    (quicksort 
     (map (lambda (x y) (list (car x) y))
          all-grades
          (map (lambda (x) (if x x 0)) (map (lambda (x y) (and y x)) (hws-week-n n) (quizzes-week-n n))) 
          )
     (lambda (x y) (> (cadr x) (cadr y)))))
  
  (define (this-weeks-grades)
    (all-grades-week-n s:this-week))
  
  (define (this-weeks-avg)
    (avgt (all-grades-week-n s:this-week)))
  (define (prof p)
    (filter (lambda (x) (equal? (get-instructor x) p)) all-grades))
  (define (calculate-all-grades st)
    ;(display (get-name st))
    ;(display (get-grades st))
    (map calculate-grade (get-quiz-grades (get-grades st)) (get-hw-grades (get-grades st)) s:max-scores))
  
  (define (avg-by-prof-week-n-quiz w p)
    (trunc (/ (avgt (map (lambda (x) (quiz-week-n x w)) (prof p))) (max-quiz w))))
  
  (define (avg-by-prof-week-n-hw w p)
    (trunc (/ (avgt (map (lambda (x) (hw-week-n x w)) (prof p))) (max-hw w))))
  
  (define (prof-avgs n)
    (map (lambda (x) (list x (avg-by-prof-week-n-hw n x) (avg-by-prof-week-n-quiz n x))) '(mf vkp rjw)))
  
  (define (all-prof-avgs)
    (map prof-avgs (build-list s:this-week (lambda (x) (add1 x) ))))
  
  (define (normalize l1 l2)
    (map / (map (lambda (x) (if (boolean? x) 1 (or x 0))) l1) l2))

  (define (calculate-all-grades-norm st)
    (normalize (calculate-all-grades st) (get-hw-grades s:max-scores)))
  
  (define (student-avg/rcg s)
     (trunc (raise-carl-g s (avgt (drop-lowest (calculate-all-grades-norm s))))))
 
  (define (student-avg s)
     (trunc (avgt (drop-lowest (calculate-all-grades-norm s)))))
 
  (define (max-exam1-grade) (apply + 0 (cdr (reverse max-exam1-scores))))
  (define (max-exam2-grade) (apply + 0 (cdr (reverse max-exam2-scores))))
  
  (define (exam1-per s)
    (/ (get-exam1-score s) (max-exam1-grade)))

  (define (exam2-per s)
    (/ (get-exam2-score s) (max-exam2-grade)))

  (define (calc-total-grade s)
    (let ((e1 (exam1-per s))
          (e2 (exam2-per s))
          (h (student-avg s))
          )
      (trunc (/ (+ (* .32 e1) (* .32 e2) (* .36 h)) 1))))
  
   (define (calc-total-grade/rcg s)
    (let ((e1 (exam1-per s))
          (e2 (exam2-per s))
          (h (student-avg/rcg s))
          )
      (trunc (/ (+ (* .32 e1) (* .32 e2) (* .36 h)) 1))))
  
  (define (letter-grade s)
    (let ((f (calc-total-grade/rcg s)))
      (cond
        [(or (>= f .91) 
             (equal? (get-id s) "6425")
             (equal? (get-id s) "6423")
             (equal? (get-id s) "8085")
             (equal? (get-id s) "2085"))
         "A "]
        [(>= f .85) "A-"]
        [(>= f .81) "B+"]
        [(>= f .75) "B "]
        [(>= f .71) "B-"]
        [(>= f .675) "C+"]
        [(>= f .63) "C "]
        [(>= f .6) "C-"]
        [(equal? (get-id s) "3184") "C-"]
        [(>= f .55) "D+"]
        [(>= f .52) "D "]
        [(>= f .5) "D-"]
        [(equal? (get-id s) "1818") "D-"]
        [else "F "]
        )))
        
  
  (define (grade-for-matthias/rcg s)
    (list (get-id s) 
          (get-name s)
          (get-instructor s)
          (letter-grade s)
          (list 'total (calc-total-grade/rcg s) )
          (list 'exams: (* 1.0 (exam1-per s)) (trunc (exam2-per s))) 
          (list 'hw: (student-avg/rcg s) (map trunc (calculate-all-grades-norm s)))))
  
  (define (grades-to-post)
    (quicksort
     (map (lambda (s)
            (list (get-id s)
                  (letter-grade s)))
          all-grades)
    (lambda (x y)
      (string<=? (car x) (car y)))))
    
;  ("0798" vkp (total 0.503) (exams: 0.66 0.36)(hw: 0.492 (0.857 0     0.769 0.868 0.062 0 0.714 0.761 0     0.76)))
;  ("2389" mf (total 0.491) (exams: 0.76 0.22) (hw: 0.495 (0.047 0.037 0.846 0.973 0     0 0.142 0.809 0.676 0.021)))
;  ("1818" mf (total 0.478) (exams: 0.6 0.34)  (hw: 0.494 (0.904 0.444 0.948 0.763 0     0 0.107 0.761 0.882 0)))
;
  
;  
;  (define (grade-for-matthias s)
;    (list (get-id s) 
;          (get-name s)
;          (list 'total (calc-total-grade s) )
;          (list 'exams: (* 1.0 (exam1-per s)) (trunc (exam2-per s))) 
;          (list 'hw: (student-avg s) (map trunc (calculate-all-grades-norm s)))))
;  
  
  
;  (define (grades-for-matthias)
;    (quicksort 
;     (map grade-for-matthias all-grades)
;     (lambda (x y) (> (cadr (caddr x)) (cadr (caddr y))))))
  
  (define (caddddr a) (cadddr (cdr a)))
  
  (define (grades-for-matthias/rcg)
    (quicksort 
     (map grade-for-matthias/rcg all-grades)
     (lambda (x y) (> (cadr (caddddr x)) (cadr (caddddr y))))))
  
;  (define (find-student id)
;    (find (lambda (x) (equal? (car x) id)) (grades-for-matthias)))
  
  (define (find-student id)
    (find (lambda (x) (equal? (car x) id)) (grades-for-matthias/rcg)))

  
  (define (top k)
    (take (grades-for-matthias/rcg) k))


  (define (bot k)
    (take (reverse (grades-for-matthias/rcg)) k))
  
  
  (define (improved-exam s)
    (> (exam2-per s) (exam1-per s)))
  
  (define (improved-on-exams)
    (map grade-for-matthias/rcg (filter improved-exam all-grades)))
  
  (define (raise-carl-g s grade)
    (if (equal? (get-ta s) 'carl)
        (* grade 1.2)
        grade))
  
  
  (define (all-student-grades)
    (quicksort
     (map (lambda (s) (append (get-info s) (list (calc-total-grade s))))
          all-grades)
     (lambda (x y)
       (> (cadddr x) (cadddr y)))))
  
  (define (all-student-avgs-hw)
    (quicksort
     (map (lambda (s)
            (list (get-name s) (get-instructor s) (get-ta s)
                  (student-avg s)))
          all-grades)
     (lambda (x y)
       (> (cadddr x) (cadddr y)))))
  
  (define (failing-students-hw )
    (quicksort
     (filter 
      (lambda (x)
        (< (cadddr x) .4))
      (map (lambda (s)
             (list (get-name s) (get-professor s) (get-ta s)
                   (student-avg s)))
           all-grades)
      )
     (lambda (x y)
       (> (cadddr x) (cadddr y)))))
  
;  (define (bad-ex/good-hw s)
;    (let ((h (student-avg s))
;          (e (/ (get-exam1-score/bonus s) (max-exam-grade))))
;      (and (< e .4) (> h .6))))
;  
  (define (avg-hw-n n los)
    (let ((l (map (lambda (x) (hw-week-n x n)) los)))
      (avgt l)))
  
  (define (all-hw-avgs l)
    (build-list s:this-week (lambda (k) (avg-hw-n (add1 k) l))))
  
  (define (exam1-avg l)
    (avgt (map get-exam1-score l)))
  
  (define (exam2-avg l)
    (avgt (map get-exam2-score l)))

  (define (all-hw-avgs/norm l)
    (map trunc (map / (all-hw-avgs l) (map cadr s:max-scores))))
  
  (define (students/ta t)
    (filter (lambda (x) (equal? (get-ta x) t)) all-grades))
  
  (define (students/prof t)
    (filter (lambda (x) (equal? (get-instructor x) t)) all-grades))
  
  (define ta-list '(carl daria felix jeff sam))
  (define prof-list '(rjw mf vkp))
  
  (define (all-hw-avgs/ta ta)
    (let* ((l (students/ta ta))
           )
      (list* ta (all-hw-avgs/norm l))))

  (define (all-hw-avgs/prof p)
    (let* ((l (students/prof p))
           )
      (list* p (all-hw-avgs/norm l))))
  
  
  (define (hw-avgs/all-ta)
    (map (lambda  (x) (list (car x) (avgt (cdr x)))) (all-hw-avgs/all-ta)))
 
  (define (hw-avgs/all-prof)
    (map (lambda  (x) (list (car x) (avgt (cdr x)))) (all-hw-avgs/all-prof)))
   
  (define (exam1-avgs/ta ta)
    (let* ((l (students/ta ta))
           )
      (list ta (exam1-avg l))))
  
  
  
  (define (exam2-avgs/ta ta)
    (let* ((l (students/ta ta))
           )
      (list ta (exam2-avg l))))
  
   (define (exam1-avgs/prof prof)
    (let* ((l (students/prof prof))
           )
      (list prof (exam1-avg l))))
  
    (define (exam2-avgs/prof prof)
    (let* ((l (students/prof prof))
           )
      (list prof (exam2-avg l))))

  (define (all-hw-avgs/all-ta)
    (map all-hw-avgs/ta ta-list))
  
  (define (all-hw-avgs/all-prof)
    (map all-hw-avgs/prof prof-list))
  
  (define (exam1-avgs/all-prof)
    (map exam1-avgs/prof prof-list))
  (define (exam2-avgs/all-prof)
    (map exam2-avgs/prof prof-list))
  
  (define (exam1-avgs/all-ta)
    (map exam1-avgs/ta ta-list))
  (define (exam2-avgs/all-ta)
    (map exam2-avgs/ta ta-list))
  
  (define (total-avg l)
    (avgt (map calc-total-grade/rcg l)))
  
  (define (total-avgs/ta t)
    (list t (total-avg (students/ta t))))
  
  (define (total-avg/all-ta)
    (map total-avgs/ta ta-list))
  
   (define (total-avgs/prof t)
    (list t (total-avg (students/prof t))))
  
  (define (total-avg/all-prof)
    (map total-avgs/prof prof-list))
  
  (define (format-num-list x l)
    (apply string-append x
           (map (lambda (x)
                  (if (> x 9) (format "~v " x)
                      (format " ~v " x)))
                l)))

  (define (posting)
    (quicksort
     (map (lambda (s) 
            (list 
             (get-id s)
             (list  (format-num-list "exam1 " (list (get-exam1-score s))) (format-num-list "exam2 " (list (get-exam2-score s))))
             (list 'hw (format-num-list ""(map (lambda (x) (if x x 0)) (get-hw-grades (get-grades s)))))))
          all-grades)
    (lambda (x y) (string<=? (car x) (car y)))
    ))
    
  )
