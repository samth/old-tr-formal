;;; threads/tests.scm

(let ((time-stamp "Time-stamp: <2003-10-27 08:14:57 wand>"))
  (eopl:printf "threads/tests.scm ~a~%"
               (substring time-stamp 13 29)))

(define groups-for-test '(base let new-letrec implicit-store print concur lock))

;;;;;;;;;;;;;;;; interface to test harness ;;;;;;;;;;;;;;;;

(define equal-external-reps?
  (lambda (actual-outcome correct-outcome)
    (equal? actual-outcome (suite-val-to-exp correct-outcome))))

;; this tests numeric and boolean values only

(define suite-val-to-exp
  (lambda (correct-answer)
    (cond
      ((memv correct-answer '(error dontrun)) correct-answer)
      ((number? correct-answer) (num-val correct-answer))
      ((boolean? correct-answer) (bool-val correct-answer))
      (else (eopl:error 'suite-val-to-exp
                        "bad value in test suite: ~s"
                        correct-answer)))))

;;;;;;;;;;;;;;;; test groups ;;;;;;;;;;;;;;;;

;; tests for new letrec

(add-test! 'new-letrec 'fact-of-6  "letrec
fact = proc (x) if zero?(x) then 1 else *(x, (fact sub1(x)))
in (fact 6)" 720)


(add-test! 'new-letrec 'odd-of-13  "letrec
even = proc (x) if zero?(x) then 1 else (odd sub1(x))
odd  = proc (x) if zero?(x) then 0 else (even sub1(x))
in (odd 13)" 1)

(add-test! 'new-letrec 'HO-nested-letrecs
           "letrec even = proc (odd,x) if zero?(x) then 1 else (odd sub1(x))
           in letrec  odd = proc (x) if zero?(x) then 0 else (even odd sub1(x))
           in (odd 13)" 1)

(add-test! 'explicit-store 'gensym-test-1 
           "let g = let counter = newref(0) 
           in proc () let d = setref(counter, add1(deref(counter)))
           in deref(counter)
           in +((g),(g))" 3)


(add-test! 'explicit-store 'even-odd-via-set-1 "
           let x = newref(0)
           in letrec even = proc () if zero?(deref(x)) 
           then true
           else let d = setref(x, sub1(deref(x)))
           in (odd)
           odd = proc () if zero?(deref(x)) 
           then false
           else let d = setref(x, sub1(deref(x)))
           in (even)
           in let d = setref(x,13) in (odd)" #t)



(add-test! 'implicit-store 'gensym-test
           "let g = let count = 0 in proc() 
           let d = set count = add1(count)
           in count
           in +((g), (g))"
           3)

(add-test! 'implicit-store 'even-odd-via-set "
           let x = 0
           in letrec even = proc () if zero?(x) then true
           else let d = set x = sub1(x)
           in (odd)
           odd  = proc () if zero?(x) then false
           else let d = set x = sub1(x)
           in (even)
           in let d = set x = 13 in (odd)" #t)

; (add-test! 'mutable-pairs 'gensym-using-mutable-pair-left
; "let g = let count = pair(0,0) in proc() 
;                         let d = setleft(count,add1(left(count)))
;                         in left(count)
; in +((g), (g))"
; 3)

; ;;; gotta check the right, too!

; (add-test! 'mutable-pairs 'gensym-using-mutable-pair-right
; "let g = let count = pair(0,0) in proc() 
;                         let d = setright(count,add1(right(count)))
;                         in right(count)
; in +((g), (g))"
; 3)

;; check this by hand
(add-test! 'print 'print-1 "
let d = print(33)
in let d = print(44)
in 12"
           12)


;; check that this prints (1 2) or (2 1)
(add-test! 'concur 'concur-1 "
let d = spawn(proc() print(1)) in
let d = spawn(proc() print(2)) in
3" 3)

(add-test! 'concur 'concur-2 "
let acc = 0 
in let d = spawn(proc()set acc = 20)
in letrec 
loop = proc (n) if zero?(acc) then (loop) else acc
in (loop)
" 20)

(add-test! 'concur 'concur-2a "
let acc = 0 
in let d = spawn(proc()letrec 
                     loop = proc (n) if zero?(n) then set acc = 20
                     else let d = print(n) 
                     in (loop sub1(n))
                     in (loop 5))
in letrec 
loop = proc () if zero?(acc)
then let d = print(100) in (loop)      
else let d = print(200) in acc

in (loop)
" 20)


(add-test! 'concur 'concur-3 "
let buf1 = 0 buf2 = 0 buf3 = 0
in let d1 = spawn(proc()set buf1 = 20)
d2 = spawn(proc() letrec 
               loop = proc () if zero?(buf1)
               then (loop)
               else set buf2 = +(buf1,2)
               in (loop))
d3 = spawn(proc() letrec 
               loop = proc () if zero?(buf2)
               then (loop)
               else set buf3 = +(buf2,2)
               in (loop))
in letrec
loop = proc () if zero?(buf3) then (loop) else buf3
in (loop)
"
  24)

(add-test! 'concur 'concur-4 "
letrec 
  noisy = proc (l) if null?(l) 
                 then 0 
                 else let d = print(car(l)) in (noisy cdr(l))
in let d1 = spawn(proc () (noisy list(1,2,3,4,5)))
       d2 = spawn(proc () (noisy list(6,7,8,9,10)))
       d3 = spawn(proc () (noisy list(11,12,13,14,15,16,17)))
   in 33
"
  33)

;; here's locks, which we are not quite ready to do.

(add-test! 'locks 'shared-variable-1 "
let l = lock list(0)
    done = 0
in let t1 = spawn let c = acquire l
                  in begin
                       setcar(c,add1(car(c)));
                       setcar(c,add1(car(c)));
                       print(list(1,car(c)));
                       set done = add1(done);
                       release l
                     end
       t2 = spawn let c = acquire l
                  in begin 
                       setcar(c,add1(car(c)));
                       setcar(c,add1(car(c)));
                       print(list(2,car(c)));
                       set done = add1(done);
                       release l
                     end
   in let v = 0
      in letrec loop = proc() if equal?(done,2)
                         then let c = acquire l
                              in begin
                                   set v = car(c);
                                   release l;
                                   v
                                 end
                         else (loop)
         in (loop)
"
4)  

; Like concur-4, but now noisy is synchronized, so there is no interleaving:

(add-test! 'concur 'lock-4 "
let noisy =
      letrec     % private definition
         noisy = proc (l) if null?(l) 
                     then 0 
                     else let d = print(car(l)) in (noisy cdr(l))
      in let lck = lock() 
      in proc (lst)     % the public definition
           let d1 = acquire(lck) in
           % critical section
           let ans = (noisy lst) in
           let d3 = release(lck) in
           % end critical section
           ans
in % now do something interesting
let d1 = spawn(proc () (noisy list(1,2,3,4,5)))
    d2 = spawn(proc () (noisy list(6,7,8,9,10)))
    d3 = spawn(proc () (noisy list(11,12,13,14,15,16,17)))
in 33
"
  33)

; Now there are several instances of noisy, each separately
; synchronized.  In the output, the items 1,..,10 and 11,..,20 should
; each appear consecutively, but the two lists should be interleaved.

(add-test! 'concur 'lock-5 "
let gen-noisy = proc ()
      letrec 
         noisy = proc (l) if null?(l) 
                     then 0 
                     else let d = print(car(l)) in (noisy cdr(l))
      in let lck = lock() 
      in proc (lst)
          let d1 = acquire(lck) in
          let ans = (noisy lst) in
          let d3 = release(lck) in
          ans
in
  let noisy1 = (gen-noisy)
      noisy2 = (gen-noisy)
  in
   let d1 = spawn(proc () (noisy1 list(1,2,3,4,5)))
       d2 = spawn(proc () (noisy1 list(6,7,8,9,10)))
       d3 = spawn(proc () (noisy2 list(11,12,13,14,15)))
       d4 = spawn(proc () (noisy2 list(16,17,18,19,20)))
   in 33
"
  33)
(let ((make-dining-philosopher-program
       (lambda (strategy)
         (string-append
   "let N = 5
        fork0 = lock()
        fork1 = lock()
        fork2 = lock()
        fork3 = lock()
        fork4 = lock()
        the-mystery-fork = lock()
                                                                                                           
        count = letrec count = proc(x) if zero?(x) then 42 else (count -(x,1))
                       in count
    in
    let take-left-fork =
                    proc(i)
                      let fork =
                            if zero?(-(i,0)) then acquire(fork0) else
                            if zero?(-(i,1)) then acquire(fork1) else
                            if zero?(-(i,2)) then acquire(fork2) else
                            if zero?(-(i,3)) then acquire(fork3) else
                            if zero?(-(i,4)) then acquire(fork4) else
                            acquire(the-mystery-fork) % error case
                      in (count 50)
        take-right-fork =
                    proc(i)
                      let fork =
                            if zero?(-(i,0)) then acquire(fork1) else
                            if zero?(-(i,1)) then acquire(fork2) else
                            if zero?(-(i,2)) then acquire(fork3) else
                            if zero?(-(i,3)) then acquire(fork4) else
                            if zero?(-(i,4)) then acquire(fork0) else
                            acquire(the-mystery-fork) % error case
                      in (count 50)
        put-left-fork =
                   proc(i)  if zero?(-(i,0)) then release(fork0) else
                            if zero?(-(i,1)) then release(fork1) else
                            if zero?(-(i,2)) then release(fork2) else
                            if zero?(-(i,3)) then release(fork3) else
                            if zero?(-(i,4)) then release(fork4) else
                            release(the-mystery-fork) % error case
        put-right-fork =
                   proc(i)  if zero?(-(i,0)) then release(fork1) else
                            if zero?(-(i,1)) then release(fork2) else
                            if zero?(-(i,2)) then release(fork3) else
                            if zero?(-(i,3)) then release(fork4) else
                            if zero?(-(i,4)) then release(fork0) else
                            release(the-mystery-fork) % error case
   in let make-philosopher =
          let think = proc()  let d = (count 100) in 42
              eat   = proc(i) let p = print(i) in
                              let p = print(100) in
                              let d = (count 50) in
                              let p = print(999) in
                              let p = print(i) in
                              24
          in " strategy "
      in let philosopher-0 = spawn( proc() (make-philosopher 0))
      in let philosopher-1 = spawn( proc() (make-philosopher 1))
      in let philosopher-2 = spawn( proc() (make-philosopher 2))
      in let philosopher-3 = spawn( proc() (make-philosopher 3))
      in let philosopher-4 = spawn( proc() (make-philosopher 4))
      in (count 1000)"))))
                                                                                                           
  (add-test!
   'concur 'starving-philosophers
   (make-dining-philosopher-program
      "proc(i)
           let step1 = (think)
        in let step2 = (take-left-fork i)
        in let step3 = (take-right-fork i)
        in let step4 = (eat i)
        in let step5 = (put-left-fork i)
        in let step6 = (put-right-fork i)
        in 13")
     42)
                                                                                                           
    (add-test!
     'concur 'a-single-dining-philosopher
     (make-dining-philosopher-program
      "let one-mutex = lock()
       in proc(i)
              let step1 = (think)
           in let step1b = acquire(one-mutex)
           in let step2 = (take-left-fork i)
           in let step3 = (take-right-fork i)
           in let step4 = (eat i)
           in let step5 = (put-left-fork i)
           in let step6 = (put-right-fork i)
           in let step6b = release(one-mutex)
           in 13")
     42)
    )
(add-test! 'concur 'lock-acquire-release-dot-dot-dot "
let lck = lock() in
  letrec f = proc (n)
    let a1 = acquire(lck) in
    let r1 = release(lck) in
    let a2 = acquire(lck) in
    let r2 = release(lck) in
    let a3 = acquire(lck) in
    let r3 = release(lck) in
    if zero?(n) then n else (f sub1(n))
in
let d1 = spawn(proc () (f 1))
    d2 = spawn(proc () (f 3))
    d3 = spawn(proc () (f 5))
in 33
"
33)
;; We do this again so we can check if we actually
;; do *release* the locks
(add-test! 'lock 'lock-acquire-release-dot-dot-dot-2 "
let lck = lock() in
  letrec f = proc (n)
    let a1 = acquire(lck) in
    let r1 = release(lck) in
    let a2 = acquire(lck) in
    let r2 = release(lck) in
    let a3 = acquire(lck) in
    let r3 = release(lck) in
    if zero?(n) then n else (f sub1(n))
in
let d1 = spawn(proc () (f 5))
    d2 = spawn(proc () (f 3))
    d3 = spawn(proc () (f 1))
in 33
"
33)
(add-test! 'lock-not-run 'lock-some-work "
let v = pair(0,0)
    lck = lock()
    equal? = proc(a,b) zero?(-(a,b))
in
  letrec
    f = proc (n)
      let a = acquire(lck) in
      let s = set v = pair(n,n) in
      let z = +(1,-(2,+(1,-(2,+(1,-(2,+(1,-(2,+(1,-(2,3)))))))))) in
      if (equal? left(v) n) then
        if (equal? right(v) n) then
          let r = release(lck) in
            if zero?(n) then n else (f sub1(n))
        else (error) % this'll throw an error
      else (error) % this'll throw an error
in
let d1 = spawn(proc () (f 3))
    d2 = spawn(proc () (f 5))
    d3 = spawn(proc () (f 7))
in 33
"
33)

;; Again, doing this will reverse values for the recursion
;; variables could show that we were releasing locks incorrectly.
;; And I was, I wasn't setting the owner's value to -1, hence
;; I thought a thread was trying to acquire a non-free lock owned
;; by that thread
(add-test! 'lock-not-run 'lock-some-work-2 "
let v = pair(0,0)
    lck = lock()
    equal? = proc(a,b) zero?(-(a,b))
in
  letrec
    f = proc (n)
      let a = acquire(lck) in
      let s = set v = pair(n,n) in
      let z = +(1,-(2,+(1,-(2,+(1,-(2,+(1,-(2,+(1,-(2,3)))))))))) in
      if (equal? left(v) n) then
        if (equal? right(v) n) then
          let r = release(lck) in
            if zero?(n) then n else (f sub1(n))
        else (error) % this'll throw an error
      else (error) % this'll throw an error
in
let d1 = spawn(proc () (f 7))
    d2 = spawn(proc () (f 5))
    d3 = spawn(proc () (f 3))
in 33
"
33)
(add-test! 'lock 'lock-error-acquiring-own-lock "
let lck = lock() in
  let d1 = acquire(lck) in
    let d2 = acquire(lck) in
      d2
"
'error)
                                                                                                           
(add-test! 'lock 'lock-error-illegal-value-for-lock "
let lck = 3 in
  let d1 = acquire(lck) in
    d1
"
'error)
                                                                                                           
(add-test! 'lock 'lock-error-attempt-to-release-free-lock "
let lck = lock() in
  let d1 = release(lck) in
    d1
"
'error)
                                                                                                           
(add-test! 'lock 'lock-error-attempt-to-release-someone-elses-lock "
let lck = lock() in
  let d1 = acquire(lck) in
    let d2 = spawn(proc () release(lck)) in
      d2
"
'error)
