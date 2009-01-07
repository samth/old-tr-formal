#lang scheme

(require redex/reduction-semantics "opsem.ss")



(define (mk-result t #:then [thn null] #:else [els null] #:s [s 0])
  (term (,t (,thn ,els) ,s)))

(define (var-res t var #:path [p null])
  (mk-result t 
             #:then (list (term (! #f ,p ,var)))
             #:else (list (term (#f ,p ,var)))
             #:s (term (,p ,var))))

(define (type-res t var #:path [p null])
  (mk-result (term (U #t #f))
             #:then (list (term (,t ,p ,var)))
             #:else (list (term (! ,t ,p ,var)))))

(define (*and a b)
  (term (if ,a ,b #f)))

(define (*or a b)
  (term (if ,a #t ,b)))

(define-syntax-rule (truety t)
  (term (,t (() (bot)) 0)))

(define-syntax predtype
  (syntax-rules ()
    [(_ ty in p) (term (,in -> (U #t #f) : (((,ty ,p)) ((! ,ty ,p))) : 0))]
    [(_ ty in) (predtype ty in (term ()))]
    [(_ ty) (predtype ty (term top))]))

(test--> reductions (if #t 1 2) 1)
(test-equal (term (no-overlap #t (U #t #f))) #f)

(define-syntax (type-tests stx)
  (syntax-case stx (test-equal term tc)
    [(_ lst (test-equal (term (tc G trm)) ty) ...)
     (with-syntax ([(nm ...) (generate-temporaries #'(trm ...))])
       #'(begin (define-values (lst fn)
                  (let ()
                    (define nm (term trm)) ...
                    (values 
                     (for/list ([n (list nm ...)])
                        (term (subst-n (x (cons 1 2)) (y #f) ,n)))
                     (lambda ()
                       (test-equal (term (tc G ,nm)) ty) ...))))
                (fn)))]))

(type-tests 
 test-terms
 (test-equal (term (tc ([x top]) x))
             (var-res (term top) (term x)))
 
 (test-equal (term (tc ([x (pr top top)]) (car x)))
             (var-res (term top) (term x) #:path (term (car))))
 
 (test-equal (term (tc ([x top]) (number? x)))
             (type-res (term N) (term x)))
 
 (test-equal (term (tc ([x (pr top top)]) (number? (car x))))
             (type-res (term N) (term x) #:path (list 'car)))
 
 (test-equal (term (tc () #f))
             (term (#f ((bot) ()) 0)))
 
 (test-equal (term (tc () 3))
             (term (N (() (bot)) 0)))
 
 (test-equal (term (tc () #t))
             (term (#t (() (bot)) 0)))
 
 (test-equal (term (tc ([x top] [y top])
                       ,(*and (term (number? x)) (term (boolean? y)))))
             (term ((U #t #f) (((N () x) ((U #t #f) () y)) ()) 0)))
 
 (test-equal (term (tc ([x top] [y top])
                       ,(*or (term (number? x)) (term (boolean? y)))))
             (term ((U #t #f) (() ((! N () x) (! (U #t #f) () y))) 0)))
 
 (test-equal (term (tc ([x top])
                       ,(*and (term (number? x)) (term (boolean? x)))))
             (term ((U #t #f) (((N () x) ((U #t #f) () x)) ()) 0)))
 
 (test-equal (term (tc ([x top])
                       ,(*or (term (number? x)) (term (boolean? x)))))
             (type-res (term (U N #t #f)) (term x)))
 
 
 (test-equal (term (tc () (lambda ([x : top]) x)))
             (truety (term (top -> top : (((! #f ())) ((#f ()))) : (() 0)))))
 
 (test-equal (term (tc () number?))
             (truety (predtype (term N))))
 
 (test-equal (term (tc () (lambda ([x : top]) (number? x))))
             (truety (predtype (term N))))
 
 (test-equal (term (tc () (cons 1 2)))
             (truety (term (pr N N))))
 
 (test-equal (term (tc () (lambda ([x : (pr top top)]) (number? (car x)))))
             (truety (predtype (term N) (term (pr top top)) (term (car)))))
 
 (test-equal (term (tc () (lambda ([x : (pr top top)]) (number? (cdr x)))))
             (truety (predtype (term N) (term (pr top top)) (term (cdr)))))
 
 (test-equal (term (tc () (lambda ([x : (pr top top)]) (not (number? (car x))))))
             (truety (term ((pr top top) -> (U #t #f) : (((! N (car))) ((N (car)))) : 0))))
 
 (test-equal (term (tc () (lambda ([x : top]) #f)))
             (truety (term (top -> #f : ((both) ()) : 0))))
 
 (test-equal (term (tc () (lambda ([x : top] [y : top]) (number? x))))
             (truety (term (top top -> (U #t #f) : (((N ())) ((! N ()))) (() ()) : 0))))
 
 (test-equal (term (tc () (if #f (add1 #f) 0)))
             (truety (term N)))
 )
(test-results)

(provide test-terms)