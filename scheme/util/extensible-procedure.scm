(module extensible-procedure mzscheme
  (provide define-extensible define-extension)
  (require (file "etc.scm"))
  (require (lib "etc.ss"))
  (require (lib "match.ss"))
  
  (define-struct ext-impl (fun))
  (define-procedural-struct (ext ext-impl)
    (lambda l
      ;; Below, note that I'm applying the fun to L, not (CDR L)
      (apply (ext-impl-fun (car l)) l)))
  
  ;; The below forms might be further generalizable to handle:
  ;; * argslist, using dotted pair a la (self . ARGLIST)
  ;; * multiple predicates in the extensible/extension definitions
  ;;   (would need to make sure that the case-lambdas are rewritten to
  ;;   try the next predicate for the current extension and not
  ;;   immediately fall back on the super class implementation)

  (define-syntax define-extensible
    (syntax-rules ()
      [(define-extensible (PROC ARGS ...) BODY ...)
       (define PROC
         (letrec ((obj (make-ext 
                        ;; Writing out the self-pass-and-bind here
                        ;; explicitly to make the dynamic-dispatch
                        ;; pattern clear.
                        (lambda (self ARGS ...)
                          (let ((PROC self))
                            BODY ...)))))
           obj))]))
  
  (define-syntax define-extension
    (syntax-rules ()
      [(define-extension (EXT-NAME BASE-EXP) 
         [(ARGS ...) PRED BODY ...])
       (define EXT-NAME 
         (let* ((base-obj BASE-EXP))
           (letrec ((ext-obj (make-ext 
                              (case-lambda
                                [(self ARGS ...) 
                                 ;; Again, making self-pass-and-bind to clarify dispatch
                                 (cond [PRED (let ((EXT-NAME self)) BODY ...)]
                                       [else ((ext-impl-fun base-obj) self ARGS ...)])]
                                [l (apply (ext-impl-fun base-obj) l)])
                              )))
             ext-obj)))]))

#| SAMPLE USAGE

(define-extensible (map-none f x) 
  (error 'map-none "No proper arg given"))

(define-extension (mapl map-none) 
  [(f l) (list? l) 
   (if (null? l) l (cons (f (car l)) 
                         (mapl f (cdr l))))])

(define-extension (mapv map-none) 
  [(f v) (vector? v) 
   (let* ((len (vector-length v)) 
          (v2 (make-vector len))) 
     (let loop ((i 0))
       (cond [(= i len) v2] 
             [else (vector-set! v2 i (f (vector-ref v i)))
                   (loop (+ i 1))])))])

(define-extensible (maps f s)
  (cond [(list? s) (map (lambda (x) (maps f x)) s)]
        [else (f s)]))

(define-extension (mapsv maps)
  [(f v) (vector? v) (mapv (lambda (x) (mapsv f x)) v)])

|#

#| Some notes:
- As a matter of style in
 (DEFINE-EXTENSION (EXT-NAME BASE-EXP) [(ARGS ...) PRED BODY ...]), 
 you really shouldn't use BASE-EXP in BODY ... unless you really
 know what you're doing; its better to decompose the data and then 
 call EXT-NAME recursively, so that you'll properly dispatch to 
 further extensions that you are unaware of.
|#
)
