(load "lang.scm")


;;;;;;;;;;;;;;;; The Type Checker ;;;;;;;;;;;;;;;;

(define type-check
  (lambda (string)
    (type-to-external-form
      (type-of-program
        (scan&parse string))))) 



(define-datatype type type?
  (atomic-type (name symbol?))
  (proc-type
    (arg-types (list-of type?))
    (result-type type? )
    (poly boolean? )) 
  (gproc-type
   (arg-types (list-of type?))
   (result-type type?))
  (tvar-type
    (tvar tvar?))
  (pair-type
   (f type?) (s type?)))

(define type-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp) (type-of-expression exp (empty-tenv))))))
(define type-of-expression
  (lambda (exp tenv)
    (cases expression exp
      (lit-exp (number) int-type)
      (true-exp () bool-type)
      (false-exp () bool-type)
      (var-exp (id) (apply-tenv tenv id))
      (if-exp (test-exp true-exp false-exp)
        (let
          ((test-type (type-of-expression test-exp tenv))
           (false-type (type-of-expression false-exp tenv))
           (true-type (type-of-expression true-exp tenv)))
          ;; these tests either succeed or raise an error
          (check-equal-type! test-type bool-type test-exp)
          (check-equal-type! true-type false-type exp)
          true-type))
      (proc-exp (texps ids body)
        (type-of-proc-exp texps ids body tenv))      
      (primapp-exp (prim rands)
        (type-of-application
          (type-of-primitive prim)
          (types-of-expressions rands tenv)
          prim rands exp))
      (app-exp (rator rands) 
        (type-of-application
          (type-of-expression rator tenv)
          (types-of-expressions rands tenv)
          rator rands exp))
      (let-exp (ids rands body) (type-of-let-exp ids rands body tenv))
      (letrec-exp (result-texps proc-names texpss idss bodies
                    letrec-body)
        (type-of-letrec-exp
          result-texps proc-names texpss idss bodies
          letrec-body tenv))
      (lettype-exp (type-name texp
                     result-texps proc-names texpss
                     idss bodies lettype-body)
        (type-of-lettype-exp type-name texp
          result-texps proc-names texpss idss bodies
          lettype-body tenv))
      (effect-exp (name args)
                  (cases effect name
                    (pair-effect ()
                                 (pair-type 
                                  (type-of-expression (car args) tenv)
                                  (type-of-expression (cadr args) tenv))
                                 )
                    (left-effect ()
                                 (let ((npt (pair-type (fresh-tvar-type) (fresh-tvar-type))))
                                   (begin 
                                     (check-equal-type! npt (type-of-expression (car args) tenv) exp)
                                     (pair-type-fst npt))))
                    (right-effect ()
                                  (let ((npt (pair-type (fresh-tvar-type) (fresh-tvar-type))))
                                    (begin 
                                      (check-equal-type! npt (type-of-expression (car args) tenv) exp)
                                      (pair-type-snd npt))))
                    (setleft-effect () 
                                    (let ((npt (pair-type (fresh-tvar-type) (fresh-tvar-type))))
                                      (begin 
                                        (check-equal-type! npt (type-of-expression (car args) tenv) exp)
                                        (check-equal-type! (pair-type-fst npt) (type-of-expression (cadr args) tenv) exp)
                                        int-type)))
                    (setright-effect () 
                                     (let ((npt (pair-type (fresh-tvar-type) (fresh-tvar-type))))
                                       (begin 
                                         (check-equal-type! npt (type-of-expression (car args) tenv) exp)
                                         (check-equal-type! (pair-type-snd npt) (type-of-expression (cadr args) tenv) exp)
                                         int-type)))

                    (else #f)))
      )))

(define type-of-expression/let
  (lambda (exp tenv)
    (cases expression exp
      (lit-exp (number) int-type)
      (true-exp () bool-type)
      (false-exp () bool-type)
      (var-exp (id) (apply-tenv tenv id))
      (if-exp (test-exp true-exp false-exp)
        (let
          ((test-type (type-of-expression test-exp tenv))
           (false-type (type-of-expression false-exp tenv))
           (true-type (type-of-expression true-exp tenv)))
          ;; these tests either succeed or raise an error
          (check-equal-type! test-type bool-type test-exp)
          (check-equal-type! true-type false-type exp)
          true-type))
      (proc-exp (texps ids body)
        (type-of-proc-exp/let texps ids body tenv))      
      (primapp-exp (prim rands)
        (type-of-application
          (type-of-primitive prim)
          (types-of-expressions rands tenv)
          prim rands exp))
      (app-exp (rator rands) 
        (type-of-application
          (type-of-expression rator tenv)
          (types-of-expressions rands tenv)
          rator rands exp))
      (let-exp (ids rands body) (type-of-let-exp ids rands body tenv))
      (letrec-exp (result-texps proc-names texpss idss bodies
                    letrec-body)
        (type-of-letrec-exp
          result-texps proc-names texpss idss bodies
          letrec-body tenv))
      (lettype-exp (type-name texp
                     result-texps proc-names texpss
                     idss bodies lettype-body)
        (type-of-lettype-exp type-name texp
          result-texps proc-names texpss idss bodies
          lettype-body tenv))
      (effect-exp (name args)
                  (cases effect name
                    (pair-effect ()
                                 (pair-type 
                                  (type-of-expression (car args) tenv)
                                  (type-of-expression (cadr args) tenv))
                                 )
                    (left-effect ()
                                 (let ((npt (pair-type (fresh-tvar-type) (fresh-tvar-type))))
                                   (begin 
                                     (check-equal-type! npt (type-of-expression (car args) tenv) exp)
                                     (pair-type-fst npt))))
                    (right-effect ()
                                  (let ((npt (pair-type (fresh-tvar-type) (fresh-tvar-type))))
                                    (begin 
                                      (check-equal-type! npt (type-of-expression (car args) tenv) exp)
                                      (pair-type-snd npt))))
                    (setleft-effect () 
                                    (let ((npt (pair-type (fresh-tvar-type) (fresh-tvar-type))))
                                      (begin 
                                        (check-equal-type! npt (type-of-expression (car args) tenv) exp)
                                        (check-equal-type! (pair-type-fst npt) (type-of-expression (cadr args) tenv) exp)
                                        int-type)))
                    (setright-effect () 
                                     (let ((npt (pair-type (fresh-tvar-type) (fresh-tvar-type))))
                                       (begin 
                                         (check-equal-type! npt (type-of-expression (car args) tenv) exp)
                                         (check-equal-type! (pair-type-snd npt) (type-of-expression (cadr args) tenv) exp)
                                         int-type)))

                    (else #f)))
      )))

(define type-of-proc-exp
  (lambda (texps ids body tenv)
    (let ((arg-types (expand-optional-type-expressions texps tenv)))
      (let ((result-type
              (type-of-expression body
                (extend-tenv ids arg-types tenv))))
        (proc-type arg-types result-type #f)))))

(define type-of-proc-exp/let
  (lambda (texps ids body tenv)
    (let ((arg-types (expand-optional-type-expressions texps tenv)))
      (let ((result-type
              (type-of-expression body
                (extend-tenv ids arg-types tenv))))
        (proc-type arg-types result-type #t)))))


(define type-of-application             
  (lambda (rator-type actual-types rator rands exp)
    (let ((result-type (fresh-tvar-type)))
      (check-equal-type!
        rator-type
        (proc-type actual-types result-type #f)
        exp)
      result-type)))

(define types-of-expressions
  (lambda (rands tenv)
    (map
      (lambda (exp) (type-of-expression exp tenv))
      rands)))

(define types-of-expressions/let
  (lambda (rands tenv)
    (map
      (lambda (exp) (type-of-expression/let exp tenv))
      rands)))


(define type-of-let-exp
  (lambda (ids rands body tenv)
    (let ((tenv-for-body
            (extend-tenv-with-type-schemes     ; lecture7-3
              ids
              (types-of-expressions/let rands tenv)
              tenv)))
      (type-of-expression body tenv-for-body))))

(define type-of-letrec-exp
  (lambda (result-texps proc-names arg-optional-texpss idss bodies
            letrec-body tenv) 
    (let
      ((arg-typess
         (map
           (lambda (optional-texps)
             (expand-optional-type-expressions optional-texps tenv))
           arg-optional-texpss))
       (result-types
         (expand-optional-type-expressions result-texps tenv)))
    (let ((the-proc-types
            (map proc-type arg-typess result-types)))
      (let ((tenv-for-body                 ;^ type env for all proc-bodies
              (extend-tenv proc-names the-proc-types tenv)))
        (for-each                     
          (lambda (ids arg-types body result-type)
            (check-equal-type!
              (type-of-expression 
                body
                (extend-tenv ids arg-types tenv-for-body))
              result-type
              body))
          idss arg-typess bodies result-types)
        (type-of-expression letrec-body tenv-for-body))))))

(define extend-tenv-with-typedef-exp
  (lambda (typename texp tenv)
    (extend-tenv-with-typedef typename
      (expand-type-expression texp tenv)
      tenv)))

(define extend-tenv-with-type-exps
  (lambda (ids texps tenv)
    (extend-tenv ids
      (expand-type-expressions texps tenv)
      tenv)))

(define fresh-type
  (let ((serial-number 0))
    (lambda (s)
      (set! serial-number (+ serial-number 1))
      (atomic-type 
        (string->symbol
          (string-append
            (symbol->string s)
            (number->string serial-number)))))))

(define type-of-lettype-exp
  (lambda (type-name texp
            result-texps proc-names arg-texpss idss bodies
            lettype-body tenv)
    (let
      ((the-new-type (fresh-type type-name))
       (rhs-texps  
         (map proc-type-exp arg-texpss result-texps)))
      (let
        ((tenv-for-implementation
           ;; here type definition is known-- bind it to its definition
           (extend-tenv-with-typedef-exp type-name texp tenv))
         (tenv-for-client
           ;; here the defined type is opaque-- bind it to a new atomic type
           (extend-tenv-with-typedef type-name the-new-type tenv)))
        (let
          ((tenv-for-proc             ; type env for all proc-bodies
             (extend-tenv-with-type-exps
               proc-names rhs-texps tenv-for-implementation))
           (tenv-for-body                   ; type env for body
             (extend-tenv-with-type-exps
               proc-names rhs-texps tenv-for-client)))
          (for-each                     
            (lambda (ids arg-texps body result-texp)
              (check-equal-type!
                (type-of-expression 
                  body
                  (extend-tenv-with-type-exps
                    ids arg-texps tenv-for-proc))
                (expand-type-expression
                  result-texp tenv-for-proc)
                body))
            idss arg-texpss
            bodies result-texps)
          (type-of-expression lettype-body tenv-for-body))))))

;;;;;;;;;;;;;;;; types ;;;;;;;;;;;;;;;;



(define free-tvars                      ; new for lecture7-3
  (lambda (t)
    (cases type t
      (atomic-type (name) '())
      (pair-type (fst snd) (union (free-tvars fst) (free-tvars snd)))
      (proc-type (arg-types result-type poly)
        (union
          (free-tvars* arg-types) 
          (free-tvars result-type)))
      (gproc-type (arg-types result-type)
        (union
          (free-tvars* arg-types) 
          (free-tvars result-type)))

      (tvar-type (tv)
        (tvar-select-contents tv
          free-tvars
          (lambda () (list tv)))))))

(define free-tvars*
  (lambda (ts)
    (if (null? ts) '()
      (union
        (free-tvars (car ts))
        (free-tvars* (cdr ts))))))

;;; selectors and extractors for types

(define atomic-type?
  (lambda (ty)
    (cases type ty
      (atomic-type (name) #t)
      (else #f))))

(define pair-type?
  (lambda (ty)
    (cases type ty
      (pair-type (f s) #t)
      (else #f))))

(define proc-type?
  (lambda (ty)
    (cases type ty
      (proc-type (arg-types result-type poly) #t)
      (else #f))))
(define gproc-type?
  (lambda (ty)
    (cases type ty
      (gproc-type (arg-types result-type) #t)
      (else #f))))

; type -> (optional tvar)
(define tvar-type?
  (lambda (ty)
    (cases type ty
      (tvar-type (tv) tv)
      (else #f))))

(define fresh-tvar-type
  (lambda ()
    (tvar-type (fresh-tvar))))

(define atomic-type->name
  (lambda (ty)
    (cases type ty
      (atomic-type (name) name)
      (else (eopl:error 'atomic-type->name
              "Not an atomic type: ~s" ty)))))

(define proc-type->arg-types
  (lambda (ty)
    (cases type ty
      (proc-type (arg-types result-type poly) arg-types)
      (else (eopl:error 'proc-type->arg-types
              "Not a proc type: ~s" ty)))))


(define proc-type->poly
  (lambda (ty)
    (cases type ty
      (proc-type (arg-types result-type poly) poly)
      (else (eopl:error 'proc-type->poly
              "Not a proc type: ~s" ty)))))

(define proc-type->result-type
  (lambda (ty)
    (cases type ty
      (proc-type (arg-types result-type poly) result-type)
      (else (eopl:error 'proc-type->arg-types
              "Not a proc type: ~s" ty)))))

(define pair-type-fst
  (lambda (ty)
    (cases type ty
      (pair-type (fst snd) fst)
      (else (eopl:error "not a pair type: ~s" ty)))))

(define pair-type-snd
  (lambda (ty)
    (cases type ty
      (pair-type (fst snd) snd)
      (else (eopl:error "not a pair type: ~s" ty)))))

;;;;;;;;;;;;;;;; type variables ;;;;;;;;;;;;;;;;

(define-datatype tvar tvar?
  (a-tvar
    (serial-number integer?)
    (container
      (lambda (v)                       ; this is only checked at
                                        ; construction time, so it's
                                        ; useless except as documentation. 
        (and
          (vector? v)
          (= (vector-length v) 1)
          ((optional type?) (vector-ref v 0)))))))

(define optional
  (lambda (pred)
    (lambda (v)
      (or (not v) (pred v)))))

;; in a tvar, the container is a vector of length 1.  It can
;; contain either: 
;; 1.  #f, meaning that nothing is known about this tvar
;; 2.  a (pointer to) a type
;; also:  type structures may never be cyclic.

(define fresh-tvar
  (let ((serial-number 0))
    (lambda ()
      (set! serial-number (+ 1 serial-number))
      (a-tvar serial-number (vector #f)))))
    
(define tvar->contents
  (lambda (tv)
    (cases tvar tv
      (a-tvar (serial-number container)
        (vector-ref container 0)))))

(define tvar->serial-number
  (lambda (tv)
    (cases tvar tv
      (a-tvar (serial-number container)
        serial-number))))

(define tvar-set-contents!
  (lambda (tv val)
    (cases tvar tv
      (a-tvar (serial-number container)
        (vector-set! container 0 val)))))

;; a better abstraction than tvar->contents

(define tvar-select-contents
  (lambda (tv receiver thunk-for-false)
    (let ((contents (tvar->contents tv)))
      (if contents
        (receiver contents)
        (thunk-for-false)))))

;;;;;;;;;;;;;;;; type schemes ;;;;;;;;;;;;;;;;

;; a type scheme a list of local tvars and a type.  The tvars are
;; intended to be local to the type.

(define-datatype type-scheme type-scheme?
  (a-type-scheme
    (local-tvars (list-of tvar?))
    (type type?)))

;; we walk through the type, substituting fresh tvar-types for each
;; local tvar.

(define instantiate-type-scheme
  (lambda (s)
    (cases type-scheme s
      (a-type-scheme (tvars t)
        (let ((subst
                (map
                  (lambda (tvar) (cons tvar (fresh-tvar-type)))
                  tvars)))
          (let recur ((t t))
            (cases type t
              (atomic-type (name) t) 
              (gproc-type (arg-types result-type)
                (gproc-type (map recur arg-types) (recur result-type)))
              (proc-type (arg-types result-type poly)
                (proc-type (map recur arg-types) (recur result-type) poly))
              (pair-type (fst snd)
                         (pair-type (recur fst) (recur snd)))
              (tvar-type (tvar)
                (tvar-select-contents tvar 
                  recur
                  (lambda ()
                    (if (memq tvar tvars)
                      (cdr (assq tvar subst))
                      t)))))))))))


;;;;;;;;;;;;;;;; expand-type-expression and friends ;;;;;;;;;;;;;;;;

(define expand-optional-type-expressions
  (lambda (otexps tenv)
    (map
      (lambda (otexp)
        (expand-optional-type-expression otexp tenv))
      otexps)))

(define expand-optional-type-expression
  (lambda (otexp tenv)
    (cases optional-type-exp otexp
      (no-type-exp () (fresh-tvar-type))
      (a-type-exp (texp) (expand-type-expression texp tenv)))))

(define expand-type-expressions
  (lambda (texps tenv)
    (map 
      (lambda (texp)
        (expand-type-expression texp tenv))
      texps)))

(define expand-type-expression
  (lambda (texp tenv)
    (letrec 
      ((loop (lambda (texp)
               (cases type-exp texp
                 (tid-type-exp (id) (apply-tenv-typedef tenv id))
                 (int-type-exp () (atomic-type 'int))
                 (bool-type-exp () (atomic-type 'bool))
                 (proc-type-exp (arg-texps result-texp)
                   (proc-type
                     (map loop arg-texps)
                     (loop result-texp)))))))
      (loop texp))))

;;;;;;;;;;;;;;;; the unifier ;;;;;;;;;;;;;;;;

;;; cases is very cumbersome in this application, so don't use it!

(define check-equal-type!
  (lambda (ty1 ty2 exp)
    (unify! ty1 ty2 exp)))

(define (g/proc-type? t)
  (or (gproc-type? t) (proc-type? t)))

; either returns #t or fails
(define unify!
  (lambda (ty1 ty2 exp)
    (cond
      ((eqv? ty1 ty2))                  ; succeed with void result
      ((tvar-type? ty1)
       =>                               ; => binds result of test to tv
       (lambda (tv)
         (tvar-select-contents tv
           (lambda (contents) (unify! contents ty2 exp))
           (lambda ()
             (begin
               (check-no-occurrence! tv ty2 exp)
               (tvar-set-contents! tv ty2))))))
      ((tvar-type? ty2) (unify! ty2 ty1 exp))
      ((and (atomic-type? ty1) (atomic-type? ty2))
       (if (not
             (eqv?
               (atomic-type->name ty1)
               (atomic-type->name ty2)))
         (raise-type-error ty1 ty2 exp)))
      ((and (g/proc-type? ty1) (g/proc-type? ty2))
       (let ((arg-types1 (proc-type->arg-types ty1))
             (arg-types2 (proc-type->arg-types ty2))
             (result-type1 (proc-type->result-type ty1))
             (result-type2 (proc-type->result-type ty2)))
         (if (not
               (= (length arg-types1) (length arg-types2)))
           (raise-wrong-number-of-arguments ty1 ty2 exp)
           (begin
             (for-each
               (lambda (ty1 ty2)
                 (unify! ty1 ty2 exp))
               arg-types1 arg-types2)
             (unify!
               result-type1 result-type2 exp)))))
      ((and (pair-type? ty1) (pair-type? ty2))
       (begin
         (unify! (pair-type-fst ty1) (pair-type-fst ty2) exp)
         (unify! (pair-type-snd ty1) (pair-type-snd ty2) exp)))
      (else (raise-type-error ty1 ty2 exp)))))

; either returns #t or fails
(define check-no-occurrence!
  (lambda (tv ty exp)
    (let loop ((ty1 ty))                ; use a different name so ty
                                        ; is available for error reporting
      (cases type ty1
        (atomic-type (name) #t) 
        (proc-type (arg-types result-type poly)
          (begin
            (for-each loop arg-types)
            (loop result-type)))
        (gproc-type (arg-types result-type)
          (begin
            (for-each loop arg-types)
            (loop result-type)))
        (pair-type (fst snd) (begin (loop fst) (loop snd)))
        (tvar-type (tv2)
          (let ((tv2-contents (tvar->contents tv2)))
            (cond
              (tv2-contents
                ;; tv2 was bound, so search in its expansion
                (loop tv2-contents))
              ((eqv? tv tv2)
               ;; tv2 is unbound.  Was it the same as tv1?
               ;; yes: time to complain
               (raise-occurrence-check (tvar->serial-number tv) ty exp))
              (else
                ;; no, it's different, so it's OK
                #t))))))))

(define raise-type-error
  (lambda (t1 t2 exp)
    (eopl:error 'check-equal-type!
      "Type mismatch: ~s doesn't match ~s in ~s~%"
      (type-to-external-form t1)
      (type-to-external-form t2)
      exp)))

(define raise-wrong-number-of-arguments
  (lambda (t1 t2 exp)
    (eopl:error 'check-equal-type!
      "Different numbers of arguments ~s and ~s in ~s~%"
      (type-to-external-form t1)
      (type-to-external-form t2)
      exp)))

(define raise-occurrence-check
  (lambda (tvnum t2 exp)
    (eopl:error 'check-equal-type!
      "Can't unify: tvar~s occurs in type ~s in expression ~s~%" 
      tvnum
      (type-to-external-form t2)
      exp)))

;;; types of primitives

(define int-type (atomic-type 'int))
(define bool-type (atomic-type 'bool))

(define binop-type (proc-type (list int-type int-type) int-type #f))
(define unop-type  (proc-type (list int-type) int-type #f))
(define int->bool-type (proc-type (list int-type) bool-type #f))

(define type-of-primitive
  (lambda (prim)
    (cases primitive prim
      (add-prim  ()     binop-type)
      (subtract-prim () binop-type)
      (mult-prim  ()    binop-type)
      (incr-prim  ()    unop-type)
      (decr-prim  ()    unop-type)
      (zero-test-prim () int->bool-type))))


;;;;;;;;;;;;;;;; type environments ;;;;;;;;;;;;;;;;
    
(define-datatype type-environment type-environment?
  (empty-tenv-record)
  (extended-tenv-record
    (syms (list-of symbol?))
    (vals (list-of type-scheme?))
    (tenv type-environment?))
  (typedef-record      ;\new4
    (name symbol?)
    (definition type?)
    (tenv type-environment?)))

(define empty-tenv empty-tenv-record)

;; for ordinary bindings, need to turn ordinary types into type schemes with no
;; bound variables -- all occurrences will have the same type.

(define extend-tenv                     
  (lambda (syms types tenv)
    (extended-tenv-record
      syms
      (map (lambda (t) (a-type-scheme '() t)) types)
      tenv)))

;; for polymorphic binding, need to turn ordinary types into type
;; schemes in which all tvars not already bound in the environment
;; become bound here.

(define extend-tenv-with-type-schemes
  (lambda (syms types tenv)
    (let ((free-tvars-in-tenv (free-tvars-in-tenv tenv)))
      (extended-tenv-record
        syms
        (map
          (lambda (t) (if (and (proc-type? t) (proc-type->poly t))
                          (make-type-scheme t free-tvars-in-tenv)
                          (a-type-scheme '() t)))
          types)
        tenv))))

(define make-type-scheme
  (lambda (ty tenv-tvars)
    (let ((ty-tvars (free-tvars ty)))
      (a-type-scheme
        (difference ty-tvars tenv-tvars)
        ty))))

(define extend-tenv-with-typedef typedef-record) 

;; apply-tenv instantiates each type scheme that it finds.

(define apply-tenv 
  (lambda (tenv sym)
    (let apply-tenv ((tenv tenv) (sym sym))
      (cases type-environment tenv
        (empty-tenv-record ()
          (eopl:error 'apply-tenv
            "Variable ~s unbound in type environment" sym))
        (extended-tenv-record (syms vals tenv)
          (let ((pos (list-find-position sym syms)))
            (if (number? pos)
              (instantiate-type-scheme (list-ref vals pos))
              (apply-tenv tenv sym))))
        (typedef-record (name type tenv)
          (apply-tenv tenv sym))))))

(define apply-tenv-typedef                    
  (lambda (tenv0 sym)
    (let loop ((tenv tenv0))
      (cases type-environment tenv
        (empty-tenv-record ()
          (eopl:error 'apply-tenv
            "Type variable ~s unbound in type environment ~s"
            sym tenv0))
        (extended-tenv-record (syms vals tenv) (loop tenv))
        (typedef-record (name type tenv) 
          (if (eqv? name sym) type (loop tenv)))))))

(define free-tvars-in-tenv
  (lambda (tenv)
    (cases type-environment tenv
      (empty-tenv-record () '())
      (extended-tenv-record (syms tss tenv)
        (union
          (bigunion
            (map 
              (lambda (ts)
                (cases type-scheme ts
                  (a-type-scheme (local-tvars ty)
                    (difference
                      (free-tvars ty)
                      local-tvars))))
              tss))
          (free-tvars-in-tenv tenv)))
      (typedef-record (name type tenv)
        (free-tvars-in-tenv tenv)))))

;;;;;;;;;;;;;;;; external form of types ;;;;;;;;;;;;;;;;

(define type-to-external-form
  (lambda (ty)
    (cases type ty
      (atomic-type (name) name)
      (proc-type (arg-types result-type poly)
        (append
          (arg-types-to-external-form arg-types)
          '(->)
          (list (type-to-external-form result-type))))
      (gproc-type (arg-types result-type)
        (append
          (arg-types-to-external-form arg-types)
          '(->)
          (list (type-to-external-form result-type))))
      (pair-type (fst snd)
                 (list 'pair (type-to-external-form fst) (type-to-external-form snd)))
      (tvar-type (tv)
        (tvar-select-contents tv
          type-to-external-form
          (lambda ()
            (string->symbol
              (string-append
                "tvar"
                (number->string (tvar->serial-number tv))))))))))

(define arg-types-to-external-form
  (lambda (types)
    (if (null? types)
      '()
      (if (null? (cdr types))
        (list (type-to-external-form (car types)))
        (cons
          (type-to-external-form (car types))
          (cons '*
                (arg-types-to-external-form (cdr types))))))))


