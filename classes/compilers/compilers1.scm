; Implementation of QType and TEnv abstract datatypes.

; Sam Tobin-Hochstadt
; 9/16/04

(load "/course/csg262/Assignments/Assignment1/qsymbol.sch")
; var : T -> Qtype

(define (var t) (list 'var t))

; type : T -> Qtype

(define (type t) (list 'type t))

; isVar? : Qtype -> boolean

(define (isVar? t) (eq? 'var (car t)))

; isType? : Qtype -> boolean

(define (isType? t) (eq? 'type (car t)))

; untagged : Qtype -> T

(define untagged cadr)

; empty : -> Tenv

(define empty (lambda () '()))

; extend : Tenv Qsymbol Qtype -> Tenv

(define (extend env sym t)
  (cons (list sym t) env))

; lookup : Tenv Qsymbol -> Qtype

(define (lookup env i)
  (cond 
    ((empty? env) (type VOID))
    ((Qsymbol.equals i (caar env)) => cadar)
    (else (lookup (cdr env) i))))

