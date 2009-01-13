#lang scheme

(require redex "opsem.ss" "types.ss" "utils.ss" "examples.ss" "tests.ss" mzlib/trace)

(reduction-steps-cutoff 150)

(define (check e node)  
  (sub? e (map term-node-expr (term-node-parents node))))

(define (tcx e)
  (parameterize ([enable-T-IfAnd #t]
                 [enable-T-IfOr #t]
                 [enable-T-AbsPred #t])
    (tc-fun e)))


(define (check/plain e)
  (no-fail
    (parameterize ([T-Bot #f]
                   [enable-T-IfAnd #f]
                   [enable-T-IfOr #f])
      (tc-fun e))))

(define (check/middle e)
  (no-fail
    (parameterize ([enable-T-IfAnd #f]
                   [enable-T-IfOr #f])
    (tc-fun e))))

(define (check/experimental e)
  (no-fail (tcx e)))

(define (check* e node)
  (define parents (term-node-parents node))
  (define children (term-node-children node))
  (define val? (value? e))
  (define parent-exprs (map term-node-expr parents))
  
  ;; check type preservation
  (*term-let occur-lang
    ([(e_p ...) parent-exprs]
     [((t_p f_p s_p) ...)
      (with-handlers ([exn:fail? (lambda _ '())])
        (term ((tc () e_p) ...)))]
     [any_ct (check/experimental e)]
     [boolean_preserve?
      (if (term any_ct)
          (*term-let occur-lang
            ([(t_c f_c s_c) (term any_ct)])
            (term (all (t_c . <: . t_p) ...)))
          #t)])
    (let ([preserve? (term boolean_preserve?)]
          [cur-type (term any_ct)]
          [parent-types (term (t_p ...))])
      (cond
        [(not preserve?) "purple"]
        ;; if it checks and doesn't reduce, but isn't a value
        [(and (not val?)
              (or (check/plain e)
                  (check/middle e)
                  (check/experimental e))
              (null? children))
         "blue"]
        ;; if it checks with no additions, then it's fine
        [(check/plain e) #t]
        ;; if we have to use the iftrue/false rules in the middle, that's ok
        [(and (not (null? parents)) (check/middle e)) "yellow"]
        ;; if we use them elsewhere, that's bad
        [(check/middle e) "MediumPurple"]
        ;; experimental rules get their own color
        [(check/experimental e) "green"]
        ;; this term didn't typecheck, but the parent did, which is bad
        [(and (not cur-type) (not (null? parent-types))) "red"]
        ;; otherwise it didn't check at all, nor did the parents
        [else #f]))))

(define (tr t) (traces reductions t #:pred check))

(define (tr2 t) (traces reductions t))

(define (tr* . t) (traces reductions t #:multiple? #t #:pred check*))

(define (trx t)
  (parameterize ([enable-T-IfAnd #t]
                 [enable-T-IfOr #t]
                 [enable-T-AbsPred #t])
    (tr t)))

