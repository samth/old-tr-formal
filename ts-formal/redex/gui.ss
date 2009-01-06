#lang scheme

(require redex "opsem.ss" "utils.ss" "examples.ss")

(define (tc-fun e)
  (term (tc () ,e)))

(define (check e node)
  (let* ([parents (term-node-parents node)]
         [parent-exprs (map term-node-expr parents)])
    (with-handlers ([exn:fail? (lambda _ #f)])
      (*term-let occur-lang
                 ([((t f s) ...) 
                   ;; if the parents don't typecheck, just ignore them
                   (with-handlers ([exn:fail? (lambda _ '())])
                     (map tc-fun parent-exprs))]
                  [(t_1 f_1 s_1) (term (tc () ,e))])
        (term (all (all (t_1 . <: . t) ...)
                   #; #;
                   (all (subeff f_1 f) ...)
                   (all (subsubj s_1 s) ...)))))))

(define (tcx e)
  (parameterize ([enable-T-IfAnd #f]
                 [enable-T-IfOr #t]
                 [enable-T-AbsPred #t]
                 [enable-T-IfVar #t])
    (tc-fun e)))

(define (check* e node)
  (define parents (term-node-parents node))
  (define children (term-node-children node))
  (define val? (value? e))
  (define parent-exprs (map term-node-expr parents))
  (define (check/plain e)
    (with-handlers ([exn:fail? (lambda _ #f)])
      (parameterize ([enable-T-IfTrue #f]
                     [enable-T-IfFalse #f])
        (tc-fun e))))
  (define (check/middle e)
    (with-handlers ([exn:fail? (lambda _ #f)])
      (tc-fun e)))
  (define (check/experimental e)
    (with-handlers ([exn:fail? (lambda _ #f)])
      (tcx e)))
  ;; check type preservation
  (*term-let occur-lang
    ([(e_p ...) parent-exprs]
     [((t_p f_p s_p) ...)
      (with-handlers ([exn:fail? (lambda _ '())])
        (term ((tc e_p) ...)))]
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

(define (r t) (apply-reduction-relation reductions t))
(define (r* t) (apply-reduction-relation* reductions t))

(define (tr t) (traces reductions t #:pred check))

(define (tr2 t) (traces reductions t))


(define (tr* . t) (traces reductions t #:multiple? #t #:pred check*))

(define (trx t)
  (parameterize ([enable-T-IfAnd #t] ;; this rule is unsound
                 [enable-T-IfOr #t]
                 [enable-T-AbsPred #t])
    (tr t)))

(reduction-steps-cutoff 150)

(print-struct #t)