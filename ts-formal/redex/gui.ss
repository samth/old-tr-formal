#lang scheme

(require redex "opsem.ss" "types.ss" "utils.ss" "examples.ss" "tests.ss" mzlib/trace)

(reduction-steps-cutoff 150)

(define (check/plain e)
  (no-fail
   (parameterize ([T-Bot #f]
                  [T-Not #f]
                  [enable-T-IfAnd #f]
                  [enable-T-IfOr #f]
                  [enable-ProofTheoretic #f])
     (tc-fun e))))

;; turn on the middle rules, but not the experimental ones
(define (check/middle e)
  (no-fail 
   (parameterize ([T-Not #f]
                  [enable-T-IfAnd #f]
                  [enable-T-IfOr #f])
     (tc-fun e))))

;; turn everything on
(define (check/experimental e)
  (no-fail (tc-fun e)))

;(current-traced-metafunctions '(check-sub subset-f))

(define (check e node)
  (define parents (term-node-parents node))
  (define children (term-node-children node))
  (define val? (value? e))
  (define parent-exprs (map term-node-expr parents))
  
  ;; check type preservation
  (let* ([parent-types (no-fail (map tc-fun parent-exprs))]
         [cur-type (check/experimental e)]
         [mid-type (check/middle e)]
         [plain-type (check/plain e)]
         [preserve? (if parent-types
                        (*term-let occur-lang ([(any_pt ...) parent-types])
                          (printf "~a parent-types: ~a~n" e parent-types)
                          (term (all (check-sub any_pt (,cur-type)) ...)))
                        #t)])
    (cond      
      ;; this term didn't typecheck, but the parent did, which is bad
      [(and (not cur-type) parent-types (not (null? parent-types))) "red"]
      ;; both typechecked, but with wrong types
      [(not preserve?) (printf "e:~a\npe:~a\npt: ~a\nct:~a\n" e parent-exprs parent-types cur-type) "orange"]
      ;; if it checks and doesn't reduce, but isn't a value
      [(and (not val?)
            (null? children)
            cur-type)
       "blue"]
      ;; if it checks with no additions, then it's fine
      [plain-type #t]
      ;; if we have to use the iftrue/false rules in the middle, that's ok
      [(and (not (null? parents)) mid-type) "yellow"]
      ;; experimental rules get their own color
      [cur-type "green"]
      ;; if we use them elsewhere, that's bad
      [mid-type "MediumPurple"]
      ;; otherwise it didn't check at all, nor did the parents
      [(and (or (null? parent-types) (not parent-types)) (not cur-type)) #f]
      ;; should never happen
      [else (error 'check* "fell off the end: ~a ~a ~a" e parent-types cur-type)])))

;(trace check)

(define (tr . t) (traces reductions t #:multiple? #t #:pred check))

