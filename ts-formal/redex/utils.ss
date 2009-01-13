#lang scheme/base

(require (for-syntax scheme/base) redex/reduction-semantics)
(provide (all-defined-out))

(define-syntax-rule (no-fail . e)
  (with-handlers ([exn:fail? (lambda _ #f)])
    . e))

(define-syntax term-let*
  (syntax-rules ()
    [(term-let* () . e) (term-let () . e)]
    [(term-let* (cl . rest) . e) (term-let (cl) (term-let* rest . e))]))

(define-syntax (match/redex stx)
  (syntax-case stx ()
    [(_ lang e clauses ...)
     (quasisyntax/loc stx
       (let ([r (term e)])
         ((term-match/single 
           lang
           clauses ... 
           [any #,(syntax/loc stx (error 'match/redex "no match for term ~a" r))])
          r)))]))

(define-syntax (*term-let-one stx)
  (syntax-case stx ()
    [(_ lang ([pat rhs]) . body)
     (quasisyntax/loc stx
       (let ([r rhs])
         ((term-match/single
           lang
           [pat (begin . body)]
           [any #,(syntax/loc stx (error 'term-let "term ~a did not match pattern ~a" r 'pat))])
          r)))]))

(define-syntax *term-let
  (syntax-rules ()
    [(*term-let lang () . e) (term-let () . e)]
    [(*term-let lang (cl . rest) . e) (*term-let-one lang (cl) (*term-let lang rest . e))]))

