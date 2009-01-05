#lang scheme/base

(require (for-syntax scheme/base) redex)
(provide (all-defined-out))

(define-syntax term-let*
  (syntax-rules ()
    [(term-let* () . e) (term-let () . e)]
    [(term-let* (cl . rest) . e) (term-let (cl) (term-let* rest . e))]))

(define-syntax (*term-let-one stx)
  (syntax-case stx ()
    [(_ lang ([pat rhs]) . body)
     (with-syntax ([(mf-name) (generate-temporaries (list 'mf))])
       (quasisyntax/loc stx
         (let ([r rhs])
           ((term-match/single
             lang
             [pat (begin . body)]
             [any #,(syntax/loc stx (error 'term-let "term ~a did not match pattern ~a" r 'pat))])
            r))))]))

(define-syntax *term-let
  (syntax-rules ()
    [(*term-let lang () . e) (term-let () . e)]
    [(*term-let lang (cl . rest) . e) (*term-let-one lang (cl) (*term-let lang rest . e))]))