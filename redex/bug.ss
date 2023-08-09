#lang scheme/base

;; bug here is infinite loop

(require redex)

(define-language lang)

(define p (make-parameter #t))

(define-metafunction lang
  m : any -> any
  [(m any_1) ,(parameterize ([p #f]) (term (m any_1)))
             (side-condition (p))]
  [(m any_2) #f])

(term (m 1))
