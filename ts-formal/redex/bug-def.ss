#lang scheme/base
(require redex)
(define-syntax-rule (id-mf mf lang)
  (define-metafunction lang
    mf : any -> any
    [(mf any_1) (term any_1)]))
(provide id-mf)
