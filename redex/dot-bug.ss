#lang scheme/base

(require redex)

(define-language occur-lang)

(define-metafunction occur-lang
  U : any ... -> any)

(define-metafunction occur-lang
  env+ : (any ...) -> any  
  [(env+ (any_1 ...)) ((any_1 (U)) ...)])


