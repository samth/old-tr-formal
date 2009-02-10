#lang scheme

(require redex)

(define-language occur-lang

  ;; types
  [(t u) N proctop top #t #f (t ..._a -> t : fh ..._a : sh) (pr t t) (union t ...)]
  ;; filters
  [fh ((ph ...) (ph ...))]
  
  [ph (t pi) (! t pi) both]
  
  [sh 0 (pi number)]
  
  ;; paths
  [pi (pe ...)]
  [pe car cdr]
  
  )

(define type? (redex-match occur-lang t))

(redex-check occur-lang t (type? (term t)) #:attempts 10000)


