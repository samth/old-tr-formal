(module memoize mzscheme

  (define-syntax memo-lambda
    (syntax-rules ()
      [(_ (arg) body ...)
       (let ([memo (make-hash-table)]
             [f (lambda (arg) body ...)])
         (lambda (arg)
           (hash-table-get memo arg (lambda ()
                                      (let ([ans (f arg)])
                                        (hash-table-put! memo arg ans)
                                        ans)))))]))

  (define-syntax memo-lambda*
    (syntax-rules ()
      [(_ (arg ...) body ...)
       (let ([memo (make-hash-table)]
             [f (lambda (arg ...) body ...)])
         (lambda (arg ...)
           (let* ([args (list arg ...)]
                  [key (bitwise-xor (eq-hash-code arg) ...)]
                  [alist (hash-table-get memo key (lambda () null))])
             (cond
               [(assoc args alist) => cdr]
               [else (let ([ans (f arg ...)])
                       (hash-table-put! memo key (cons (cons args ans) alist))
                       ans)]))))]))


  (provide memo-lambda memo-lambda*))
