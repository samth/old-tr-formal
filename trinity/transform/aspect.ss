(module aspect mzscheme

  ;; ? ? ?
  (define-struct aspect (when where action))

  (provide/contract (struct aspect ((when any?)
                                    (where any?)
                                    (action any?)))))

