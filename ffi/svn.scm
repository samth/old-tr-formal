(module svn mzscheme
  (require (lib "foreign.ss"))
  
  (unsafe!)
  
  (define libapr (ffi-lib "libapr-0"))
  (define libsvn (ffi-lib "libsvn_client-1"))
  
  
  
  (define-values 
    (_apr_byte_t _apr_int_16_t _apr_uint_16_t _apr_status_t)
    (values _byte _int16 _uint16 _int))
 
  
   (define-syntax defsvn
    (syntax-rules ()
      [(_ nm  ty)
       (define nm
         (get-ffi-obj (regexp-replaces (quote nm) '((#rx"-" "_") (#rx"^" "svn_client_")))  
                      libsvn ty))]
      [(defsvn nm sym ty)
       (define nm (get-ffi-obj sym libsvn ty))]))
   (define-syntax defapr
    (syntax-rules ()
      [(_ nm  ty)
       (define nm
         (get-ffi-obj (regexp-replaces (quote nm) '((#rx"-" "_")))  
                      libapr ty))]
      [(defsvn nm sym ty)
       (define nm (get-ffi-obj sym libapr ty))]))
  
  
  (defapr apr-initialize  (_fun -> _apr_status_t))
  
  (define-cpointer-type _pool _pointer)
  ;(define _pool (make-ctype _pointer #f #f))
  (define _allocator (make-ctype _pointer #f #f))
  (define _svn_error (make-ctype _pointer #f #f))
  (define _revnum _long)
  (define-cpointer-type _client_cxt)
  
  (define _revision_kind
    (_enum '(revision_unspecified
             revision_number
             revision_date
             revision_committed
             revision_previous
             revision_base
             revision_working
             revision_head
             )))
  
  (define-cstruct _svn_opt_revision_t 
                  ((kind _revision_kind)
                   (value _int64)))
  
  (defsvn checkout 
          (_fun
           (_revnum = 0)
           (URL : _string)
           (path : _string)
           (revision : _svn_opt_revision_t-pointer)
           (recurse : _bool)
           (ctxt : _client_cxt)
           (pool : _pool)
           ->
           _svn_error))
          
  
  
  
  (defsvn create-pool "svn_pool_create_ex" 
          (_fun _pool/null (_allocator = #f) -> _pool))
  
  (define (new-pool) (create-pool #f))
  
  (defapr clear-pool "apr_pool_clear" (_fun _pool -> _void))
  (defapr destroy-pool "apr_pool_destroy" (_fun _pool -> _void))
  
  (defsvn create-context
          (_fun (cxt : (_ptr o _client_cxt)) _pool -> (ret : _svn_error) -> (or ret cxt)))
  
  (defsvn cleanup 
          (_fun _string _client_cxt _pool -> _svn_error))
  
  (defsvn update 
          (_fun (_ptr o _revnum) 
                _string 
                _svn_opt_revision_t-pointer 
                (_bool = #t)
                _client_cxt/null 
                _pool 
                -> _svn_error))
  
  (apr-initialize)
  (define pool (new-pool))
  (define c (create-context pool))
  (define rev (make-svn_opt_revision_t 'revision_head 1))
  
  
  )
