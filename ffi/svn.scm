;(module svn mzscheme
  (require (lib "foreign.ss"))
  (define libapr (ffi-lib "libapr-0"))
  (define libsvn (ffi-lib "libsvn_client-1"))
  
  (define-values 
    (_apr_byte_t _apr_int_16_t _apr_uint_16_t _apr_status_t)
    (values _byte _int16 _uint16 _int))

(define-syntax defsvn
  (syntax-rules ()
    [(_ nm fun ty)
     (define nm
       (get-ffi-obj fun libsvn ty))]))

(define-syntax defapr
  (syntax-rules ()
    [(_ nm fun ty)
     (define nm
       (get-ffi-obj fun libapr ty))]))

(defapr apr-initialize "apr_initialize" (_fun -> _apr_status_t))
  
  (define-cpointer-type _pool _pointer)
  ;(define _pool (make-ctype _pointer #f #f))
  (define _allocator (make-ctype _pointer #f #f))
  (define _svn_error (make-ctype _pointer #f #f))
  (define _revnum _long)
  (define _client_cxt (make-ctype _pointer #f #f))

(define _revnum _long)
  
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
    "svn_client_checkout"
    (_fun (_revnum = 0)
          (URL : _string)
          (path : _string)
          (revision : _svn_opt_revision_t-pointer)
          (recurse : _bool)
          (ctxt : _client_cxt)
          (pool : _pool)
          ->
          _svn_error)
    )
    
    
  
  (defsvn create-pool "svn_pool_create_ex" 
    (_fun _pool/null (_allocator = #f) -> _pool))
  
  (define (new-pool) (create-pool #f))
  
  (defapr clear-pool "apr_pool_clear" (_fun _pool -> _void))
  (defapr destroy-pool "apr_pool_destroy" (_fun _pool -> _void))
  
  (defsvn create-client-context
    "svn_client_create_context"
    (_fun (cxt : (_ptr o _client_cxt)) _pool -> (ret : _svn_error) -> (or ret cxt)))

(defsvn cleanup "svn_client_cleanup"
  (_fun _string _client_cxt _pool -> _svn_error))

(defsvn update "svn_client_update"
  (_fun (_ptr o _revnum) _string _svn_opt_revision_t-pointer/null (_bool = #t) _client_cxt/null _pool -> _svn_error))

(apr-initialize)
(define pool (new-pool))
(define c (create-client-context pool))
(define rev (make-svn_opt_revision_t 'revision_head 1))
 
;  (provide (all-defined))
  
  
; )
