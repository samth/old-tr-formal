(module svn mzscheme
  (require (lib "foreign.ss"))
  
  (unsafe!)
  
  (define libapr (ffi-lib "libapr-0"))
  (define libsvn (ffi-lib "libsvn_client-1"))
  
  (default-_string-type _string/utf-8)
  
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
  
  
  (define-syntax define-cpointer-types
    (syntax-rules ()
      [(_ nms ...)
       (begin (define-cpointer-type nms) ...)]))
  
  (defapr apr-initialize  (_fun -> _apr_status_t))
  
  (define-cpointer-type _apr_array_header)
  (define-cpointer-types _pool _allocator _svn_error)
  (define _revnum _long)
  (define-cpointer-types 
    _svn_stringbuf _svn_auth_baton _svn_wc_notify_func _apr_hash _svn_cancel_func)
  
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

  (define-cstruct _svn_client_proplist_item
    ((node-name _svn_stringbuf)
     (prop-hash _apr_hash)))

  (define-cstruct _svn_client_commit_info
    (;(revison _revnum)
     (date _string)
     (author _string)))

  (define SVN_CLIENT_COMMIT_ITEM_ADD         #x01)
  (define SVN_CLIENT_COMMIT_ITEM_DELETE      #x02)
  (define SVN_CLIENT_COMMIT_ITEM_TEXT_MODS   #x04)
  (define SVN_CLIENT_COMMIT_ITEM_PROP_MODS   #x08)
  (define SVN_CLIENT_COMMIT_ITEM_IS_COPY     #x10)

  
  (define-cstruct _svn_opt_revision 
                  ((kind _revision_kind)
                   (value _int64)))
  
  (define _apr_byte _uint8)
  
  (define-cpointer-type _svn_node_kind)
  
  (define _svn_client_get_commit_log
    (_fun (_ptr o _string) (_ptr o _string) _apr_array_header _pointer _pool -> _svn_error))
  
  (define _svn_client_blame_reciever
    (_fun _pointer _int64 _revnum _string _string _string _pool -> _svn_error))
  
  (define-cstruct _svn_client_commit_item
                  ((path _string)
                   (kind _svn_node_kind)
                   (url _string)
                   (revision _revnum)
                   (copyfrom-url _string)
                   (state-flags _apr_byte)
                   (wcprop-changes _apr_array_header)))
  
  (define-cstruct _svn_client_ctx
                  ((auth-baton _svn_auth_baton)
                   (notify-func _svn_wc_notify_func)
                   (notify-baton _pointer)
                   (log-msg-func _svn_client_get_commit_log)
                   (log-msg-baton _pointer)
                   (config _apr_hash)
                   (cancel_func _svn_cancel_func)
                   (cancel_baton _pointer)))
  
  (defsvn checkout 
          (_fun
           (_revnum = 0)
           (URL : _string)
           (path : _string)
           (revision : _svn_opt_revision-pointer)
           (recurse : _bool)
           (ctxt : _svn_client_ctx-pointer)
           (pool : _pool)
           ->
           _svn_error))
          
  
  
  
  (defsvn create-pool "svn_pool_create_ex" 
          (_fun _pool/null (_allocator/null = #f) -> _pool))
  
  (define (new-pool) (create-pool #f))
  
  (defapr clear-pool "apr_pool_clear" (_fun _pool -> _void))
  (defapr destroy-pool "apr_pool_destroy" (_fun _pool -> _void))
  
  (defsvn create-context
          (_fun (cxt : (_ptr o _svn_client_ctx)) _pool -> (ret : _svn_error/null) -> (or ret cxt)))
  
  (defsvn cleanup 
          (_fun _string _svn_client_ctx _pool -> _svn_error))
  
  (defsvn update 
          (_fun (_ptr o _revnum) 
                _string 
                _svn_opt_revision-pointer 
                (_bool = #t)
                _svn_client_ctx-pointer 
                _pool 
                -> _svn_error))

  (defsvn switch
    (_fun (_ptr o _revnum) 
          _string
          _string
          _svn_opt_revision-pointer 
          _bool
          _svn_client_ctx-pointer 
          _pool 
          -> _svn_error))

  (defsvn add (_fun _string _bool _svn_client_ctx-pointer _pool -> _svn_error))

  (defapr apr-array-make (_fun _pool _int _int -> _apr_array_header))
  
  (defsvn auth-open "svn_auth_open" (_fun (bat : (_ptr o _svn_auth_baton)) _apr_array_header _pool -> _void -> bat ))
  
  (defsvn mkdir 
          (_fun (commit-info : (_ptr o _svn_client_commit_info-pointer))
                (paths : _apr_array_header )
                (ctx : _svn_client_ctx-pointer)
                _pool
                -> _svn_error))
  
  (defsvn delete           
          (_fun (commit-info : (_ptr o _svn_client_commit_info-pointer))
                (paths : _apr_array_header )
                (force : _bool)
                (ctx : _svn_client_ctx-pointer)
                _pool
                -> _svn_error))

  (defsvn import           
          (_fun (commit-info : (_ptr o _svn_client_commit_info-pointer))
                (path : _string)
                (url : _string)
                (nonrecursive : _bool)
                (ctx : _svn_client_ctx-pointer)
                _pool
                -> _svn_error))
  
   (defsvn commit           
          (_fun (commit-info : (_ptr o _svn_client_commit_info-pointer))
                (targets : _apr_array_header)
                (nonrecursive : _bool)
                (ctx : _svn_client_ctx-pointer)
                _pool
                -> _svn_error))
  
  (defsvn status
          (_fun (result_rev : _revnum)
                (path : _string)
                (revision : _svn_opt_revision)
                (status-baton : _pointer)
                (descend : _bool)
                (get-all : _bool)
                (update : _bool)
                (no-ignore : _bool)
                _svn_client_ctx
                _pool
                -> _svn_error
                ))
  

  
  (apr-initialize)
  (define pool (new-pool))
  (define c (create-context pool))
  (define rev (make-svn_opt_revision 'revision_head 1))
  
  (define arr (apr-array-make pool 0 0))
  (define bat (auth-open arr pool))
  (set-svn_client_ctx-auth-baton! c bat)
  (define (test)
    (begin
      (checkout  "http://svn.collab.net/repos/svn/trunk/ac-helpers" "foo" rev 1 c pool)
      (update "foo" rev c pool)))
  (provide (all-defined))

  )
