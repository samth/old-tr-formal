(module etc mzscheme
  (require (lib "etc.ss"))
  (require (lib "list.ss"))
  (require (lib "match.ss"))
  (require (lib "string.ss"))
  (provide compose)
  (provide let1 lambda-typed define-typed define-traced 
           full-cond full-case full-match let*/match)
  (provide if-not for-each-from id)
  (provide symbol-prefix?)
  (provide assert)
  (provide define-procedural-struct)
  (provide append-format)
  (provide unmatch)
  (provide apropos)

  ;; - (define-procedural-struct (<proc-struct> <super>) <proc>) 
  ;; will define an extension of <super> named <proc-struct>, which when
  ;; used as a procedure, will apply <proc> to itself and whatever
  ;; arguments were passed to the original invocation.
  (define-syntax define-procedural-struct
    (lambda (stx)
      (syntax-case stx ()
        [(define-procedural-struct (PROC-STRUCT MAIN-STRUCT) PROC)
         (let* ((++ (lambda sym (string->symbol (apply string-append (map symbol->string sym)))))
                (so (lambda (sym) (datum->syntax-object #'define-procedural-struct sym)))
                (maker (so (++ 'make- (syntax-object->datum #'PROC-STRUCT))))
                (pred  (so (++ (syntax-object->datum #'PROC-STRUCT) '?)))
                (super (so (++ 'struct: (syntax-object->datum #'MAIN-STRUCT)))))
           #`(define-values (#,maker #,pred)
               (let ()
                 (define-values (struct:anon make-anon anon? anon-ref anon-set!)
                   (make-struct-type (quote PROC-STRUCT) #,super 1 0 #f null #f 
                                     (lambda args
                                       (apply (anon-ref (car args) 0) args))))
                 (values (lambda l
                           (apply make-anon (append l (list PROC))))
                         anon?))))])))

  (define-syntax define-traced 
    (syntax-rules (lambda)
      [(define-traced (FUNC ARGS ...) BODY ...)
       (define (FUNC ARGS ...)
         (display `(FUNC ,@(list ARGS ...)))
         (newline)
         (let ()
           BODY ...))]
      [(define-traced FUNC (lambda ARGS BODY ...))
       (define FUNC 
         (lambda ARGS 
           (display `(FUNC ,@ARGS))
           (newline) 
           (let () 
             BODY ...)))]
      ))
  
  (define-syntax trace
    (syntax-rules ()
      [(trace OP ARGS ...)
       (let ((argl (list ARGS ...)))
         (display `(OP ,@argl)) 
         (newline)
         (apply OP argl))]))

  (define-syntax let1 
    (syntax-rules ()
      [(let1 (NAME EXP) BODY ...)
       (let ((NAME EXP)) BODY ...)]
      [(let1 PROC (NAME EXP) BODY ...)
       (let PROC ((NAME EXP)) BODY ...)]))
  
  (define for-each-from (lambda (l) (lambda (f) (for-each f l))))

  (define-syntax assert
    (syntax-rules ()
      [(assert EXP MESG CXT)
       (if (not EXP)
           (error CXT 
                  (let ((mesg-str (format "~a" MESG)))
                    (if (> (string-length mesg-str) 0)
                        (format "assertion failure on ~a : ~a" (quote EXP) mesg-str)
                        (format "assertion failure on ~a"      (quote EXP))))))]
      [(assert EXP MESG)
       (assert EXP MESG 'assert)]
      [(assert EXP)
       (assert EXP "")]))

  (define id (lambda (x) x))

  (define-syntax full-cond
    (syntax-rules ()
      [(full-cond CLAUSE ...)
       (cond CLAUSE ...
             [else 
              (error 'full-cond "no clause matched")])]))

  (define-syntax full-match
    (lambda (stx)
    (syntax-case stx ()

      ;; Putting in a special case for the the case of a catch-all so
      ;; that DrScheme doesn't print out warnings about unreachable
      ;; match clauses...
      [(full-match EXP [ID BODY ...]) (identifier? #'ID) #'(match EXP [ID BODY ...])]

      [(full-match EXP CLAUSE ...)
       #'(let ((e EXP))
           (match e
             CLAUSE ...
             [else (error 'full-match 
                          (format 
                           "no clause matched on ~a : ~a" 
                           (quote EXP) e))]))])))
    
  (define-syntax let*/match
    (syntax-rules ()
      [(let*/match () BODY ...)
       (begin BODY ...)]
      [(let*/match ((PAT EXP) REST ...) BODY ...)
       (full-match EXP
         [PAT (let*/match (REST ...) BODY ...)])]))

  (define-syntax full-case
    (syntax-rules ()
      [(full-case ARG CLAUSE ...)
       (let ((a ARG))
         (case a 
           CLAUSE 
           ...
           [else 
            (error 'full-case 
                   (format "no clause matched on ~a : ~a" (quote ARG) a))]))]))

  (define (if-not this that)
    (if this this that))
  
  ;; I should extend these to allow one to not provide a type
  ;; predicate (which is then equivalent to (lambda (x) #t), aka the
  ;; Any type.
  (define-syntax lambda-typed 
    (syntax-rules ()
      [(lambda-typed RET-TYP? ((ARG ARG-TYP?) ...) BODY ...)
       ((wrapped-lambda 'unknown-proc RET-TYP? ARG-TYP? ...)
        (lambda (ARG ...)
          BODY ...))]))

  (define-syntax define-typed
    (syntax-rules ()
      [(define-typed RET-TYP? (PROC-NAME (ARG ARG-TYP?) ...) BODY ...)
       (define PROC-NAME
         ((wrapped-lambda (quote PROC-NAME) RET-TYP? ARG-TYP? ...)
          (lambda (ARG ...)
            BODY ...)))]))

  (define (wrapped-lambda proc-sym ret-pred . arg-preds)
    (lambda (proc)
      (lambda l
        (cond [(not (andmap (lambda (x) x) (map apply arg-preds (map list l))))
               (error proc-sym "incorrect argument type")])
        (let ((val (apply proc l)))
          (cond [(not (ret-pred val))
                 (error proc-sym "incorrect return type")])
          val))))

  (define (symbol-prefix? pfx sym)
    (let ((pfx (symbol->string pfx)) 
          (sym (symbol->string sym)))
      (let ((sym-len (string-length sym)) 
            (pfx-len (string-length pfx)))
        (and (>= sym-len pfx-len)
             (equal? pfx (substring sym 0 pfx-len))))))


  (define append-format/buggy ;; an interesting exercise: what's the bug here:
    (lambda args
      (let loop ((fmt "")
                 (fmt-args '())
                 (args args))
        (cond [(null? args) (apply format (cons fmt (reverse fmt-args)))]
              [(string? (car args)) (loop (string-append fmt (car args))
                                          fmt-args
                                          (cdr args))]
              [else                 (loop (string-append fmt "~a")
                                          (cons (car args) fmt-args)
                                          (cdr args))]))))
  
  (define append-format
    (lambda args
      (apply format 
             (cons (apply 
                    string-append 
                    (build-list (length args) (lambda (x) "~a")))
                   args))))

  ;; Provides a way to easily [re]construct input to match patterns.
  ;; TODO: add support for quasiquotation.
  (define-syntax unmatch
    (syntax-rules (quote quasiquote ...)
      [(unmatch (quote A))      (quote A)]
      [(unmatch (quasiquote A)) (quasiquote A)]
      ;; (... ...) is esc.sequence for ... symbol
      [(unmatch ((A ...) (... ...)))  (map (lambda l l) . (A ...))]
      [(unmatch (A (... ...)))  (unmatch A)]
      [(unmatch (A B ...))      (cons (unmatch A) (unmatch (B ...)))]
      [(unmatch (A . REST))     (cons (unmatch A) (unmatch REST))]
      [(unmatch A)              A]))
  
  ;; This is actually "buggy", because it allows arbitrary characters
  ;; to be interspersed (between the elements of pat) in str and still
  ;; returns true.  So we're really not talking about a true substring
  ;; here.  What's a better name for this relationship?
  (define (substring-present? pat str) 
    (let ((s-l (string->list str))
          (p-l (string->list pat)))
      (let loop ((p-l p-l) (s-l s-l))
        (cond [(null? p-l) #t]
              [(member (car p-l) s-l) => (lambda (x) (loop (cdr p-l) x))]
              [else #f]))))
  
  (define (apropos sym)
    (let ((rx (regexp (regexp-quote (symbol->string sym) #t))))
      (filter
       (lambda (s)
         (regexp-match rx (symbol->string s)))
       (namespace-mapped-symbols (current-namespace)))))

)

