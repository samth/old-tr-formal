(module dsjr mzscheme
  (require 
   (lib "unitsig.ss")
   (lib "servlet-sig.ss" "web-server")
   (lib "servlet.ss" "web-server")
   
   (lib "servlet-helpers.ss" "web-server")
   (lib "async-channel.ss")
   (lib "mred.ss" "mred")
   (lib "pconvert.ss" )
   ;(rename "my-draw.ss" image-file-name the-filename )
   )
  
  (provide interface-version timeout start)
  
  (define interface-version 'v1)
  
  (define timeout +inf.0)
  
  (define (debug x . y)
    (begin
      (printf "DEBUG ~v ~v ~n" x y)
      (if (null? y) y (car y))))
  
  (define my-ch-get async-channel-get)
  
  (define my-ch-put async-channel-put)
  
  (define my-ch-try-get async-channel-try-get)
  
  (define image-file-name "../foo.jpg")
  
  (define print-scheme-val
    (lambda (sval)
      (cond ((void? sval) "")
            ((equal? eval-lang "plt-mzscheme.ss") (format "~a " sval))
            (else (parameterize 
                      ((constructor-style-printing #t)
                       )
                      (format "~a " (print-convert sval))))
            )))
  
  ; result -> xexpr
  ; a result is a pair, the car of which is a bool, the cadr isa list of scheme values in reverse order, or an xexpr
  ; if the car is #t, return an xexpr consisting of all the values in the list 
  ; in a p
  ; if the car is #f, return the xexpr that is the cadr in italics
  (define (present-result result)
    (if (car result)
        `(p ,@(reverse (map print-scheme-val (cadr result))))
        `(p (i ,(cadr result)))))
  
  (define (present-expr-and-result expr result)
    `(div (p "> " ,expr)  ,(present-result result)))
  
  
  
  (define (present-interactions exprs results)
    (reverse (map present-expr-and-result exprs results)))
  
  
  (define user-custodian (make-custodian))
  
  (define un (make-namespace))
  (define eval-lang "htdp-beginner.ss")
  
  (define (make-lang-option lang current-lang)
    (if (string=? lang current-lang) (list 'option '([selected "selected"]) lang) (list 'option lang)))
  
  (define prompt "")
  
  
  (define output-ch (make-async-channel))
  
  (define (get-lang lang-str)
    `(lib ,lang-str "lang"))
  
  ; input-port -> void : reads more from IS, prints result to OUTPUT-PORT
  (define (eval-help is result)
    (let 
        ((r (read is))
         (xzy (debug "in eval-help")))
      (cond ((eof-object? r) (my-ch-put output-ch (list #t result)))
            (else (debug "recurse in eval-help" (eval-help is (cons (eval r) result)))))))
  
  (define mred-sym ((current-module-name-resolver) '(lib "mred.ss" "mred") #f #f))
  (define draw-sym ((current-module-name-resolver) "my-draw.ss" #f #f))
  
  ; evaluate: string string bool -> void 
  ; evals EXPR-STR in language LANG, making a new env if EXEC? is true, puts the result on output-ch
  (define (evaluate expr-str lang exec?)
    (letrec 
        ((old-namespace (current-namespace))
         (new-namespace (if exec? (debug "foobar" (make-namespace 'empty)) un))
         )
      (queue-callback
       (lambda ()
         (parameterize 
             ((current-custodian user-custodian)
              (current-namespace new-namespace))
           (if exec? 
               (begin
                 (namespace-attach-module old-namespace 'mzscheme)
                 (namespace-attach-module old-namespace mred-sym)
;                 (namespace-attach-module old-namespace draw-sym)
                 (namespace-require "my-draw.ss")
                 (namespace-require (get-lang lang))
                 ))
           ;               (with-handlers 
           ;                   ((exn?
           ;                     (lambda (exn) (my-ch-put output-ch (list #f (exn-message exn))))))
           ;(debug "calling" "eval-help")
           (parameterize 
               ((current-exception-handler (lambda (exn)
                                             (begin
                                               (debug "in exception handler")
                                               (my-ch-put output-ch (list #f (exn-message exn)))
                                               (error-escape-handler)))))
             (debug "eval-help" (eval-help (open-input-string expr-str) '()))
             )
           (set! un (current-namespace))
           ;(channel-get sync-ch)
           )
         
         ))))
  
  
  
  ; string->list : evaluates EXPR-STR in LANG language, returns result as list of results
  (define (eval-thread expr-str lang exec?)
    ;        (letrec 
    ;            ((s (open-output-string))
    ;             (tid (evaluate expr-str s lang exec?))
    ;             (killer-tid (thread 
    ;                          (lambda ()
    ;                            (sleep 10)
    ;                            (kill-thread tid)))))
    ;          
    ;          (object-wait-multiple 
    ;           #f
    ;           (thread-dead-waitable tid))
    (begin
      (evaluate expr-str lang exec?)
      
      )
    ) 
  
  (define (eval-eventspace expr lang exec? eventspace)
    (parameterize ((current-eventspace eventspace))
      (begin
        (debug "the current thread" (current-thread))
        (evaluate expr lang exec?)
        (begin
          (debug "waiting on get")
          ;(sleep/yield 1)
          ;(debug "still waiting on get")
          (my-ch-get output-ch)
          )
        )))
  
  ; get-web-results: string string string string string string string -> list of values to pass to run-program
  (define (get-web-results eval-lang defs-contents defs-result old-exprs old-results) 
    ; continuation-url -> ??? : displays HTML page, waits for continuation
    (define (html-gen k-url) 
      `(html (head (title "Dr. Scheme Jr."))
             (body (form ([action ,k-url] [method "post"])
                         (table
                          (tr (td
                               (input ([type "submit"] [name "exec"] [value "Execute"])))
                              (td ,eval-lang)
                              (td ([rowspan "99"]) (img ([src ,image-file-name]))))
                          (tr (td
                               (textarea ([name "defs"] [rows "10"] [cols "64"]) 
                                         ,defs-contents)))
                          (tr (td ,(present-result defs-result)))
                          (tr (td ,@(present-interactions old-exprs old-results)))
                          (tr (td ">"))
                          (tr (td (textarea ([name "prompt"] [rows "10"] [cols "64"])
                                            ,prompt)))
                          (tr (td (input ([type "submit"] [name "eval"] [value "Evaluate"]))))
                          (tr (td (select ([name "lang"]) 
                                          ,(make-lang-option "htdp-beginner.ss" eval-lang)
                                          ,(make-lang-option "plt-mzscheme.ss" eval-lang)
                                          ,(make-lang-option "htdp-intermediate.ss" eval-lang)
                                          ,(make-lang-option "htdp-advanced.ss" eval-lang)
                                          ))))
                         ))))
    (letrec 
        ((bindings (request-bindings (send/suspend html-gen)))
         (exec (null? (extract-bindings 'eval bindings)))
         (defs (extract-binding/single 'defs bindings))
         (expr (extract-binding/single 'prompt bindings))
         (lang (extract-binding/single 'lang bindings))
         (empty (string=? "" expr))) 
      (list exec defs expr lang empty)
      ))
  
  (define (get-local-results l)
    (let* ((exec  (car l))
           (defs  (if exec (cadr l) ""))
           (expr (if exec "" (cadr l)))
           (lang "plt-mzscheme.ss")
           (empty #f))
      (list exec defs expr lang empty)))
  
  
  (define (web-main-loop defs-contents defs-result old-exprs old-results last-eventspace) 
    (define (run-program exec defs expr lang empty)
      (cond 
        [exec (set! eval-lang lang) 
              (let* ((new-eventspace (make-eventspace))
                     (eval-result (debug "eval-eventspace 1" (eval-eventspace defs lang #t new-eventspace)))
                     )  
                (web-main-loop defs eval-result '() '() new-eventspace))]
        [empty (web-main-loop defs "" old-exprs old-results last-eventspace)]
        [else (let* ((eval-result (debug "eval-eventspace 2" (eval-eventspace expr eval-lang #f last-eventspace)))
                     )
                (web-main-loop defs defs-result (cons expr old-exprs) (cons  eval-result old-results) last-eventspace))]))
    
    
    (let*  ((results (get-web-results eval-lang defs-contents defs-result old-exprs old-results))
            (exec (car results))
            (defs (cadr results))
            (expr (caddr results))
            (lang (cadddr results))
            (empty (list-ref results 4)))
      (run-program exec defs expr lang empty)))
  
  
  
  
  
  
  
  (define (initial-web-call initial-request)
    (report-errors-to-browser send/back)
    (letrec 
        ((defs-list (extract-bindings 'defs (request-bindings initial-request)))
         (defs (if (null? defs-list) "" (car defs-list)))
         )
      (printf "~v" (current-directory))
      (web-main-loop defs '(#t ("")) '() '() (make-eventspace))))
  
  (define (local-main-loop last-eventspace l)
    (define (run-program exec defs expr lang empty)
      (cond 
        [exec (set! eval-lang lang) 
              (let* ((new-eventspace (make-eventspace))
                     (eval-result (debug "eval-eventspace 1" (eval-eventspace defs lang #t new-eventspace)))
                     )  
                (local-main-loop new-eventspace (cdr l)))]
        [empty (local-main-loop last-eventspace (cdr l))]
        [else (let* ((eval-result (debug "eval-eventspace 2" (eval-eventspace expr eval-lang #f last-eventspace)))
                     )
                (local-main-loop last-eventspace (cdr l)))]))
    
    
    (let*  ((results (get-local-results (car l)))
            (exec (car results))
            (defs (cadr results))
            (expr (caddr results))
            (lang (cadddr results))
            (empty (list-ref results 4)))
      (run-program exec defs expr lang empty)))
  
  (define (initial-local-call l)
    (local-main-loop (make-eventspace) l))
  
  (define test-list
    `((#t "(define x (call/cc (lambda (x) x)))")
      (#f "(x (lambda (y) 1))")))
  
  ; the initial call - start the program
  (define start 
    (lambda (ir)
      ;(initial-local-call test-list)
      (initial-web-call ir)
      ))
  

  ) 
   
