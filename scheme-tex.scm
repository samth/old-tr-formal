(module scheme-tex (lib "qstr-lang.ss" "quasistring")
  (require (lib "etc.ss") (lib "list.ss") (lib "match.ss"))
  
  (provide (all-defined))
  
  (define sp "\\ ")
  
  (define section-depth (make-parameter 0))
  
  (define (squish . args) (apply string-append (map (lambda (x) (format "~a" x)) args)))
  
  (define (group . args) (if (and (pair? args) (list? (car args)))
                             (apply squish (interleave " " (car args)))
                             (apply squish (interleave " " args))))
  
  
  (define (seq l) (apply sequence l))
  
  (define (tex-process content) (seq content))
  
  (define input (lambda files (seq (map (predef 'input) files))))
  
  (define (interleave val lst)
    (foldr (lambda (x y) (if (null? y) (list x) (list* x val y))) () lst))
  
  (define (sequence . elems)
    (apply string-append (interleave "\n" elems)))
  
  (define (tex fname . content)
    (let* ([outport (open-output-file fname 'text 'truncate/replace)]
           [output-tex (tex-process content)])
      (write-string-avail output-tex outport)
      (close-output-port outport)))
  
  (define documentclass
    (match-lambda*
      [((? symbol? sym)) (format "\\documentclass{~a}" sym)]
      [((? symbol? sym) (? number? pt)) (format "\\documentclass{~v}[~vpt]" sym pt)]
      ))
  
  (define (sub a b) (ensuremath (format "~a_{~a}" a b)))
  
  (define (package sym)
    (format "\\usepackage{~v}" sym))
  
  (define (packages . syms)
    (apply sequence (map package syms)))
  
  
  
  (define maketitle "\\maketitle")
  
  (define wrap-brace (lambda (x) (format "{~a}" x)))
  (define wrap-brack (lambda (x) (format "[~a]" x)))
  
  (define (block type req-args opt-args . content)
    (let ([args1 (apply string-append (map wrap-brace req-args))]
          [args2 (apply string-append (map wrap-brack opt-args))])
      (sequence (format "\\begin{~a}~a~a" type args1 args2) (seq content) (format "\\end{~a}" type))))
  
  (define (ensuremath arg) (format "{\\ensuremath{~a}}" arg))
  
  
  (define (varray . args) (array (map list args)))
  (define (harray . args) (array (list args)))
  
  (define debug? #t)
  
  (define (debug x)
    (if debug? (begin (display x) (newline) x) x))
  
  (define (paragraph title . content)
    "\\paragraph{$title} $(seq content)")
  
  (define (in e set)
    (group e (predef0 'in) set))
  
  (define (do-array spec content)
    (let* ((make-line (lambda (row) (apply group (interleave "&" row))))
           (lines (map make-line content))
           (arr (seq (interleave "\\\\" lines))))
      (apply block 'array (list spec) '() (list arr))))
  
  (define array
    (match-lambda*
      [((? string? spec) content) (do-array spec content)]
      [(content) (do-array (apply string-append ""
                                  (build-list (length (car content)) 
                                              (lambda x "c")))
                           content)]))

                 
  (define (document . args)
    (apply block 'document () ()
           maketitle
           args)
    
    )
  
  
  (define-syntax predefs
    (syntax-rules ()
        [(_ sym ...)
         (define-values (sym ...)
           (values (predef (quote sym)) ...))]))
  
  (define-syntax predefs0
    (syntax-rules ()
        [(_ sym ...)
         (define-values (sym ...)
           (values (predef0 (quote sym)) ...))]))
  
  (define (predef0 name) (format "\\~a" name))
  
  (define (predef name) (lambda args (format "\\~a~a" name (apply string-append (map wrap-brace args)))))
  
  (define (font name) (lambda args (format "{\\~a {~a}}" name (group args))))
  
  (define tt (font 'tt))
  
  (predefs title author newpage vspace hspace)
  (predefs0 cup mapsto)
  
  (define-syntax section
    (syntax-rules ()
        [(_ title args ...)
         (let ([subs (apply string-append "" (build-list (section-depth) (lambda x "sub")))])
           (apply sequence (format "\\~asection{~a}" subs title)
                (parameterize ((section-depth (add1 (section-depth)))) 
                   (list args ...))))]))
  
  (define (itemize . elems)
    (apply block 'itemize () () (map (lambda (x) (format "\\item ~a" x)) elems)))
  
  (define (test-case)
    (tex "foo.tex"
         (documentclass 'article 12)
         (packages 'amsmath 'amssymb)
         (title "Foo")
         (author "Sam")
         (document 
          (section "sec1"
           (tt "foo")
           (section "sec2"
                    "bar"))
          ""
          (itemize "one" "two" "three")
          ""
         (harray "a" "b" "c")))
    ))
  
