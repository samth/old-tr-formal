(module select mzscheme
  (require (lib "contract.ss"))
  (require (lib "list.ss" "srfi" "1"))
  (require "../syntactic/ast.ss")

  ;; select : (any -> boolean) ast -> (listof ast)
  (define (select p? tree)
    ;; select-with-p? : ast -> (listof ast)
    (let ([select-with-p? (lambda (t) (select p? t))]
          [subtrees (immediate-subtrees tree)])
      (if (p? tree)
          (cons tree (append-map select-with-p? subtrees))
          (append-map select-with-p? subtrees))))

  ;; immediate-subtrees : ast -> (listof ast)
  (define (immediate-subtrees tree)
    ;; immediate-subtrees* : (listof any) -> (listof ast)
    (define (immediate-subtrees* fields)
      (if (null? fields)
          null
          (let ([field (car fields)])
            (cond
              [(ast? field) (cons field (immediate-subtrees* (cdr fields)))]
              [(pair? field) (append (immediate-subtrees* field)
                                     (immediate-subtrees* (cdr fields)))]
              [else (immediate-subtrees* (cdr fields))]))))
    (immediate-subtrees* (vector->list (struct->vector tree))))

  (provide/contract [select ((any/c . -> . boolean?) ast? . -> . (listof ast?))]))