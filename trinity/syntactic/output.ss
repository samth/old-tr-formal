#cs
(module output mzscheme
  (require (lib "list.ss" "srfi" "1"))
  (require (lib "string.ss" "srfi" "13"))
  ;(require (all-except (lib "list.ss") empty))
  (require (lib "contract.ss"))
  (require (lib "match.ss"))
  (require (lib "etc.ss"))
  (require "ast.ss")
  (require "../util/pprint.ss")

  (define current-indent-width (make-parameter 4))

  ;; TODO: output for literals
  ;; TODO: come up with more specific errors for when match falls through
  ;; TODO: literal needs subtypes for each literal type

  ;; ===========================================================================
  ;; Utilities
  ;; ===========================================================================

  ;; (listof (optional Doc) -> Doc
  (define (force-vertical ds)
    (unless (proper-list? ds)
      (fprintf (current-error-port)
               "not a proper list: ~v~n"
               ds))
    ((opt vsep) ds))
    ;(hcat (punctuate line (filter identity ds))))

  ;; Doc (listof (optional Doc)) -> (optional Doc)
  (define (align-sep sep ds)
    (let ([ds* (filter identity ds)])
      (and (pair? ds*)
           ;(vsep ds*))))
           (align (cat (punctuate sep ds*))))))

  ;; Doc (listof (optional Doc)) -> (optional Doc)
  (define (filter-sep sep ds)
    (let ([ds* (filter identity ds)])
      (and (pair? ds*)
           (cat (punctuate sep ds*)))))

  ;; (listof (optional Doc)) -> (optional Doc)
  (define (paragraphs ds)
    (let ([ds* (filter identity ds)])
      (and (pair? ds*)
           (vsep (punctuate line ds*)))))

  ;; ((listof Doc) -> Doc) -> ((listof (optional Doc)) -> (optional Doc))
  (define (opt comb)
    (lambda (ds)
      (let ([ds* (filter identity ds)])
        (and ds* (comb ds*)))))

  ;; (Doc ... -> Doc) -> ((optional Doc) ... -> (optional Doc))
  (define (opt* comb)
    (lambda ds
      (let ([ds* (filter identity ds)])
        (and ds* (apply comb ds*)))))

  ;; (optional Doc) -> Doc
  (define (opt->doc od)
    (or od empty))

  ;; (optional Doc) -> any
  (define (pp doc)
    (parameterize ([current-page-width 80])
      (if doc (pretty-print doc) "")))

  ;; TODO: find a simpler idiom for (opt->doc ((opt _) (list ...)))

  ;; ===========================================================================
  ;; Common
  ;; ===========================================================================

  ;; symbol -> Doc
  (define (render-symbol sym)
    (value->doc sym))

  ;; id -> Doc
  (define (render-id id)
    (render-symbol (id-name id)))

  ;; name -> Doc
  (define (render-name n)
    (match n
      [($ name _ path id)
       (hcat (punctuate dot (map render-id (append path (list id)))))]))

  ;; (listof name) -> Doc
  (define (render-name-list ns)
    (align-sep (text ", ") (map render-name ns)))

  ;; type-name -> Doc
  (define (render-type-name n)
    (cond
      [(primitive-type? n) (render-symbol n)]
      [(name? n) (render-name n)]
      [else (error 'render-type-name "bad type-name: ~a" n)]))

  ;; type-spec -> Doc
  (define (render-type-spec type)
    (<> (let ([base-type (type-spec-base-type type)])
          (if (name? base-type)
              (render-name base-type)
              (render-type-name base-type)))
        (render-dims (type-spec-dimension type))))

  ;; natural-number -> Doc
  (define (render-dims n)
    (hcat (build-list n (lambda (i)
                          (<> lbracket rbracket)))))

  ;; (listof name) string -> (optional Doc)
  (define (render-kw-list imp keyword)
    (and (pair? imp)
         (align-sep space (list (text keyword)
                                (render-name-list imp)))))

  ;; (optional Doc) -> Doc
  (define (in-block body)
    (if body
        (<> (nest (current-indent-width) (<> lbrace line body))
            line
            rbrace)
        (<+> lbrace rbrace)))

  ;; (listof a) (a -> (optional Doc)) -> Doc
  (define (render-args args renderer)
    (<> lparen
        (or (align-sep (text ", ") (map renderer args)) empty)
        rparen))

  ;; (listof variable-decl) -> Doc
  (define (render-formals formals)
    (render-args formals
                 ;; variable-decl -> (optional Doc)
                 (match-lambda
                   [($ variable-decl _ mods name type _)
                    ((opt hsep) (list (and (memq 'final (map modifier-modifier mods))
                                           (text "final"))
                                      (render-type-spec type)
                                      (render-id name)))])))

  ;; (listof expr) -> Doc
  (define (render-actuals actuals)
    (render-args actuals render-expression))

  ;; ===========================================================================
  ;; Top-level
  ;; ===========================================================================

  ;; compilation-unit -> (optional Doc)
  (define (render-program ast)
    (match ast
      [($ compilation-unit _ p is cs)
       (paragraphs (list (render-package p)
                         (render-imports is)
                         (render-type-decls cs)))]))

  ;; (optional name) -> (optional Doc)
  (define (render-package p)
    (and p (<> (text "package") space (render-name p) semi)))

  ;; (listof import) -> (optional Doc)
  (define (render-imports is)
    (and (pair? is)
         (force-vertical (map render-import is))))

  ;; import -> Doc
  (define (render-import i)
    (match i
      [($ import _ name star?)
       (<+> (text "import")
            (<> (render-name name)
                (if star? (<> dot (text "*")) empty)
                semi))]))

  ;; ===========================================================================
  ;; Declarations
  ;; ===========================================================================

  ;; (listof modifier) -> (optional Doc)
  (define (render-modifiers mods)
    (and (pair? mods)
         (fill-sep (map (compose render-symbol modifier-modifier) mods))))

  ;; (optional name) -> (optional Doc)
  (define (render-extends sup)
    (and sup ((opt hsep) (list (text "extends")
                               (render-name sup)))))

  ;; (listof type-decl) -> Doc
  (define (render-type-decls cs)
    (opt->doc (paragraphs (map render-decl cs))))

  ;; (optional decl) -> Doc
  (define (render-decl d)
    (cond
      [(class-decl? d) (render-class-decl d)]
      [(interface-decl? d) (render-interface-decl d)]
      [(behavior-decl? d) (render-behavior-decl d)]
      [(variable-decl? d) (render-variable-decl d)]
      [(not d) semi]
      [else (error 'render-decl "not a decl: ~v" d)]))

  ;; class-decl -> Doc
  (define (render-class-decl d)
    (match d
      [($ class-decl _ mods name imp body sup)
       (opt->doc
        ((opt fill-sep) (list ((opt hsep) (list (render-modifiers mods)
                                                (text "class")
                                                (render-id name)))
                              (align-sep space (list (render-extends sup)
                                                     (render-kw-list imp "implements")))
                              (in-block (render-class-body body)))))]))

  ;; interface-decl -> Doc
  (define (render-interface-decl d)
    (match d
      [($ interface-decl _ mods name sup body)
       (opt->doc
        ((opt fill-sep) (list ((opt hsep) (list (render-modifiers mods)
                                                (text "interface")
                                                (render-id name)))
                              (render-kw-list sup "extends")
                              (in-block (render-class-body body)))))]))

  ;; behavior-decl -> Doc
  (define (render-behavior-decl decl)
    (let ([ret-type (and (method-decl? decl) (method-decl-return-type decl))])
      (match decl
        [($ behavior-decl _ mods name formals throws body)
         (let ([prefix (opt->doc ((opt hsep) (list (render-modifiers mods)
                                                   (and ret-type (render-type-spec ret-type))
                                                   (<> (render-id name)
                                                       ;; TODO: soft-breaking nest?
                                                       (render-formals formals)))))]
               [throws-doc (render-kw-list throws "throws")])
           (cond
             [body (opt->doc ((opt fill-sep) (list prefix throws-doc (render-block body))))]
             [throws-doc (opt->doc ((opt fill-sep) (list prefix (<> throws-doc semi))))]
             [else (<> prefix semi)]))])))

  ;; variable-decl -> Doc
  (define (render-variable-decl d)
    (match d
      [($ variable-decl _ mods name type init)
       (let ([decl (hsep (filter identity (list (render-modifiers mods)
                                                (render-type-spec type)
                                                (render-id name))))])
         (<> (if init
                 (nest (current-indent-width)
                       ;; TODO: why doesn't this ever break?
                       (</> (<+> decl (text "="))
                            (render-expression init)))
                 decl)
             semi))]))

  ;; (listof class-element) -> (optional Doc)
  (define (render-class-body body)
    (let ([elts (paragraphs (map render-class-element body))])
      (if elts
          (<> line elts line)
          softline)))

  ;; class-element -> Doc
  (define (render-class-element elt)
    (cond
      [(initializer? elt) (render-initializer elt)]
      [(decl? elt) (render-decl elt)]
      [(pair? elt) (render-var-decl-list elt)]
      [(not elt) semi]
      [else (error 'render-class-element "not a class element: ~e" elt)]))

  ;; initializer -> Doc
  (define (render-initializer i)
    (if (initializer-static? i)
        (<+> (text "static")
             (render-block (initializer-body i)))
        (render-block (initializer-body i))))

  ;; (listof variable-decl) -> (optional Doc)
  (define (render-var-decl-list fs)
    (and (pair? fs)
         (let* ([mods (decl-modifiers (car fs))]
                [base-type (type-spec-base-type (variable-decl-type (car fs)))]
                [min-dim (apply min (map (compose type-spec-dimension variable-decl-type) fs))])
           (nest (current-indent-width)
                 (opt->doc
                  ((opt* <>)
                   ((opt* <+>) (render-modifiers mods)
                               (render-type-spec (make-type-spec (ast-src (variable-decl-type (car fs)))
                                                                 base-type
                                                                 min-dim))
                               (hcat (punctuate (<> comma softline)
                                                (map (lambda (f)
                                                       (let ([id (<> (render-id (decl-name f))
                                                                     (render-dims (- (type-spec-dimension (variable-decl-type f))
                                                                                     min-dim)))])
                                                         (if (variable-decl-init f)
                                                             (</> (<+> id (text "="))
                                                                 (render-expression (variable-decl-init f)))
                                                             id)))
                                                     fs))))
                   semi))))))

  ;; ===========================================================================
  ;; Expressions
  ;; ===========================================================================

  ;; expr -> Doc
  (define (render-expression e)
    (match e
      [($ conditional-expr _ test con alt)
       (<> (render-subexpression test)
           space
           (align-sep space
                      (list (<+> (text "?") (render-subexpression con))
                            (<+> (text ":") (render-subexpression alt)))))]
      [($ prefix-expr _ _ rator rand)
       (<> (render-symbol rator) (render-expression rand))]
      [($ postfix-expr _ _ rator rand)
       (<> (render-expression rand) (render-symbol rator))]
      [($ unary-expr _ _ rator rand)
       (<> (render-symbol rator) (render-subexpression rand))]
      [($ binary-expr _ _ rator left right)
       (let ([rator-text (case rator
                           [(or) (text "|")]
                           [(oror) (text "||")]
                           [else (render-symbol rator)])])
         (<+> (render-subexpression left)
              rator-text
              (render-subexpression right)))]
      [($ instanceof-expr _ _ expr type)
       (<+> (render-subexpression expr)
            (text "instanceof")
            (render-type-spec type))]
      [(? literal? e)
       (render-literal e)]
      [($ class-expr _ type)
       (<> (render-type-spec type) dot (text "class"))]
      [($ new-object-expr _ container name args class-body)
       (<+> (if container
                (<> (render-expression container) dot (text "new"))
                (text "new"))
            (<> (render-name name)
                (render-actuals args)
                (if class-body
                    (<> space (in-block (render-class-body class-body)))
                    empty)))]
      [($ new-array-expr _ type dim-exprs dim init)
       (<+> (text "new")
            (<> (render-type-spec type)
                (hcat (map (lambda (dim-expr)
                             (<> lbracket (render-expression dim-expr) rbracket))
                           dim-exprs))
                (hcat (build-list dim (lambda (i) (<> lbracket rbracket))))
                (if init (render-expression init) empty)))]
      [($ array-initializer _ contents)
       ;; TODO: parent node shouldn't nest with blocks!
       (<> lbrace softline (hcat (punctuate (<> comma softline) (map render-expression contents)))
           softline rbrace)]
      [($ call-expr _ obj name args)
       (<> (if obj (<> (render-expression obj) dot) empty)
           (render-name name)
           (render-actuals args))]
      [($ assign-expr _ op left right)
       (let ([op-text (if (eq? op 'or=)
                          (text "|=")
                          (render-symbol op))])
         (<+> (render-access left) op-text (render-expression right)))]
      [($ cast-expr _ type expr)
       (<> lparen (render-type-spec type) rparen (render-subexpression expr))]
      [(? access? e)
       (render-access e)]))

  ;; expr -> boolean
  (define (complex-expression? e)
    (or (binary-expr? e)
        (unary-expr? e)
        (postfix-expr? e)
        (prefix-expr? e)
        (conditional-expr? e)
        (instanceof-expr? e)
        (new-object-expr? e)
        (new-array-expr? e)
        (assign-expr? e)
        (cast-expr? e)))

  ;; expr -> Doc
  (define (render-subexpression e)
    (if (complex-expression? e)
        (<> lparen (render-expression e) rparen)
        (render-expression e)))

  ;; literal -> Doc
  (define (render-literal e)
    (match e
      [($ boolean-literal _ b)
       (if b (text "true") (text "false"))]
      [($ char-literal _ c)
       (<> squote (text (format-char c)) squote)]
      [($ integer-literal _ i)
       (value->doc i)]
      [($ long-literal _ l)
       (<> (value->doc l) (text "L"))]
      [($ float-literal _ f)
       (value->doc f)]
      [($ double-literal _ d)
       (<> (value->doc d) (text "d"))]
      [($ string-literal _ s)
       (<> dquote (text (apply string-append (map format-char (string->list s)))) dquote)]
      [($ null-literal _ _)
       (text "null")]))

  ;; string -> string
  (define (escape code)
    (string-append "\\" code))

  ;; char -> string
  (define (format-char c)
    (match c
      [#\backspace (escape "b")]
      [#\return (escape "r")]
      [#\newline (escape "n")]
      [#\tab (escape "t")]
      [#\\ (escape "\\")]
      [#\' (escape "'")]
      [#\" (escape "\"")]
      [_ (let ([n (char->integer c)])
           (if (<= 32 n 126)
               (string c)
               (string-append "\\" (string-pad (format "~o" n) 3 #\0))))]))

  ;; access -> Doc
  (define (render-access a)
    (match a
      [($ field-access _ obj name)
       (<> (render-subexpression obj) dot (render-id name))]
      [($ array-access _ arr index)
       (<> (render-subexpression arr) lbracket (render-expression index) rbracket)]
      [($ var-access _ name)
       (render-name name)]))

  ;; ===========================================================================
  ;; Statements
  ;; ===========================================================================

  ;; TODO: types are wrong for in-block, render-statement, et al

  ;; block-stmt -> Doc
  (define (render-block b)
    (in-block
     (match b
       [($ block-stmt _ body)
        (and (pair? body)
             (force-vertical (map render-block-statement body)))])))

  ;; block-statement -> (optional Doc)
  (define (render-block-statement s)
    (cond
      [(stmt? s) (render-statement s)]
      [(decl? s) (render-decl s)]
      [(pair? s) (render-var-decl-list s)] ; TODO: this has never been tested
      [else (error 'render-block-statement "not a block statement: ~e" s)]))

  ;; (optional statement) -> Doc
  (define (render-statement stmt)
    (match stmt
      [($ expr-stmt _ expr)
       (<> (render-expression expr) semi)]
      [($ labeled-stmt _ label stmt)
       (force-vertical (list (<> (render-id label) colon)
                             (render-statement stmt)))]
      [(? block-stmt? stmt)
       (render-block stmt)]
      [($ switch-stmt _ expr clauses)
       ;; TODO: fix the indentation
       (<+> (text "switch")
            (<> lparen (render-expression expr) rparen)
            (in-block (force-vertical (map render-switch-clause clauses))))]
      [($ if-stmt _ test con alt)
       (render-if test con alt)]
      [($ for-stmt _ init test update body)
       (let ([prefix (<+> (text "for")
                          (<> lparen
                              (render-for-init init)
                              (if test
                                  (<> space (render-expression test))
                                  empty) semi
                              (if (pair? update)
                                  (<> space (hcat (punctuate comma (map render-expression update))))
                                  empty)
                              rparen))])
         (cond
           ;; TODO: I should be able to abstract these kinds of tests by
           ;;       being smarter with render-statement=>block-stmt
           [(block-stmt? body) (<+> prefix (render-block body))]
           [(stmt? body) (<+> prefix (in-block (render-statement body)))]
           [(not body) (<> prefix semi)]
           [else (error 'render-for-stmt "not a for statement body: ~v" body)]))]
      [($ while-stmt _ expr body)
       (<+> (text "while")
            (<> lparen
                (render-expression expr)
                rparen
                (if body (<> space (render-block body)) semi)))]
      [($ do-stmt _ body expr)
       (<+> (text "do")
            (render-block body)
            (text "while")
            (<> lparen (render-expression expr) rparen semi))]
      [($ break-stmt _ label)
       (<> (if label
               (<+> (text "break") (render-id label))
               (text "break"))
           semi)]
      [($ continue-stmt _ label)
       (<> (if label
               (<+> (text "continue") (render-id label))
               (text "continue"))
           semi)]
      [($ return-stmt _ value)
       (<> (if value
               (<+> (text "return") (render-expression value))
               (text "return"))
           semi)]
      [($ throw-stmt _ expr)
       (<+> (text "throw") (render-expression expr))]
      [($ synchronized-stmt _ expr body)
       (<+> (text "synchronized")
            (render-expression expr)
            (render-block body))]
      [($ try-stmt _ body catches finally)
       (force-vertical
        (append (list (<+> (text "try") (render-block body)))
                (map render-catch catches)
                (list (and finally
                           (<+> (text "finally") (render-block finally))))))]
      [($ assert-stmt _ pred message)
       ;; TODO: implement me
       empty]
      [#f semi]))

  (define (render-for-init init)
    (cond
      [(null? init) semi]
      [(variable-decl? (car init)) (render-var-decl-list init)]
      [(expr? (car init)) (<> (render-actuals init) semi)] ; TODO: don't use render-actuals?
      [else (error 'render-for-init "not a list of variable-decl or expression: ~v" init)]))

  (define (render-if test con alt)
    (force-vertical
     (list (render-if/then test con)
           (and alt (render-else alt)))))

  ;; TODO: this indents even if if-clause is just ";"
  (define (render-if/then test con)
    (if (block-stmt? con)
        (<+> (text "if")
             (<> lparen (render-expression test) rparen)
             (render-block con))
        (<+> (text "if")
             (<> lparen
                 (render-expression test)
                 rparen
                 (nest (current-indent-width) (<> line (render-statement con)))
                 line))))

  (define (render-else alt)
    (match alt
      [#f #f]
      [($ if-stmt _ test con alt)
       (<+> (text "else") (render-if test con alt))]
      [(? block-stmt? alt)
       (<+> (text "else") (render-block alt))]
      [_ (<+> (text "else")
              (<> (nest (current-indent-width) (<> line (render-statement alt)))
                  line))]))

  (define (render-switch-clause clause)
    (if (case-stmt? clause)
        (render-case clause)
        (render-block-statement clause)))

  (define (render-case c)
    (match c
      [($ case-stmt _ test)
       (<> (if test (<+> (text "case") (render-expression test)) (text "default"))
           colon)]))

  (define (render-catch catch)
    (match catch
      [($ catch-stmt _ exn body)
       (<+> (text "catch") (render-formals (list exn)) (render-block body))]))

  (provide render-program (rename pp pretty-print)))
