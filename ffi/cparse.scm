(module cparse mzscheme
  
  (require (lib "lex.ss" "parser-tools")
           (prefix : (lib "lex-sre.ss" "parser-tools"))
           (lib "yacc.ss" "parser-tools")
           (lib "list.ss")
           (lib "etc.ss")
           (lib "test.ss" "schemeunit")
           (lib "assert-test.ss" "schemeunit")
           (lib "assert-util-test.ss" "schemeunit")
           (lib "test-test.ss" "schemeunit")
           (lib "graphical-ui.ss" "schemeunit")
           (lib "pretty.ss")
           (lib "match.ss")
           )
  
  (define-syntax thunk
    (syntax-rules ()
      [(thunk e) (lambda () e)]))
  
  (define-syntax def-struct
    (syntax-rules ()
      [(_ e ...) (define-struct e ... (make-inspector))]))
  
  (define typenames (make-hash-table 'equal))
  
  (define (add-type str)
    (hash-table-put! typenames str (token-TYPE_NAME str)))
  
  (define (lex-ident str)
    (hash-table-get typenames str (thunk (token-IDENTIFIER str))))
  
  (define-struct var (name type) (make-inspector))

  (define-struct func (name ret-type args) (make-inspector))

  (define-struct typedef (name type) (make-inspector))
  
  (def-struct all-struct ())
  
  (def-struct (anon-struct all-struct) (elems))
  
  (def-struct (opaque-struct all-struct) (name))
  
  (def-struct (full-struct all-struct) (name elems))

  (def-struct ptr-type (base))
  
  (def-struct type-mod (base mod))
  
  (define-tokens value-tokens (CONSTANT IDENTIFIER STRING_LITERAL))
  
  (define-tokens
   empty-tokens
   (ADD_ASSIGN
    AND_ASSIGN
    AND_OP
    AUTO
    BREAK
    CASE
    CHAR
    CONST
    CONTINUE
    DEC_OP
    DEFAULT
    DIV_ASSIGN
    DO
    DOUBLE
    ELLIPSIS
    ELSE
    ENUM
    EQ_OP
    EXTERN
    FLOAT
    FOR
    GE_OP
    GOTO
    IF
    INC_OP
    INT
    LEFT_ASSIGN
    LEFT_OP
    LE_OP
    LONG
    MOD_ASSIGN
    MUL_ASSIGN
    NE_OP
    OR_ASSIGN
    OR_OP
    PTR_OP
    REGISTER
    RETURN
    RIGHT_ASSIGN
    RIGHT_OP
    SHORT
    SIGNED
    SIZEOF
    STATIC
    STRUCT
    SUB_ASSIGN
    SWITCH
    TYPEDEF
    TYPE_NAME
    UNION
    UNSIGNED
    VOID
    VOLATILE
    WHILE
    XOR_ASSIGN
    LONG-LONG
    ! % & |(| |)| * + |,| - |.| / : |;| 
    < = > ? |[| |]| ^ |{| \| |}| ~ EOF ...))
  
  (define-lex-abbrevs
   (letter (:or (:/ #\A #\Z) (:/ "a" "z") "_"))
   
   ;; (:/ 0 9) would not work because the lexer does not understand numbers.  
   ;; (:/ #\0 #\9) is ok too.
   (digit (:/ "0" "9"))
   (hex (:or (:/ #\A #\F) (:\ "a" "f") digit))
   (expon (:: (:or "e" "E") (:? (:or "-" "+")) (:+ digit)))
   (FS (:or "F" "f" "L" "l"))
   (IS (:* (:or "u" "U" "L" "l")))
   (comment (:: "/*" (complement (:: any-string "*/" any-string)) "*/"))
   (line-comment (:: "//" (complement (:: any-string #\newline any-string))))
   (directive (:: "#" (complement (:: any-string #\newline any-string))))
   ;(white-space (:or #\space #\tab #\newline))
   (ws (:* whitespace))
   )
  
  
  
  (define clex
    (lexer
     [(eof) 'EOF]
     ["\\\n" (clex input-port)]
     [directive (clex input-port)]
     ;[comment (token-COMMENT lexeme)]
     [whitespace (clex input-port)]
     [(:or "..." "=" "->" "(" ")" "[" "]" "{" "}" "." "*" "&&" "||" "++" "--" ";" "," "+" "-" "/" "%") 
      (string->symbol lexeme)]
     ; keywords go here
     ["auto" 'AUTO]
     ["char" 'CHAR]
     ["const" 'CONST]
     ["double" 'DOUBLE]
     ["enum" 'ENUM]
     ["extern" 'EXTERN]
     ["float" 'FLOAT] 
     ["int" 'INT]
     ["typedef" 'TYPEDEF]
     ["struct" 'STRUCT]
     ["void" 'VOID]
     ["signed" 'SIGNED]
     ["unsigned" 'UNSIGNED]
     ["short" 'SHORT]
     ["void" 'VOID]
     ["long" 'LONG]
     ["union" 'UNION]
     ["sizeof" 'SIZEOF]
     
     ["__extension__" (clex input-port)]
  
     [(:: letter (:* (:or digit letter))) (lex-ident lexeme)]
     [(:+ digit) (token-CONSTANT (string->number lexeme))]
     [(:: (:+ digit) #\. (:* digit)) (token-CONSTANT (string->number lexeme))]
     [(:: "0" "x" (:+ digit)) (token-CONSTANT (string->number (substring lexeme 2) 16))]
     )) 
  
  
  (define (initialize-table)
    (set! typenames (make-hash-table 'equal))
    (hash-table-put! typenames "__builtin_va_list" (token-TYPE_NAME "__builtin_va_list"))
    )
  
  
 
  
  
  
  (define-syntax parser/values
    (syntax-rules ()
      [(_ . e) (let  ((p (parser . e)))
                 (if (list? p) (apply values p) p))]))
  
  (define-values
    (cparse parse-decl parse-type parse-funargs)
    (parser/values
     (error (lambda (token-ok token-name token-value) 
              ;(pretty-print (hash-table-map typenames cons))
              (display (list "foo" token-ok token-name token-value))))
     (tokens value-tokens empty-tokens)
     (start decls decl type funargs)
     (end EOF)
     
     (debug "debugout")
     
     (grammar

      (decls
       [(decl) (list $1)]
       [(decl decls) (cons $1  $2)])
      
      (decl
       [(name-decl |;|) $1]
       [(type-decl |;|) $1]
       [(typedef |;|) $1])
      
      (typedef
       [(TYPEDEF name-decl)
        (match $2
          [(($ var nm ty)) 
           (begin
             (add-type nm)
             (make-typedef nm ty))])])
      
      (type-decl
       [(struct-def) $1]
       [(union-def) $1]
       [(enum-def) $1])
      
      (union-def
       [(UNION |{| name-decls |}|) (list 'union $3)])
      
      (enum-def 
       [(ENUM |{| ids |}|) (cons 'enum $3)]
       [(ENUM IDENTIFIER |{| ids |}|) (list* 'enum $2 $4)]
       )

      (struct-def 
       [(STRUCT id |{| name-decls |}|) (make-full-struct $2 $4)]
       [(STRUCT |{| name-decls |}|) (make-anon-struct $3)]
       [(STRUCT id) (make-opaque-struct $2)])
      
      (name-decls
       [(name-decl |;|) (list $1)]
       [(name-decl |;| name-decls) (cons $1 $3)])
      
      (name-decl
       [(func-decl) $1]
       [(var-decl) $1])
      
      (var-decl
       [(type ids) (map (lambda (x) (make-var x $1)) $2)])
      
      (unmod-type
       [(base-type) $1]
       [(struct-def) $1]
       [(enum-def) $1]
       [(union-def) $1])
      
      (base-type
       [(INT) 'int]
       [(SHORT) (make-type-mod 'int 'short)]
       [(FLOAT) 'float]
       [(CHAR) 'char]
       [(DOUBLE) 'double]
       [(LONG) (make-type-mod 'int 'long)]
       [(VOID) 'void]
       [(TYPE_NAME) $1])
      
      (type
       [(unmod-type) $1]
       [(type-mod type) (make-type-mod $2 $1)]
       [(type *) (make-ptr-type $1)])
      
      (type-mod
       [(CONST) 'const]
       [(LONG) 'long]
       [(SIGNED) 'signed]
       [(UNSIGNED) 'unsigned]
       [(SHORT) 'short])
      
      
      (const-expr
       [(add-expr) $1])
      
      (func-decl
       [(type IDENTIFIER |(| funargs/opt |)|) (make-func $2 $1 $4)]
       [(type |(| * IDENTIFIER |)| |(| funargs/opt |)|) (make-func $2 $1 $4)]
       )
      
      (funargs/opt
       [() '()]
;       [(VOID) '()]
       [(funargs) $1])
      
      (funargs
       [(funarg) (list $1)]
       [(funarg |,| funargs) (cons $1 $3)]
       )
      
      (funarg
       [(type) $1]
       [(type IDENTIFIER) (make-var $2 $1)])
      
      (add-expr
       [(mul-expr) $1]
       [(add-expr + mul-expr) (list '+ $1  $3)]
       [(add-expr - mul-expr) (list '- $1  $3)])

      (mul-expr
       [(cast-expr) $1]
       [(mul-expr / cast-expr) (list '/ $1 $3)]
       [(mul-expr % cast-expr) (list '% $1 $3)]
       [(mul-expr * cast-expr) (list '* $1 $3)])

      (cast-expr
       [(unary-expr) $1]
       [(|(| type |)| cast-expr) (list 'cast $2 $4)])
      
      (unary-op
       [(*) $1]
       [(&) $1]
       [(+) $1]
       [(-) $1]
       [(!) $1]
       [(~) $1]
       )
      
      (postfix-expr
       [(primary-expr) $1])
      
      (primary-expr
       [(CONSTANT) $1]
       [(|(| const-expr |)|) $2])
      
      (unary-expr
       [(postfix-expr) $1]
       [(unary-op cast-expr) (list $1 $2)]
       [(SIZEOF unary-expr) (list 'sizeof $2)]
       [(SIZEOF |(| type |)|) (list 'sizeof $3)])

      (id/array/init
       [(IDENTIFIER) $1]
       [(id/array/init |[| const-expr |]|) (list $1 'array $3)]
       [(id/array/init = const-expr) (list $1 '= $3)])
      
      (ids [(id/array/init) (list $1)]
           [(id/array/init |,| ids) (list* $1 $3)])
      
      ;;;; old grammar below
      
;      
;      #;(type-specs
;       [(type-spec) $1]
;       [(type-specs type-spec) (append $1 $2)]
;       [(type-specs *) (append $1 (list '*))])
;      
;      #;(type-spec
;       [(INT) '(int)]
;       [(CHAR) '(char)]
;       [(FLOAT) '(float)]
;       [(SHORT) '(short)]
;       [(LONG) '(long)]
;       [(DOUBLE) '(double)]
;       [(SIGNED) '(signed)]
;       [(UNSIGNED) '(unsigned)]
;       [(VOID) '(void)]
;       [(CONST) '(const)]
;       [(struct-type) $1]
;       [(union-type) $1]
;       [(enum-type) $1]
;       [(TYPE_NAME) (list $1)]
;       )
;      
;      
;      
;      
;      #;(vardec [(type-specs ids |;|) (map (lambda (x) (list $1 x)) $2)]
;              [(type-specs |;|) (list $1)])
;      #;(vardecs [(vardec) $1]
;               [(vardecs  vardec) (append $1 $2)])
;      
      (id
       [(IDENTIFIER) $1]
       [(TYPE_NAME) $1])
;      
;      #;(var-dec
;       [(type-specs IDENTIFIER) (list $1 $2)]
;       [(type-specs IDENTIFIER |[| |]|) (list $1 $2 'array)]
;       [(type-specs IDENTIFIER |[| const-expr |]|) (list $1 $2 'array $4)]
;       [(type-specs IDENTIFIER = const-expr) (list $1 $2 '= $3)]
;       )
;
;      #;(decs [(dec) (begin (display $1) 
;                          (newline) 
;                          (list $1))]
;            [(dec decs) (cons $1 $2)])
;      
;      #;(dec [(type-def |;|) $1]
;           [(fun-def  |;|) $1]
;           [(struct-type |;|) $1]
;           [(EXTERN fun-def  |;|) $2]
;           [(var-dec |;|) $1]
;           [(EXTERN var-dec |;|) $2]
;           [(enum-type |;|) $1])
;
;      #;(type-def 
;       [(TYPEDEF type-specs IDENTIFIER) 
;        (begin
;          (hash-table-put! typenames $3 (token-TYPE_NAME $3))
;          `(typedef ,$2 ,$3))]
;       [(TYPEDEF type-specs |(| * IDENTIFIER |)| |(| funargs/opt |)|)
;        (begin 
;          (hash-table-put! typenames $5 (token-TYPE_NAME $5))
;          `(typedef (func ,$2 ,$8) ,$5))]
;       [(TYPEDEF type-specs IDENTIFIER |(| funargs/opt |)|)
;        (begin 
;          (hash-table-put! typenames $3 (token-TYPE_NAME $3))
;          `(typedef (func ,$2 ,$6) ,$3))])
        )))
  
  (define str "typedef short int st; typedef st bar;")
  
  
  ;(define test (cparse (thunk (clex str))))
  
  (define parse 
    (opt-lambda
        (input [parser cparse])
      (define (internal-parse x) (parser (thunk (clex x))))
      (initialize-table)
      (cond [(input-port? input)
             (internal-parse input)]
            [(and (path? input)
                  (file-exists? input))
             (internal-parse (open-input-file input))]
            [(and (string? input)
                  (file-exists? (string->path input)))
             (internal-parse (open-input-file input))]
            [(string? input) ;(display str)
             (internal-parse (open-input-string input))]
            [else (error "bad input to parse")])))
  
  (define (parse-tests)
    (let 
        ([str-result `(,(make-typedef  "st" '(short (int))) 
                       ,(make-typedef  "bar" '("st")))])
      (make-test-suite 
       "Parse Tests"
       (make-test-case "Parse String port"
                       (assert-equal? str-result (parse (open-input-string str))))
       (make-test-case "Parse filename as string"
                       (assert-equal? str-result (parse "testfile.c")))
       (make-test-case "Parse filename as path"
                       (assert-equal? str-result (parse (string->path "testfile.c"))))
       (make-test-case "Parse String"
                       (assert-equal? str-result (parse str)))
       (make-test-case "Parse Number fails"
                       (assert-exn void (thunk (parse 5)))))))
  
  (define simple-typedef "typedef int foo;")
  (define typedef-pointer "typedef int * foo;")
  (define typedef-opaque-struct "typedef struct bar foo;")
  (define typedef-simple-struct "typedef struct baz {int x;} foo;")
  (define typedef-struct "typedef struct baz {int x; float y;} foo;")
  (define simple-fun "int foo();")
  (define one-arg-fun "int foo(int x);")
  
  (define (parse-decl-tests)
    (define (p x) (parse x parse-decl))
    (make-test-suite
     "Declaration Tests"
     (make-test-case "Opaque Struct" (p typedef-opaque-struct))
     (make-test-case "One Elem Struct" (p typedef-simple-struct))
     (make-test-case "Simple Function Dec" (p simple-fun))
     (make-test-case "One Arg Function Dec" (p one-arg-fun))
     (make-test-case "Full Struct"
      (assert-equal?
       (make-typedef "foo" 
                     (make-full-struct 
                      "baz" 
                      (list (make-var "x" (list 'int)) 
                            (make-var "y" (list 'float)))))
       (p typedef-struct)
       ))))
  
  (define (show-types) (hash-table-map typenames list))
  
  (define (run-tests)  
    (test/graphical-ui
     (make-test-suite "C Parser Tests"
                      (parse-tests)
                      (parse-decl-tests)
                      ))
    (void)
    )
  
  )