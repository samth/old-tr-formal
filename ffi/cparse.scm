(module cparse mzscheme
  
  (require (lib "lex.ss" "parser-tools")
         (prefix : (lib "lex-sre.ss" "parser-tools"))
         (lib "yacc.ss" "parser-tools"))
  
  (define-tokens
   value-tokens
   (ADD_ASSIGN
    AND_ASSIGN
    AND_OP
    AUTO
    BREAK
    CASE
    CHAR
    CONST
    CONSTANT
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
    IDENTIFIER
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
    STRING_LITERAL
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
    XOR_ASSIGN))
  (define-empty-tokens empty-tokens (! % & |(| |)| * + |,| - |.| / : |;| < = > ? |[| |]| ^ |{| \| |}| ~ EOF))
  
  (define-lex-abbrevs
   (letter (:or (:/ #\A #\Z) (:/ "a" "z") "_"))
   
   ;; (:/ 0 9) would not work because the lexer does not understand numbers.  (:/ #\0 #\9) is ok too.
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
     [(:or "=" "->" "(" ")" "[" "]" "{" "}" "." "*" "&&" "||" "++" "--") (string->symbol lexeme)]
     ;[line-comment (token-COMMENT lexeme)]
     [(:: "extern" (:+ whitespace) "\"C\"") 'EXTERN-C]
     [";" 'SEMI]
     ["," 'COMMA]
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
     [(:: "long" ws "long") 'LONG-LONG]
     ["long" 'LONG]
     
     ["__extension__" (clex input-port)]
     ;   [(:: "#" (:* whitespace) "ifdef") 'PRE-IFDEF]
     ;   [(:: "#" (:* whitespace) "if") 'PRE-IF]
     ;   [(:: "#" (:* whitespace) "ifndef") 'PRE-IFNDEF]
     ;   [(:: "#" (:* whitespace) "endif") 'PRE-ENDIF]
     ;   [(:: "#" (:* whitespace) "define") 'PRE-DEFINE]
     ;   [(:: "#" (:* whitespace) "else") 'PRE-ELSE]
     ;   [(:: "#" (:* whitespace) "undef") 'PRE-UNDEF]
     ;   [(:: "#" (:* whitespace) "include" (:* whitespace) "<" (:* (complement ">")) ">" ws #\newline)
     ;    (token-PRE-INCLUDE lexeme)]
     ;      
     [(:: letter (:* (:or digit letter))) (token-IDENTIFIER lexeme)]
     [(:+ digit) (token-CONSTANT (string->number lexeme))]
     [(:: (:+ digit) #\. (:* digit)) (token-CONSTANT (string->number lexeme))]
     )) 
  
  
  
  
  
  
  (define str (open-input-string "_foo /*  foo bar *** foo */= ->// 123 1\n//2.4\n"))
  (define p (open-input-file "pixman.ii"))
  (define (f) (let ((l (clex p))) (if (equal? l (token-EOF)) '() (cons l (f)))))
  
  (define (g) (clex p))
  
  (define types (make-hash-table 'equal)) 
  (define cparse 
    (parser
     (error (lambda (token-ok token-name token-value) (error "foo" token-ok token-name token-value)))
     (tokens value-tokens empty-tokens)
     (start translation_unit)
     (end EOF)
     (grammar
      (primary_expression ((IDENTIFIER) #f) ((CONSTANT) #f) ((STRING_LITERAL) #f) ((|(| expression |)|) #f))
      (postfix_expression
       ((primary_expression) #f)
       ((postfix_expression |[| expression |]|) #f)
       ((postfix_expression |(| |)|) #f)
       ((postfix_expression |(| argument_expression_list |)|) #f)
       ((postfix_expression |.| IDENTIFIER) #f)
       ((postfix_expression PTR_OP IDENTIFIER) #f)
       ((postfix_expression INC_OP) #f)
       ((postfix_expression DEC_OP) #f))
      (argument_expression_list ((assignment_expression) #f) ((argument_expression_list |,| assignment_expression) #f))
      (unary_expression
       ((postfix_expression) #f)
       ((INC_OP unary_expression) #f)
       ((DEC_OP unary_expression) #f)
       ((unary_operator cast_expression) #f)
       ((SIZEOF unary_expression) #f)
       ((SIZEOF |(| type_name |)|) #f))
      (unary_operator ((&) #f) ((*) #f) ((+) #f) ((-) #f) ((~) #f) ((!) #f))
      (cast_expression ((unary_expression) #f) ((|(| type_name |)| cast_expression) #f))
      (multiplicative_expression
       ((cast_expression) #f)
       ((multiplicative_expression * cast_expression) #f)
       ((multiplicative_expression / cast_expression) #f)
       ((multiplicative_expression % cast_expression) #f))
      (additive_expression
       ((multiplicative_expression) #f)
       ((additive_expression + multiplicative_expression) #f)
       ((additive_expression - multiplicative_expression) #f))
      (shift_expression
       ((additive_expression) #f)
       ((shift_expression LEFT_OP additive_expression) #f)
       ((shift_expression RIGHT_OP additive_expression) #f))
      (relational_expression
       ((shift_expression) #f)
       ((relational_expression < shift_expression) #f)
       ((relational_expression > shift_expression) #f)
       ((relational_expression LE_OP shift_expression) #f)
       ((relational_expression GE_OP shift_expression) #f))
      (equality_expression
       ((relational_expression) #f)
       ((equality_expression EQ_OP relational_expression) #f)
       ((equality_expression NE_OP relational_expression) #f))
      (and_expression ((equality_expression) #f) ((and_expression & equality_expression) #f))
      (exclusive_or_expression ((and_expression) #f) ((exclusive_or_expression ^ and_expression) #f))
      (inclusive_or_expression ((exclusive_or_expression) #f) ((inclusive_or_expression \| exclusive_or_expression) #f))
      (logical_and_expression ((inclusive_or_expression) #f) ((logical_and_expression AND_OP inclusive_or_expression) #f))
      (logical_or_expression ((logical_and_expression) #f) ((logical_or_expression OR_OP logical_and_expression) #f))
      (conditional_expression ((logical_or_expression) #f) ((logical_or_expression ? expression : conditional_expression) #f))
      (assignment_expression ((conditional_expression) #f) ((unary_expression assignment_operator assignment_expression) #f))
      (assignment_operator
       ((=) #f)
       ((MUL_ASSIGN) #f)
       ((DIV_ASSIGN) #f)
       ((MOD_ASSIGN) #f)
       ((ADD_ASSIGN) #f)
       ((SUB_ASSIGN) #f)
       ((LEFT_ASSIGN) #f)
       ((RIGHT_ASSIGN) #f)
       ((AND_ASSIGN) #f)
       ((XOR_ASSIGN) #f)
       ((OR_ASSIGN) #f))
      (expression ((assignment_expression) #f) ((expression |,| assignment_expression) #f))
      (constant_expression ((conditional_expression) #f))
      (declaration ((declaration_specifiers |;|) #f) ((declaration_specifiers init_declarator_list |;|) #f))
      (declaration_specifiers
       ((storage_class_specifier) #f)
       ((storage_class_specifier declaration_specifiers) #f)
       ((type_specifier) #f)
       ((type_specifier declaration_specifiers) #f)
       ((type_qualifier) #f)
       ((type_qualifier declaration_specifiers) #f))
      (init_declarator_list ((init_declarator) #f) ((init_declarator_list |,| init_declarator) #f))
      (init_declarator ((declarator) #f) ((declarator = initializer) #f))
      (storage_class_specifier ((TYPEDEF) #f) ((EXTERN) #f) ((STATIC) #f) ((AUTO) #f) ((REGISTER) #f))
      (type_specifier
       ((VOID) #f)
       ((CHAR) #f)
       ((SHORT) #f)
       ((INT) #f)
       ((LONG) #f)
       ((FLOAT) #f)
       ((DOUBLE) #f)
       ((SIGNED) #f)
       ((UNSIGNED) #f)
       ((struct_or_union_specifier) #f)
       ((enum_specifier) #f)
       ((TYPE_NAME) #f))
      (struct_or_union_specifier
       ((struct_or_union IDENTIFIER |{| struct_declaration_list |}|) #f)
       ((struct_or_union |{| struct_declaration_list |}|) #f)
       ((struct_or_union IDENTIFIER) #f))
      (struct_or_union ((STRUCT) #f) ((UNION) #f))
      (struct_declaration_list ((struct_declaration) #f) ((struct_declaration_list struct_declaration) #f))
      (struct_declaration ((specifier_qualifier_list struct_declarator_list |;|) #f))
      (specifier_qualifier_list
       ((type_specifier specifier_qualifier_list) #f)
       ((type_specifier) #f)
       ((type_qualifier specifier_qualifier_list) #f)
       ((type_qualifier) #f))
      (struct_declarator_list ((struct_declarator) #f) ((struct_declarator_list |,| struct_declarator) #f))
      (struct_declarator ((declarator) #f) ((: constant_expression) #f) ((declarator : constant_expression) #f))
      (enum_specifier ((ENUM |{| enumerator_list |}|) #f) ((ENUM IDENTIFIER |{| enumerator_list |}|) #f) ((ENUM IDENTIFIER) #f))
      (enumerator_list ((enumerator) #f) ((enumerator_list |,| enumerator) #f))
      (enumerator ((IDENTIFIER) #f) ((IDENTIFIER = constant_expression) #f))
      (type_qualifier ((CONST) #f) ((VOLATILE) #f))
      (declarator ((pointer direct_declarator) #f) ((direct_declarator) #f))
      (direct_declarator
       ((IDENTIFIER) #f)
       ((|(| declarator |)|) #f)
       ((direct_declarator |[| constant_expression |]|) #f)
       ((direct_declarator |[| |]|) #f)
       ((direct_declarator |(| parameter_type_list |)|) #f)
       ((direct_declarator |(| identifier_list |)|) #f)
       ((direct_declarator |(| |)|) #f))
      (pointer ((*) #f) ((* type_qualifier_list) #f) ((* pointer) #f) ((* type_qualifier_list pointer) #f))
      (type_qualifier_list ((type_qualifier) #f) ((type_qualifier_list type_qualifier) #f))
      (parameter_type_list ((parameter_list) #f) ((parameter_list |,| ELLIPSIS) #f))
      (parameter_list ((parameter_declaration) #f) ((parameter_list |,| parameter_declaration) #f))
      (parameter_declaration
       ((declaration_specifiers declarator) #f)
       ((declaration_specifiers abstract_declarator) #f)
       ((declaration_specifiers) #f))
      (identifier_list ((IDENTIFIER) #f) ((identifier_list |,| IDENTIFIER) #f))
      (type_name ((specifier_qualifier_list) #f) ((specifier_qualifier_list abstract_declarator) #f))
      (abstract_declarator ((pointer) #f) ((direct_abstract_declarator) #f) ((pointer direct_abstract_declarator) #f))
      (direct_abstract_declarator
       ((|(| abstract_declarator |)|) #f)
       ((|[| |]|) #f)
       ((|[| constant_expression |]|) #f)
       ((direct_abstract_declarator |[| |]|) #f)
       ((direct_abstract_declarator |[| constant_expression |]|) #f)
       ((|(| |)|) #f)
       ((|(| parameter_type_list |)|) #f)
       ((direct_abstract_declarator |(| |)|) #f)
       ((direct_abstract_declarator |(| parameter_type_list |)|) #f))
      (initializer ((assignment_expression) #f) ((|{| initializer_list |}|) #f) ((|{| initializer_list |,| |}|) #f))
      (initializer_list ((initializer) #f) ((initializer_list |,| initializer) #f))
      (statement
       ((labeled_statement) #f)
       ((compound_statement) #f)
       ((expression_statement) #f)
       ((selection_statement) #f)
       ((iteration_statement) #f)
       ((jump_statement) #f))
      (labeled_statement ((IDENTIFIER : statement) #f) ((CASE constant_expression : statement) #f) ((DEFAULT : statement) #f))
      (compound_statement
       ((|{| |}|) #f)
       ((|{| statement_list |}|) #f)
       ((|{| declaration_list |}|) #f)
       ((|{| declaration_list statement_list |}|) #f))
      (declaration_list ((declaration) #f) ((declaration_list declaration) #f))
      (statement_list ((statement) #f) ((statement_list statement) #f))
      (expression_statement ((|;|) #f) ((expression |;|) #f))
      (selection_statement
       ;((IF |(| expression |)| statement) #f)
       ((IF |(| expression |)| statement ELSE statement) #f)
       ((SWITCH |(| expression |)| statement) #f))
      (iteration_statement
       ((WHILE |(| expression |)| statement) #f)
       ((DO statement WHILE |(| expression |)| |;|) #f)
       ((FOR |(| expression_statement expression_statement |)| statement) #f)
       ((FOR |(| expression_statement expression_statement expression |)| statement) #f))
      (jump_statement
       ((GOTO IDENTIFIER |;|) #f)
       ((CONTINUE |;|) #f)
       ((BREAK |;|) #f)
       ((RETURN |;|) #f)
       ((RETURN expression |;|) #f))
      (translation_unit ((external_declaration) #f) ((translation_unit external_declaration) #f))
      (external_declaration ((function_definition) #f) ((declaration) #f))
      (function_definition
       ((declaration_specifiers declarator declaration_list compound_statement) #f)
       ((declaration_specifiers declarator compound_statement) #f)
       ((declarator declaration_list compound_statement) #f)
       ((declarator compound_statement) #f)))))
  )