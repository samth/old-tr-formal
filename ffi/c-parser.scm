(require (lib "lex.ss" "parser-tools")
         (prefix : (lib "lex-sre.ss" "parser-tools"))
         (lib "yacc.ss" "parser-tools"))

(define-tokens value-tokens (NUM ID COMMENT PREPROC))

(define-empty-tokens empty-tokens (TYPEDEF * SEMI |(| |)| |[| |]| |{| |}| |.| -> CONST STRUCT UNION COMMA 
                                           COLON = INT FLOAT CHAR EOF 
                                           AUTO CHAR CONST DOUBLE
                                           ENUM EXTERN-C FLOAT INT
                                           TYPEDEF STRUCT
                                           PRE-IF PRE-IFDEF PRE-DEFINE PRE-UNDEF PRE-ELSE 
                                           PRE-ENDIF PRE-IFNDEF
                                           ))
(define-lex-abbrevs
 (letter (:or (:/ #\A #\Z) (:/ "a" "z") "_"))

 ;; (:/ 0 9) would not work because the lexer does not understand numbers.  (:/ #\0 #\9) is ok too.
 (digit (:/ "0" "9"))
 (hex (:or (:/ #\A #\F) (:\ "a" "f") digit))
 (exp (:: (:or "e" "E") (:? (:or "-" "+")) (:+ digit)))
 (FS (:or "F" "f" "L" "l"))
 (IS (:* (:or "u" "U" "L" "l")))
 (comment (:: "/*" (complement (:: any-string "*/" any-string)) "*/"))
 (line-comment (:: "//" (complement (:: any-string #\newline any-string))))
 ;(preprocessor (:: "#" (complement (:: any-string #\newline any-string))))
 (whitespace (:or #\space #\tab #\newline))
 )



(define clex
  (lexer
   [(eof) 'EOF]
   [comment (token-COMMENT lexeme)]
   [whitespace (clex input-port)]
   [(:or "=" "->" "(" ")" "[" "]" "{" "}" "." "*") (string->symbol lexeme)]
   [line-comment (token-COMMENT lexeme)]
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
;   [preprocessor (token-PREPROC lexeme)]
   [(:: "#" (:* whitespace) "ifdef") 'PRE-IFDEF]
   [(:: "#" (:* whitespace) "if") 'PRE-IF]
   [(:: "#" (:* whitespace) "ifndef") 'PRE-IFNDEF]
   [(:: "#" (:* whitespace) "endif") 'PRE-ENDIF]
   [(:: "#" (:* whitespace) "define") 'PRE-DEFINE]
   [(:: "#" (:* whitespace) "else") 'PRE-ELSE]
   [(:: "#" (:* whitespace) "undef") 'PRE-UNDEF]
      
   [(:: letter (:* (:or digit letter))) (token-ID lexeme)]
   [(:+ digit) (token-NUM (string->number lexeme))]
   [(:: (:+ digit) #\. (:* digit)) (token-NUM (string->number lexeme))]
   ))



(define str (open-input-string "_foo /*  foo bar *** foo */= ->// 123 1\n//2.4\n"))
(define p (open-input-file "pixman.h"))
(define (f) (let ((l (clex p))) (if (equal? l (token-EOF)) '() (cons l (f)))))
