(require (lib "lex.ss" "parser-tools")
         (prefix : (lib "lex-sre.ss" "parser-tools"))
         (lib "yacc.ss" "parser-tools"))

(define-tokens value-tokens (NUM ID COMMENT PREPROC PRE-INCLUDE))

(define-empty-tokens empty-tokens (TYPEDEF * SEMI |(| |)| |[| |]| |{| |}| |.| -> CONST STRUCT UNION COMMA 
                                           COLON = INT FLOAT CHAR EOF VOID
                                           AUTO CONST DOUBLE
                                           ENUM 
                                           TYPEDEF STRUCT LONG LONG-LONG
                                           SIGNED SHORT UNSIGNED
                                           PRE-IF PRE-IFDEF PRE-DEFINE PRE-UNDEF PRE-ELSE 
                                           PRE-ENDIF PRE-IFNDEF 
                                           && || ++ --
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
 (directive (:: "#" (complement (:: any-string #\newline any-string))))
 (whitespace (:or #\space #\tab #\newline))
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
   [(:: letter (:* (:or digit letter))) (token-ID lexeme)]
   [(:+ digit) (token-NUM (string->number lexeme))]
   [(:: (:+ digit) #\. (:* digit)) (token-NUM (string->number lexeme))]
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
   (start decs)
   (end EOF)
   
   (grammar
    (type [(INT) '(int)]
          [(CHAR) '(char)]
          [(FLOAT) '(float)]
          [(SHORT) '(short)]
          [(sign-qual type) (list* $1 $2)]
          [(size-qual type) (list* $1 $2)]
          [(struct-type) $1]
          [(enum-type) $1]
          [(type *) (list 'pointer $1)]
          [(ID) (list $1)]
          )
    (enum-type [(ENUM |{| ids |}|) (cons 'enum $3)])
    (ids [(ID) (list $1)]
         [(ID COMMA ids) (list* $1 $3)])
    (vardec [(type ids SEMI) (map (lambda (x) (list $1 x)) $2)])
    (vardecs [(vardec) $1]
             ;[(VOID) (list 'void)]
             [(vardec COMMA vardecs) (append $1 $3)])
    (struct-type [(STRUCT ID |{| vardecs |}|) (list 'struct $2 $4)]
                 [(STRUCT ID) (list 'struct $2)])
    (size-qual [(LONG) 'long]
               [(SHORT) 'short]
               [(LONG-LONG) 'longlong])
    (sign-qual [(SIGNED) 'signed]
               [(UNSIGNED) 'unsigned]
               )
    (decs [(dec) (display $1)]
               [(dec decs) (display $1)])
    (dec [(type-def) #f]
         [(fun-def) #f])
    (fun-def [(type ID |(| vardecs |)| SEMI) (display (list $1 $2 $4))])
    (type-def [(TYPEDEF type ID SEMI) (hash-table-put! types $3 $2)]))))

(define simple "typedef int foobar ;")
(define str2 (open-input-string simple))



(cparse (lambda () (clex p)))