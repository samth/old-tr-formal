(require (lib "lex.ss" "parser-tools")
         (prefix : (lib "lex-sre.ss" "parser-tools"))
         (lib "yacc.ss" "parser-tools"))

(define-tokens value-tokens (INT ID))

(define-empty-tokens empty-tokens (TYPEDEF 
                             STAR
                             SEMI
                             LP
                             RP
                             LB
                             RB
                             LC
                             RC
                             DOT
                             ARR
                             CONST
                             STRUCT
                             UNION
                             COMMA 
                             COLON
                             EQ))