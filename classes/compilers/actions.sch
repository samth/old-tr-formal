; Revision history:
;
; 6 October 2004
;     Fixed bugs in <exp> (mk_newexp, mkCaseExp).
; 30 September 2004
;     Fixed bug in <vardec> (mkVarDecs).

(define scanner.lineNumber (lambda () 0))
(define scanner.tokenValue (lambda () '*))

; Cruft.

(define jArrayType  'jArrayType)
(define jCall       'jCall)
(define jCase       'jCase)
(define jAref       'jAref)
(define jComplete   'jComplete)
(define jOp         'jOp)
(define jPartial    'jPartial)
(define jQualified  'jQualified)

(define NOPOS    0)
(define NOSYMBOL (Qsymbol.intern "%FAKE%"))
(define NOTREE   '())
(define NOP      'NOP)

(define (crash proc t)
  (astWrite t)
  (display "Compiler bug (")
  (display proc)
  (display ")")
  (exit 1))

(define (mkop op)
  (makeASTxxx 'jOp (scanner.lineNumber) NOSYMBOL NOSYMBOL
              NOTREE NOTREE NOTREE op))

; Action routines.

(define (emptyList) '())
(define (identity x) x)

(define (mkArrayType <type>) (makeArrayType (scanner.lineNumber) <type>))

(define (mkBooleanType) (makeBoolType (scanner.lineNumber)))

; <id1> is a field name, <id2> is a variable

(define (mkCase <id1> <id2> <exp>)
  (makeASTxxx jCase (scanner.lineNumber) <id1> <id2> <exp> NOTREE NOTREE NOP))

(define (mkCaseExp <exp0> <cases> <default>)
  (makeCaseExp (scanner.lineNumber)
               <exp0>
               (map astVarExp.name (map astSymbol111 <cases>))              ;!
               (map astVarExp.name (map astSymbol222 <cases>))              ;!
               (map astTree111 <cases>)
               <default>))

(define (mkCharLiteral)
  (makeCharLit (scanner.lineNumber)
               (string-ref (Qsymbol.toString (scanner.tokenValue)) 1)))

(define (mkCharType) (makeCharType (scanner.lineNumber)))

(define (mkCompoundExp <exps>) (makeBeginExp (scanner.lineNumber) <exps>))

(define (mkFalse) (makeFalseLit (scanner.lineNumber)))

; Achtung: Notice the reversal here (used in new record expressions).

(define (mkField <id> <exp>)
  (makeFieldExp (astPos <id>) <exp> (astVarExp.name <id>)))

(define (mkFieldDec <id> <argtype>)
  (makeFormalDec (astPos <id>) (astVarExp.name <id>) <argtype>))

(define (mkFloatLiteral)
  (makeFloatLit (scanner.lineNumber)
                (string->number (Qsymbol.toString (scanner.tokenValue)))))

(define (mkFloatType)
  (makeFloatType (scanner.lineNumber)))

; for <id> = <exp0> to <exp1> do <exp2>
; =>
; let $init = <exp0>
;     $limit = <exp1>
; in letrec $loop = lambda (<id> : int) : void .
;                     if <id> < $limit
;                       then begin <exp2>; $loop (<id> + 1) end
;                       else 0
;    in $loop ($init)

(define (mkForExp <bindingdec> <exp1> <exp2>)
  (let* ((pos (astPos <bindingdec>))
         ($init (Qsymbol.intern "$init"))
         ($limit (Qsymbol.intern "$limit"))
         ($loop (Qsymbol.intern "$loop"))
         (<id> (astBindingDec.name <bindingdec>))
         (<exp0> (astBindingDec.exp <bindingdec>))
         (loopcall (makeCallExp pos
                                (makeVarExp pos $loop)
                                (list (makeBinOpExp
                                       pos
                                      'plus_int
                                      (makeVarExp pos <id>)
                                      (makeLiteralExp
                                       pos
                                       (makeIntLit pos 1))))))
         (bodylambda (makeLambdaExp pos
                                    (list (makeFormalDec pos
                                                         <id>
                                                         (makeIntType pos)))
                                    (makeVoidType pos)
                                    (makeBeginExp pos (list <exp2> loopcall))))
         (body (makeCallExp pos
                            (makeVarExp pos $loop)
                            (list (makeLiteralExp pos (makeIntLit pos 1))))))
    (makeLetExp pos
                (list (makeBindingDec pos $init <exp0>)
                      (makeBindingDec pos $limit <exp1>))
                (makeLetrecExp pos
                               (list (makeBindingDec pos $loop bodylambda))
                               body))))

(define (mkFormal <type> <id>)
  (makeFormalDec (astPos <id>)
                 (astVarExp.name <id>)
                 <type>))

(define (mkFunDecs <fundecs>)
  (makeFunDec (astPos (car <fundecs>))
              (map astBindingDec.name <fundecs>)
              (map astBindingDec.exp <fundecs>)))

(define (mkFunctionType <argtypes> <rtype>)
  (makeFunType (astPos (car <argtypes>)) <argtypes> <rtype>))

(define (mkId)
  (makeVarExp (scanner.lineNumber) (scanner.tokenValue)))

(define (mkIfExp <exp0> <exp1> <exp2>)
  (makeIfExp (astPos <exp0>) <exp0> <exp1> <exp2>))

(define (mkIntLiteral)
  (let ((s (Qsymbol.toString (scanner.tokenValue))))
    (makeIntLit (scanner.lineNumber)
                (string->number s))))

(define (mkIntType)
  (makeIntType (scanner.lineNumber)))

(define (mkLambdaExp <formals> <rtype> <exp>)
  (makeLambdaExp (astPos <rtype>) <formals> <rtype> <exp>))

(define (mkLetExp <vardecs> <exp>)
  (if (null? <vardecs>)
      <exp>
      (makeLetExp (astPos (car <vardecs>)) <vardecs> <exp>)))

(define (mkLetRecExp <vardecs> <exp>)
  (if (null? <vardecs>)
      <exp>
      (makeLetRecExp (astPos (car <vardecs>)) <vardecs> <exp>)))

(define (mkLiteral <literal>)
  (makeLiteralExp (scanner.lineNumber) <literal>))

(define (mkMod <ids> <decs> <mod2>)
  (let* ((asts (append <ids> <decs> <mod2>))
         (pos (if (null? asts) (scanner.lineNumber) (astPos (car asts)))))
    (makeModDec pos (map astVarExp.name <ids>) <decs> <mod2>)))

(define (mkProductType <fielddecs>)
  (makeProductType (astPos (car <fielddecs>)) <fielddecs>))

(define (mkProgram <exp> <mods>)
  (makePgmDec (astPos <exp>) <exp> <mods>))

(define (mkStringLiteral)
  ; Must strip off the double quotes.
  (let* ((s (Qsymbol.toString (scanner.tokenValue)))
         (s (substring s 1 (- (string-length s) 1))))
    ;FIXME (escape characters aren't being recognized)
    (makeStringLit (scanner.lineNumber) s)))

(define (mkSumType <fielddecs>)
  (makeSumType (astPos (car <fielddecs>)) <fielddecs>))

(define (mkTrue)
  (makeTrueLit (scanner.lineNumber)))

(define (mkTypeDec <id> <newtype>)
  (makeFormalDec (astPos <id>) (astVarExp.name <id>) <newtype>))

(define (mkTypeDecs <typedecs>)
  (let ((pos (if (null? <typedecs>)
                 (scanner.lineNumber)
                 (astPos (car <typedecs>)))))
    (makeTypDec pos
                (map astFormalDec.name <typedecs>)
                (map astFormalDec.type <typedecs>))))

(define (mkTypeId <id>)
  (makeTypeId (astPos <id>) (astVarExp.name <id>)))

(define (mkVarDec <id> <exp>)
  (makeBindingDec (astPos <id>)
                  (astVarExp.name <id>)
                  <exp>))

(define (mkVarDecs <vardecs>)
  (let ((pos (if (null? <vardecs>)
                 (scanner.lineNumber)
                 (astPos (car <vardecs>)))))
    (makeVarDec pos                                                         ;!
                (map astBindingDec.name <vardecs>)
                (map astBindingDec.exp <vardecs>))))

(define (mkVoidType)
  (makeVoidType (scanner.lineNumber)))

; while <exp0> do <exp2>
; =>
; letrec $loop = lambda () : void .
;                  if <exp0>
;                    then begin <exp2>; $loop () end
;                    else 0
; in $loop ()

(define (mkWhileExp <exp0> <exp1>)
  (let* ((pos (astPos <exp0>))
         ($loop (Qsymbol.intern "$loop"))
         (loopcall (makeCallExp pos (makeVarExp pos $loop) '()))
         (bodylambda
          (makeLambdaExp pos
                         '()
                         (makeVoidType pos)
                         (makeIfExp pos
                                    <exp0>
                                    (makeBeginExp pos (list <exp1> loopcall))
                                    (makeLiteralExp pos (makeIntLit pos 0)))))
         (body (makeCallExp pos
                            (makeVarExp pos $loop)
                            '())))
    (makeLetrecExp pos
                   (list (makeBindingDec pos $loop bodylambda))
                   body)))

(define (mk_aref <exp> <factor-rest>)
  (makeASTxxx 'jAref NOPOS NOSYMBOL NOSYMBOL
               <exp> <factor-rest> NOTREE NOP))

(define (mk_argtype <type> <argtype2>)
  (case (astKind <argtype2>)
    ((jComplete) <type>)
    ((jArrayType)
     (mk_argtype (makeArrayType (astPos <type>) <type>)
                 (astTree111 <argtype2>)))
    (else (crash "mk_argtype" <argtype2>))))

(define (mk_arraytype <argtype2>)
  (makeASTxxx 'jArrayType NOPOS NOSYMBOL NOSYMBOL
              <argtype2> NOTREE NOTREE NOP))

(define (mk_call <actuals> <factor-rest>)
  (makeASTxxx 'jCall NOPOS NOSYMBOL NOSYMBOL
              <actuals> <factor-rest> NOTREE NOP))

(define (mk_complete)
  (makeASTxxx 'jComplete NOPOS NOSYMBOL NOSYMBOL
              NOTREE NOTREE NOTREE NOP))

(define (mk_factor <exp> <factor-rest>)
  (case (astKind <factor-rest>)
    ((jComplete)
     <exp>)
    ((jCall)
     (let* ((actuals (astTree111 <factor-rest>))
            (exp (makeCallExp (astPos <exp>) <exp> actuals))
            (factorRest (astTree222 <factor-rest>)))
       (mk_factor exp factorRest)))
    ((jQualified)
     (let* ((f (astSymbol111 (astTree111 <factor-rest>)))
            (exp (makeFieldExp (astPos <exp>) <exp> f))
            (factorRest (astTree222 <factor-rest>)))
       (mk_factor exp factorRest)))
    ((jAref)
     (let* ((subscript (astTree111 <factor-rest>))
            (exp (makeArrayExp (astPos <exp>) <exp> subscript))
            (factorRest (astTree222 <factor-rest>)))
       (mk_factor exp factorRest)))
    (else
     (crash "mk_factor" <factor-rest>))))

(define (mk_left <term> <simple-rest>)
  (case (astKind <simple-rest>)
    ((jComplete)
     <term>)
    ((= k jPartial)
     (let* ((op (astTree111 (astTree111 <simple-rest>)))
            (E2 (astTree222 (astTree111 <simple-rest>)))
            (rest (astTree222 <simple-rest>))
            (B (astOp000 op))
            (pos (astPos op)))
       (mk_left (makeBinOpExp pos B <term> E2) rest)))
    (else
     (crash "mk_left" <simple-rest>))))

(define (mk_newarray1 <primtype> <exp1> <exp2>)
  (makeNewArrayExp (astPos <primtype>)
                   <primtype>
                   <exp1>
                   <exp2>))

(define (mk_new_array <exp1> <exp2>)
  (makeASTxxx 'jNewArray (astPos <exp1>) NOSYMBOL NOSYMBOL
              <exp1> <exp2> NOTREE NOP))

(define (mk_new_struct <fields>)
  (makeASTxxx 'jNewStruct 0 NOSYMBOL NOSYMBOL
              <fields> NOTREE NOTREE NOP))

(define (mk_newexp <id> <new-rest>)
  (case (astKind <new-rest>)
    ((jNewArray)
     (makeNewArrayExp (astPos <id>)
                      (makeTypeId (astPos <id>) (astVarExp.name <id>))
                      (astTree111 <new-rest>)
                      (astTree222 <new-rest>)))
    ((jNewStruct)
     (makeNewRecordExp (astPos <id>)
                       (astVarExp.name <id>)                                ;!
                       (astTree111 <new-rest>)))
    (else
     (crash "mk_newexp" <new-rest>))))

(define (mk_noassoc <simple> <conjunct-rest>)
  (mk_right <simple> <conjunct-rest>))

(define (mk_partial <op> <exp>)
  (makeASTxxx 'jPartial NOPOS NOSYMBOL NOSYMBOL
              <op> <exp> NOTREE NOP))

(define (mk_qualified <id> <factor-rest>)
  (makeASTxxx 'jQualified NOPOS NOSYMBOL NOSYMBOL
              <id> <factor-rest> NOTREE NOP))

(define (mk_right <lhs> <exp-rest>)
  (case (astKind <exp-rest>)
    ((jComplete)
     <lhs>)
    ((jPartial)
     (let* ((pos (astPos (astTree111 <exp-rest>)))
            (B (astOp000 (astTree111 <exp-rest>)))
            (<rhs> (astTree222 <exp-rest>)))
       (case B
         ((or)
          (makeIfExp pos
                     <lhs>
                     (makeLiteralExp pos (makeTrueLit pos))
                     <rhs>))
         ((and)
          (makeIfExp pos
                     <lhs>
                     <rhs>
                     (makeLiteralExp pos (makeFalseLit pos))))
         (else
          (makeBinOpExp pos B <lhs> <rhs>)))))
    (else
     (crash "mk_right" <exp-rest>))))

(define (mk_unary <unop> <factor>)
  (makeUnOpExp (astPos <unop>) (astOp000 <unop>) <factor>))

(define (mkop_and)     (mkop 'and))
(define (mkop_assign)  (mkop 'assign))
(define (mkop_divide)  (mkop 'divide))
(define (mkop_equal)   (mkop 'eq))
(define (mkop_ge)      (mkop 'ge))
(define (mkop_greater) (mkop 'gt))
(define (mkop_le)      (mkop 'le))
(define (mkop_less)    (mkop 'lt))
(define (mkop_minus)   (mkop 'minus))
(define (mkop_ne)      (mkop 'ne))
(define (mkop_not)     (mkop 'not))
(define (mkop_or)      (mkop 'or))
(define (mkop_plus)    (mkop 'plus))
(define (mkop_sharp)   (mkop 'length))
(define (mkop_times)   (mkop 'times))
