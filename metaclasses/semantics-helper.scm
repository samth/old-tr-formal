#cs(module semantics-helper mzscheme
     (require "scheme-tex.scm")
     
     (require (lib "quasistring.ss" "quasistring"))
     (require (lib "etc.ss") )
     (require (lib "list.ss"))
     (require (lib "match.ss"))
     
     (define popl #f)
     
     (provide (all-defined))
     
     (define mbox (predef 'mbox))
     
     
     
     (define (math . args) (ensuremath (apply group args)))
     
     (define subtype-sym (qs "$sp <:$sp"))
     (define not-subtype-sym (math (qs "$sp $(predef0 'not)<:$sp")))
     
     (define (not-subtype a b)
       (group a subtype-sym b))
     
     (define-values
       (a b c d e f g h i j k l m n o p q r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z CL)
       (apply values (map (compose mbox tt) '(a b c d e f g h i j k l m n o p q r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z CL))))
     
     (define-values
       (Object Class   kind type interface tru fls bookean extends implements return this instanceof newtt class)
       (apply values (map (compose mbox tt) '(Object Class   kind type interface true false bookean extends implements return this instanceof 
                                                     new class))))
     
     (define-values
       (semicolon comma dot)
       (values
        (mbox (tt ";"))
        (mbox (tt ","))
        (mbox (tt "."))
        ))
     
     (define (eq a b)
       (squish a " = " b))
     (define (neq a b)
       (squish a (math " \\not= ") b))
     (define (eqtt a b)
       (squish a (mbox (tt "\\ =\\ ")) b))
     
     
     (define id (lambda (x) x))
     
     (define (call meth args)
       (qs "$(id meth)$(parens (multiple args))"))
     
     (define invoke 
       (local ((define (invoke-help r f)
                 (mbox (format "~a~a~a"  (math r) dot  (math f)))))
         (match-lambda*
           [(rcvr field) (invoke-help rcvr field)]
           [(rcvr meth args) (invoke-help rcvr (call meth args))])))
     
     (define ov (compose math (predef 'ov)))
     
     (define-values (oa ob oc od oe of og oh oi oj  ol om on oo op oq  os ot ou  ow ox oy oz oA oB oC oD oE oF oG oH oI oJ oK oL oM 
                        oN oO oP oQ oR oS oT oU oV oW oX oY oZ)
       (apply values (map ov (list a b c d e f g h i j  l m n o p q  s t u  w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z))))
     
     (define (prime x) (format "~a~a" x (ensuremath "'")))
     
     (define-values (Gp Ip Jp Lp Mp Sp Tp Up Wp fp ep)
       (apply values (map prime (list G I J L M S T U W f e))))
     
     (define-values (oJp oSp oTp ofp)
       (apply values (map prime (list oJ oS oT of))))
     
     (define Upp (prime Up))
     
     (define production (mbox "::="))
     
     (define it (font 'it))
     
     (define (function nm)
       (lambda args
         (let ((sep ", "))
           (qs "$(mbox (it nm))($(apply string-append (interleave sep (map math args))))"))))
     
     (define-values  (Gamma Delta Phi) (apply values (map (compose math predef0) '(Gamma Delta Phi))))
     
     (define emptyset (predef0 'emptyset))
     
     (define-values (eproves eeproves egproves dproves dgproves deproves
                            )
       (values 
        (lambda (x) (proves emptyset x))
        (lambda (x) (proves emptyset emptyset x))
        (lambda (x) (proves emptyset Gamma x))
        (lambda (x) (proves Delta x))
        (lambda (x) (proves Delta Gamma x)) 
        (lambda (x) (proves Delta emptyset x))
      ))
     
     (define (dsub x y) (dproves (subtype x y)))
     
     (define CT (function "CT"))
     (define Gam (function Gamma))
     (define Del (function Delta))
     
     (define textrm (font 'textrm))
     
     (define (ok t) (qs "$(values t)$(mbox (textrm sp 'ok))"))
     (define (okin m t) (qs "$(values m)$(mbox (textrm sp 'ok 'in sp))$t"))
     
     (define (myproof . content)
       (apply paragraph (it "Proof") content))
     
     (define boundE (function (math (format "bound_~a" emptyset))))
     (define boundD (function (math (format "bound_~a" Delta))))
     
     (define (trans a b) (math (qs "$a $(predef0 'rightarrow) $b")))
     (define (trans* a b) (math (qs "$a $(predef0 'rightarrow)^* $b")))
     
     (define (phiof t f) ((function (math (format "~a_{~a}" Phi t))) f))
     
     (define (type-args nm args) (qs "$(id nm)$(parens (math (multiple args)))"))
     
     (define-values (mbody mtype methods fields field-vals super type-params dom override)
       (apply values (map function '(mbody mtype methods fields field-vals super params dom override))))
     
     (define (lines . args) (seq (interleave "" args)))
     
     (define subseteq (math (predef0 'subseteq)))
     (define forall (predef0 'forall))
     
     
     
     (define (esub a b) (eproves (subtype a b)))
     
     
     (define oep (prime oe))
     
     (define oee (trans oe oep))
     
     (define quad (predef0 'quad))
     
     (define vdash (predef0 'vdash))
     
     
     (define proves (case-lambda 
                      [(env conc) (math env vdash conc)]
                      [(env1 env2 conc) (proves (squish env1 ";" env2) conc)]))
     
     (define (mapping from to ty) (math (qs "{$lbrace $from $mapsto $to $rbrace}_{$ty}")))
     
     (define (make-pairs l)
       (cond
         [(empty? l) ()]
         [(not (zero? (modulo (length l) 2))) (error "even number of elements required")]
         [else (cons (list (car l) (cadr l)) (make-pairs (cddr l)))]))
     
     (define (uncurry f) (lambda (x) (apply f x)))
     
     (define (substitute . args)
       (let* ((pairs (make-pairs args))
              (mp (uncurry (lambda (x y) (math (qs "$x $(predef0 'mapsto) $y")))))
              (content (interleave "," (map mp pairs))))
         (lambda (x) (qs "[$(apply squish content)] $x"))))
     
     (define Tfe (format "~a ~a ~a ~a ~a" oT sp of sp oe))
     (define Tf (format "~a ~a ~a" oT sp of))
     
     (define (typ e t)
       (math (qs "$e : $t")))
     
     (define (type-args-bounds nm var ibound kbound)
       (math (qs "$(id nm)$(parens var super-sym (parens ibound comma kbound))")))
     
     
     (define-values (
                     preservationProof
                     progressProof 
                     typeSubstSubtypeLemma
                     typeSubstSubtypeProof
                     typeSubstTypeLemma
                     typeSubstTypeProof
                     substitutionPreservesTyping
                     substitutionPreservesTypingProof
                     substmbodyLemma
                     substmbodyProof
                     extensionMethodOKLemma
                     extensionMethodOKProof
                     fieldsPreservedLemma
                     fieldsPreservedProof
                     substDistFieldsLemma
                     substDistFieldsProof
                     methodTypingLemma
                     methodTypingProof
                     mtypembodyLemma
                     methodsDefinedLemma
                     substOKLemma
                     substOKProof
                     fieldsAgreeLemma
                     lbrace rbrace
                     rightarrow
                     )
       (apply values (map predef0 '(
                                    preservationProof
                                    progressProof 
                                    typeSubstSubtypeLemma
                                    typeSubstSubtypeProof
                                    typeSubstTypeLemma
                                    typeSubstTypeProof
                                    substitutionPreservesTyping
                                    substitutionPreservesTypingProof
                                    substmbodyLemma
                                    substmbodyProof
                                    extensionMethodOKLemma
                                    extensionMethodOKProof
                                    fieldsPreservedLemma
                                    fieldsPreservedProof
                                    substDistFieldsLemma
                                    substDistFieldsProof
                                    methodTypingLemma
                                    methodTypingProof
                                    mtypembodyLemma
                                    methodsDefinedLemma
                                    substOKLemma
                                    substOKProof
                                    fieldsAgreeLemma
                                    lbrace rbrace
                                    rightarrow
                                    ))))
     
     (define 3mm (vspace "3mm"))
     
     
     (define braces (compose (predef 'braces) group))
     (define parens (compose (predef 'parens) group))
     (define angles (compose (predef 'angles) group))
     (define brackets (compose (predef 'brackets) group))
     
     (define (multiple arg)
       (if (list? arg)
           (apply group (interleave ", " arg))
           (math (ov arg))))
     
     (define new
       (let ((new-help 
              (lambda (c t a)
                (let ((sub (if c (qs "_{$c}") "")))
                  (mbox (tt (qs "$(math newtt sub)$(parens (math (multiple t)))$(parens (math (multiple a)))")))))))
         (match-lambda*
           [(types args) (new-help #f types args)]
           [(class types args) (new-help class types args)])))
     
     (define (typeof t)
       (mbox (qs "$(tt 'typeOf)$(brackets (math t))")))
     
     (define-values (impl-sym kind-sym super-sym)
       (apply values (map math (list (predef0 'sqsubset) ":" (squish " " (predef0 'triangleleft))))))
     
     (define txt (compose tt (font 'small)))
     
     (define-values (Cpp FGJ FJ)
       (values "C++" "Featherweight GJ" "Featherweight Java"))
     
     (define frac (predef 'frac))
     
     (define (newfrac top bot)
       (frac top (qs "$bot $((predef 'rule) '0pt '11pt)")))
     
     (define phig (sub Phi G))
     
     (define e0 (sub e 0))

     
     (define (rule-label name) (mbox ((font 'bfseries) ((font 'sc) (qs "$(hspace '0cm) [$name]")))))
     
     (define displaystyle (predef 'displaystyle))
     
     (define (last l) (car (reverse l)))
     (define (butlast l) (reverse (cdr (reverse l))))
     
     (define rule
       (match-lambda*
         [(or () (name)) (error "not enough arguments to rule")]
         [(name rule) (math rule (rule-label name))]
         [(name top bot) (math (newfrac (displaystyle top) (displaystyle bot)) (rule-label name))]
         [(name . args) (let ((bot (last args))
                              (top (butlast args)))
                          (rule name (apply varray top) bot))])) 
     
     
     
     (define (cast t e)
       (mbox (tt (squish (parens (math t)) (math e)))))
     
     (define classdef
       (let ((class-front (lambda (name kind super interfaces)
                            (math (interleave sp (if popl 
                                                     (list class name kind-sym kind super-sym super)
                                                     (list class name kind-sym kind super-sym super impl-sym (multiple interfaces))))))))
         (match-lambda*
           [(and args (name kind super interfaces)) (apply class-front args)]
           [(name kind super interfaces cfields cmethods fields methods) 
            (math (group (class-front  name  kind  super  interfaces)
                         sp
                         (braces (interleave (group semicolon sp) (list cfields cmethods fields methods)))))]))
       )
     
     (define (arrtype a b)
       (group (math a) (math rightarrow) (math b)))
     
     (define (method-front t m ts xs)
       (group (math t) sp (math m) (parens (math ts) sp (math xs))))
     
     (define (method-def t m ts xs b)
       (group (method-front t m ts xs) (braces b)))
     
     (define (subtype a b)
       (group a subtype-sym b))
     
     (define interf-def
       (match-lambda*
         [(name kind interfaces) (interf-def name kind interfaces "...")]
         [(name kind interfaces body) (apply group (interleave sp (list interface  name  kind-sym kind impl-sym (multiple interfaces) (braces body))))]))
     
     (define-values 
       (CS CSp CR CX IS SforX SpforX RforX VforX)
       (values
        (type-args C S)
        (type-args C Sp)
        (type-args C R)
        (type-args C X)
        (type-args I S)
        (substitute oX oS)
        (substitute oX oSp)
        (substitute oX oR)
        (substitute oX oV)        
        ))
     
     (define-values (simple-class full-class full-class-syntax simple-method-syntax simple-method 
                                  simple-interf full-interf full-interf-syntax)
       (values
        (math (classdef (type-args-bounds C X I J) B A I))
        (math (classdef (type-args-bounds C X I J) B A I Tfe oM (group oW sp og) oN))
        (math (classdef (type-args-bounds C X T T) A A I Tfe oM Tf oM))
        (math (method-def T m oT ox e))
        (math (method-def U m oT ox e))
        (math (interf-def (type-args-bounds I X L Lp) K J))
        (math (interf-def (type-args-bounds I X L Lp) K J oM))
        (math (interf-def (type-args-bounds I X T T) A T oM))
        ))
     
     (define (squish/inter sep . args) (apply squish (interleave sep args)))
     
     (define space (lambda args (squish/inter sp args)))
     
     (define (parens/comma . arg) (parens (apply squish/inter ", " arg)))
     
     (define XIJ (group oX impl-sym (parens/comma oI oJ)))
     
     (define (rule-line . elems)
       (seq (append (interleave quad elems) (list 3mm ""))))

     (define eept (compose eeproves typ))
     
     (define-values (subi sub0) (values (lambda (x) (sub x "i")) (lambda (x) (sub x 0))))
     
   

     
     )
