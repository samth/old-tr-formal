#cs(module sem-proofs (lib "qstr-lang.ss" "quasistring")
     (require "semantics-helper.scm")
     (require "scheme-tex.scm")
     (require (lib "etc.ss") )
     (require (lib "list.ss"))
     (require (lib "match.ss"))
     (provide (all-defined))
     
     (define unproved "Unproved.")
     
     (define thm/lem
       (lambda
           (thm? name stmt)
         (let ((env (if thm? "theorem" "lemma")))
           (opt-lambda
               ([proof #f])
             (sequence 
               (block
                env
                '()
                (list name)
                stmt)
               (if proof
                   (myproof proof)
                   "")))
           )))
     
     (define (theorem nm st) (thm/lem #t nm st))
     (define (lemma nm st) (thm/lem #f nm st))
     
     (define (proof-cases . body)
       (apply block 'description '() '() body))
     
     (define (proof-case head body)
       (sequence "$(predef0 'item )[Case $(id head):]"
                 body))
     
     (define (proof-case/rn name body) (proof-case (rule-label name) body))
     
     (define preservation
       (theorem
        "Subject Reduction"
        "If $(eept e S) and $(trans e ep) then $(eept ep T) where $(esub T S)."
        ))
     
     (define progress
       (theorem
        "Progress"
        (sequence "If $(eept e S) then one of the following holds:"
                  (itemize
                   (eq e (mapping of (ov v) G))
                   (trans e ep)
                   "$(eq e (cast S ep)) and $(eept ep T) and $(eproves (not-subtype T S))."))
        ))
     
     (define soundness
       (theorem 
        "Type Soundness"
        (sequence "If $(eept e S) then one of the following holds:"
                  (itemize 
                   (group (trans* e (mapping of (ov v) G)) "where" (esub G S))
                   (group (trans* e ep) "where $ep is an invalid cast")
                   "$e reduces infinitely."))
        ))
     
     (define xd (substitute ox od))
     
     (define substitution-preserves-typing
       (lemma "Substitution Preserves Typing"
              (group "If" (dgproves (typ e T)) "and" (eq Gamma (typ ox oS)) "and"
                     (deproves (typ od oU)) "and" (dsub oU oS) "then"
                     (deproves (typ (xd e) T)) "where" (dsub Tp T) ".")))
     
     
     
     (define xsp (substitute oX oSp))
     
     (define type-sub-preserves-typing
       (lemma "Type Substitution Preserves Typing"
              (group "If" (eq Delta (group oX super-sym oS)) 'and (dgproves (typ e T))
                     'and (esub oSp (xsp oS)) 'then (proves (squish emptyset ";" (xsp Gamma))
                                                            (typ (xsp e) (xsp T))) ".")
              ))
     (define-values (xi Si Spi) (values (subi x) (subi S) (prime (subi S))))
     (define (one-case this-e this-T . rest)
       (apply group "$(eq e this-e), $(eq T this-T)" rest))
     
     (define tspt-proof
       (sequence 
         "We prove this by induction over the derivation of $(dgproves (typ e T))."
         (case-proof/rn
          ("T-Var"  (one-case v (Gam v)
                              "Then" (eq (xsp e) v) 'and (eq (xsp (Gam v)) ((function (xsp Gamma)) v))))
          ("T-Class" (one-case R (typeof R)
                               "If" (neq R (subi X)) "then substitution has no effect."
                               "Otherwise," (eq (xsp R) Spi) "and" (eq (xsp (typeof R)) (typeof Spi))))
          ("T-Cast" (one-case (cast R ep) R
                              (case-proof
                               ((neq R (subi X)) "Then $(eq (xsp e) (cast R (xsp ep))), which still has type $R")
                               ((eq R (subi X)) "Then $(eq (xsp e) (cast (subi S) (xsp ep))), which  has type $(eq (subi S) (xsp R)).")
                               )))
          ("T-Mapping" (one-case (mapping of oep G) G
                                 "Then" ((xsp e) . eq . (mapping of (xsp oep) G)) 
                                 "since $G is ground and unaffected by the substitution."
                                 "Then by $(rule-label 'T-Mapping)," (proves (squish emptyset ";" (xsp Gamma))
                                                                             (typ (xsp e) (xsp G)))))
          ("T-New" (one-case (new C R ep) CR
                             "Then" (eq (xsp e) (new C (list (xsp oR)) (list (xsp oep)))) ". By the induction hypothesis,"
                             (proves emptyset (xsp Gamma) (typ (xsp oep) (xsp oU))) "where" 
                             (proves emptyset Gamma (typ oep oU)) ". By Type Subst. Preserves Subtyping, "
                             (esub (xsp oU) (xsp oV)) "where" (eq (group oV sp of) (fields CR))))
          ("T-Field" (one-case (invoke ep (subi f)) (subi T)
                               "where" (eq (fields (boundD U)) Tf) "and" (dgproves (typ ep U)) ". By the induction hypothesis, "
                               (proves emptyset (xsp Gamma) (typ (xsp ep) (xsp U)))  "There are two subcases:"
                               (case-proof
                                ((eq U (subi X))
                                 (group "Then" (eq (xsp (fields (boundD U))) (subtype (xsp (subi S)) Spi)) "by assumption"
                                        "and" (eq Spi (boundE (xsp U))) ", and because field shadowing is disallowed"
                                        (xsp (fields (boundD U))) subseteq (fields (boundE (xsp U))) 
                                        ". Then by $(rule-label 'T-Field)," (proves emptyset (xsp Gamma) (typ (xsp e) (xsp T)))))
                                ((group (neq U (subi X)) "for any $(math i)")
                                 (group "Then" (eq (boundD U) U) ". Then by definition of $(it 'fields)," 
                                        (eq (xsp (fields U)) (fields (xsp U))) ".  Then by" (rule-label 'T-Field) 
                                        (proves emptyset (xsp Gamma) (typ (xsp e) (xsp T))))
                                 ))))
          ("T-Invk" "This case is almost identical to the previous case, except that although method overriding is allowed, type invariance of methods is required by $(rule-label 'ValidOverride).")
          )))
     
     (define mtype-mbody-lemma
       (lemma (group (it 'mtype) "and" (it 'mbody) "Agree")
              (group "If" (eq (mbody m G) (parens/comma ox e)) "and" (eq (mtype m G) (arrtype oT U)) "then"
                     (proves emptyset (squish (typ this G) "," (typ oX oT)) (typ e Up)) "where" (esub Up U) ".")))
     
     (define mtype-mbody-proof
       (sequence 
         (group "Since the class table is well formed, then from the hypotheses we have that"
                (eq (mbody m G) (parens/comma ox e)) "and" (eq (mtype m G) (arrtype oT U)) 
                "which implies that" (math (simple-method . in . (methods G))))
         (group "Therefore, " (okin (method-def Up m (ov Tp) ox ep) CX) "where"
                (eq G (type-args C V)) "for some $(values (ov v)). Then we have the desired conclusion by lemma"
                "Type Substitution Preserves Typing.")))
     
     (define rn rule-label)
     

     (define Rp (prime R))
     (define Vp (prime V))
     
     (define spt-proof
       (sequence 
         "We prove this by induction over the derivation of $(dgproves (typ e T))."
         (case-proof/rn
          ("T-Var"  (one-case xi Si 
                              "But" (deproves (typ (subi d) (subi U))) "and"
                              (dsub (subi U) Si) ", completing the case."))
                      
          ("T-Class" "Immediate since the expression casted does not impact the type.")
                      
          ("T-Cast" "Immediate since $(eq (xd e) e).")
                         
          ("T-Mapping" (one-case (mapping of oep G) G 
                                 "By the induction hypothesis, all the substitued $ep will"
                                 "have subtypes of their original types, so $(rn 'T-Mapping) applies."))
          
          ("T-New" (one-case (new C R ep) CR
                             "Immediate by the application of the induction hypothesis to $(values oep)."))
                             
                             
          ("T-Field" (one-case (invoke ep (subi f)) (subi T)
                               "Let $(dgproves (typ ep R)).  By the induction hypothesis, $(deproves (typ (xd ep) Rp)) where"
                               (dsub Rp R) ". Then, by the definition of $(it 'fields)," (group (fields R) subseteq (fields Rp)) 
                               ". Therefore, $(rn 'T-Field) applies and $(deproves (typ (xd e) T))."))
                         
          ("T-Invk" (one-case (invoke r m ep) U
                    "Let" (dgproves (typ oep oR)) ". By application of the induction hypothesis, "
                    (deproves (typ (xd oep) (ov Rp))) "where" (dsub (ov Rp) oR) ". Also, let"
                    (dgproves (typ r V)) ". By the induction hypothesis," (deproves (typ (xd r) Vp))
                    "where" (dsub Vp V) ".  But, because methods are not overloaded, and because of the type invariance"
                    "restriction on $(rn 'ValidOverride), if" (eq (mtype m V) (arrtype oT U)) ", then" 
                    (eq (mtype m Vp) (arrtype oT U)) ", completing the case."
                    ) 
                 ))))
     
     (define-syntax case-proof
       (syntax-rules ()
         [(_ (nm body) ...)
          (proof-cases 
           (proof-case nm body) ...)]))
     
     (define-syntax case-proof/rn
       (syntax-rules ()
         [(_ (nm body) ...)
          (proof-cases 
           (proof-case/rn nm body) ...)])) 
     
     (define preservation-proof
       (sequence 
         "We prove this by structural induction on the derivation of $(trans e ep)"
         (case-proof/rn
          ("R-Object" "Immediate.")
          ("R-New" "Immediate from the premises of $(rn 'T-New) and $(rn 'R-New).")
          ("R-Class" "Immediate from the premises of $(rn 'WF-ClassDef) and $(rn 'R-Class).")
          ("R-Cast"
           "By $(rn 'T-Cast), $(e . eq . (cast T phig)) must have type
$(id T).  By $(rn 'T-Mapping), $(ep . eq . phig) must have type
$(id G).  By hypothesis of the reduction rule, $(esub G T).")
          ("R-Field"
           "We know that $(e . eq . (invoke (mapping of od G) (sub f 'i))) and that $(eq ep
(sub d 'i)).  Since $e must have been typed by $(rn 'T-Field), we
know that $((fields G) . eq . Tf) and $(eept e (sub T 'i)).
Further, since $(mapping of od G)  must have been typed by
$(rn 'T-Mapping), we know that $(eept (sub d 'i) S)
where $(esub S T).")
          ("R-Invk" 
           (sequence "We know that $(e . eq . (invoke phig m d)) and that $(ep . eq .
((substitute ox od this phig) (sub e 0))). Further, $e
was typed by $(rn 'T-Invk) to have type $U where $((mtype m G) . eq .
(arrtype oT U)) and $(eept od oTp) and $(esub oTp oT).
 As a premise of $(rn 'R-Invk), we know that $((mbody m G) . eq .
(parens/comma ox (prime (sub e 0))))."
                     
                     (let ((env "$emptyset;$(typ ox oT)$(typ this G)"))
                       "By the lemma (it 'mtype) and (it 'mbody) agree, $(proves env (typ (prime (sub e 0)) Up))
where $(esub Up U).  Then by the lemma Substitution
Preserves Typing, $(eept  (ep . eq . ((substitute ox od
this phig) (sub e 0))) Upp) where $(esub Upp Up).")
                     )
           )
          ("C-Cast"
           "Trivial, since $(eept (cast T e) T) for any $e")
          ("C-Map" "Immediate from the induction hypothesis and the transitivity of subtyping.")
          ("C-New" "Immediate from the induction hypothesis and the transitivity of subtyping.")
          ("C-Arg" "Immediate from the induction hypothesis and the transitivity of subtyping.")
          ("C-Rcvr"
           "We know that $(e . eq . (invoke (sub e 0) m d)) and $(ep . eq . (invoke (prime (sub e 0)) m d)). Further, $e must have been typed by 
$(rn 'T-Invk), which means that $(eept (sub e 0) W) for some ground type $W, and that
$(eept od oV) and $(esub oV oU), and also $((mtype m W) . eq . (arrtype oU T)).  By the induction hypothesis, $(eept (prime e0) Wp) where $(esub
Wp W).  Therefore, by lemma Subtyping Preserves Method Typing,
$((mtype m Wp) . eq . (arrtype oU T)) and thus $(eept (invoke (prime e0) m d) T) by $(rn 'T-Invk).")
          ("C-Field"
           "If $(trans (invoke e (sub f 'i)) (invoke ep (sub f 'i))) then $(trans e ep).
Further, $(invoke e (sub f 'i)) must have been typed by $(rn 'T-Field) to have type 
$(sub T 'i).  Therefore, by the induction hypothesis, $(eept e S) and $(eept ep Sp)
where $(esub S Sp).  Then, by the lemma Fields are Preserved by Subtypes, $((fields Sp)
. eq . (space (fields S) '@ oF)), and by $(rn 'T-Field), $(eept (invoke ep (sub f 'i)) (sub T 'i)).")
          
          )))
     
     (define progress-proof 
       (sequence "We prove this by induction over the derivation of $(eept e S)."
                 (case-proof/rn
                  ("T-Var" "This is a contradiction, since $e is ground")
                  ("T-Class" "In this case $(eq e (prime CS)) where $(prime CS) is ground.  Then lemma  
Agreement of $(it 'field-vals) and $(it 'fields)
$(eq (type-params (prime CS)) XIJ) for some ???.  Further, $((field-vals (typeof (prime CS))) . eq . Tfe) for some $oT, $of and $(id oe).
Therefore, $(rn 'R-Class) applies and $(trans S (mapping of (SpforX (prime CS)) (typeof (prime CS)))).")
                  ("T-Mapping" "Either $e is already a value, or $(e . eq . (mapping of oe G)) where not all of the $oe are values.
Then by the induction hypothesis, there is some $i such that either $(trans (subi e) (subi ep)), in which case
$(rn 'C-Mapping) applies, or $(subi e) contains a bad cast, and the case is complete.")
                  ("T-Cast"
                   (sequence "Here there are three cases:"
                             (itemize
                              "$(eq e (cast S ep)) where $ep is not a mapping.  Then $(rn 'C-Cast) applies." 
                              "$(eq e (cast S ep)) where $(esub T S).  Then $(rn 'R-Cast) applies." 
                              "$(eq e (cast S ep)) where $(proves emptyset (not-subtype T S)).  Then $e is a bad cast." )))
                  ("T-New" "From the antecedent of $(rn 'T-New) the premise of $(rn 'R-New) applies.") 
                  ("T-Invk" 
                   (sequence "Here there are two cases:"
                             (itemize 
                              "$(e . eq . (invoke r m d)) where $r is not a mapping. Then by the induction hypothesis, 
either $r contains a bad cast or $(trans r (prime r)) and $(rn 'C-Rcvr) applies "
                              "$(e . eq . (invoke (sub Phi T) m d))  We know from the antecedent that $((mtype m (boundD T)) . eq .
(arrtype oU V)) and therefore $((mtype m T) . eq . (arrtype oU V)) since $T is ground.  Therefore, since $(it 'mbody)
is defined everywhere $(it 'mtype) is defined, $(eq (mbody m T) (parens/comma ox e0)) for some $ox and $(sub0 e).  
Thus $(rn 'R-Invk) applies.")))
                  ("T-Field" "Here there are two cases, either the reciever is a mapping or not.  In the first, by the antecedent of the typing rule, we can lookup the field successfully and apply $(rn 'R-Field).  Otherwise, we can apply $(rn 'C-Field).")
                  )))
     
     
     (define soundness-proof unproved)
     
     (define soundness-proof-short "Immediate from Subject Reduction and Progress")
     )