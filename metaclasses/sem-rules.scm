#cs(module sem-rules (lib "qstr-lang.ss" "quasistring")
     (require "semantics-helper.scm")
     (require "scheme-tex.scm")
     (require (lib "etc.ss") )
     (require (lib "list.ss"))
     (require (lib "match.ss"))
     
     (provide (all-defined))
     
     (define metavars
       (itemize
        "Expressions or mappings: $e, $d, $r"
        "Field names: $f, $g"
        "Variables: $x"
        "Method names: $m"
        "Values: $v"
        "Method definitions: $M, $N"
        "Type names: $C, $D"
        "Types: $I, $J, $K, $U, $V, $W"
        "Non-$(txt 'typeOf) types: $O, $P ,$Q, $R, $S"
        "Types that are $|Object| or a type application: $A, $B"
        "Ground types (contain no type variables): $G"
        "Type variables: $X, $Y, $Z"
        "Mappings (field name $(math mapsto) value): $|Phi|"
        ))
     
     (define grammar-rule 
       (match-lambda*
         [(nt rhs name) (list nt production rhs (textrm name))]
         [(rhs name) (list "" "|" rhs (textrm name))]))
     
     (define fortress-syntax
       (math 
        (array "rcll"
               (list
                (grammar-rule CL full-class-syntax "class declaration")
                (grammar-rule I full-interf-syntax "interface definition")
                (grammar-rule M simple-method-syntax "method defintion")
                (grammar-rule e x "variable reference")
                (grammar-rule (invoke e f) "field access")
                (grammar-rule (invoke e m oe) "method invocation")
                (grammar-rule (new C r e) "instance creation")
                (grammar-rule (cast T e) "cast")
                (grammar-rule R "type reference")
                (grammar-rule T R "non-typeof type")
                (grammar-rule (typeof R) "typeof application")
                (grammar-rule R X "type variable")
                (grammar-rule A "")
                (grammar-rule A (type-args C R) "type application")
                (grammar-rule Object "")
                )
               )
        ))
     
     ; Subtyping rules
     
     (define (subtype-rule cl class a b name)
       (rule name 
             (eq (CT cl) class)
             (dproves (subtype a b))))
     
     (define-values (subtype-rule-c subtype-rule-i)
       (values
        (lambda (a b n)
          (subtype-rule C simple-class a b n))
        (lambda (a b n)
          (subtype-rule I simple-interf a b n))))
     
     (define subtype-refl
       (rule "S-Reflex" (dproves (subtype T T))))
     
     (define subtype-var
       (rule "S-Var" 
             (in (math (space X super-sym T)) Delta)
             (dproves (subtype X T))))
     
     (define subtype-trans
       (rule "S-Trans"
             (harray (dproves (subtype V T)) (dproves (subtype T U)))
             (dproves (subtype V U))))
     
     
     (define subtype-super (subtype-rule-c CS (SforX A) "S-Super"))
     (define subtype-inter (subtype-rule-i IS (SforX J) "S-Inter"))
     (define subtype-inter-kind (subtype-rule-i (typeof IS) (SforX A) "S-Inter-Kind"))
     (define subtype-kind (subtype-rule-c (typeof CS) (SforX B) "S-Kind"))
     (define subtype-impl (subtype-rule-c CS (SforX I) "S-Impl"))
     (define subtype-cimpl (subtype-rule-c (typeof CS) (SforX Ip) "S-CImpl"))
     
     ; type bounds
     
     (define bound-var (eq (boundD X) (Del X)))
     (define bound-typeof (eq (boundD (typeof X)) (Del (typeof X))))
     (define bound-class (eq (boundD N) N))
     
     ; Well-formedness rules
     
     (define (dprovesok a) (dproves (ok a)))
     (define (dprovesokin a b) (dproves (okin a b)))
     
     (define object-ok (rule "WF-Object" (dprovesok Object)))
     
     (define typeof-ok (rule "WF-TypeOf" (dprovesok T) (dprovesok (typeof T))))
     
     (define var-ok (rule "WF-Var" (dproves (subtype X T)) (dprovesok X)))
     
     (define classref-ok (rule "WF-Class" 
                               (eq (CT C) simple-class)
                               (harray
                                (dproves (subtype oS (SforX oI)))
                                (dproves (subtype (typeof oS) (SforX oJ)))
                                (dprovesok oS))
                               (dprovesok CS)))
     
     (define delta-def (eq Delta (squish (group oX super-sym oI) "," (group (typeof oX) super-sym oJ))))
     
     (define method-ok
       (rule "WF-Method"
             (eq (type-params G) (math (group oX impl-sym (parens oI ", " oJ))))
             (harray delta-def (eq Gamma (group (typ ox oT) ", " (typ this G))))
             (harray (dprovesok oT) (dprovesok U) (override m (super G) (arrtype oT U)))
             (harray (dgproves (typ e W)) (dproves (subtype W U)))
             (okin simple-method G)))
     
     (define classdef-ok
       (rule "WF-ClassDef"
             (harray (okin oM  (typeof CX)) (okin oN CX)  delta-def)
             (harray (dprovesok B)(dprovesok A)(dprovesok I)(dprovesok J)(dprovesok oT) (dprovesok oW))
             (harray (group (fields B) subseteq Tf) (proves (squish Delta ";" emptyset) (typ oe oTp)) (esub oTp oT))
             (squish forall sp (in (new D S d) (apply squish (interleave ", " (list oe oM oN)))) "." sp sp (eq D C))
             (ok full-class)))
     
     
     ; congruence rules
     
     (define (cong-templ e a b nm)
       (rule nm
             (trans e (prime e))
             (trans a b)))
     
     (define cong-field (cong-templ e (invoke e f) (invoke ep f) "C-Field"))
     (define cong-meth (cong-templ e (invoke e m d) (invoke ep m d) "C-Rcvr"))
     (define cong-arg (cong-templ oe (invoke d m e) (invoke d m ep) "C-Arg"))
     (define cong-new (cong-templ e (new C S e) (new C S ep) "C-New"))
     (define cong-cast (cong-templ e (cast T e) (cast T ep) "C-Cast"))
     (define cong-map (cong-templ oe (mapping of oe G) (mapping of oep G) "C-Map"))
     
     ; reduction rules
     
     (define comp-new (rule "R-New"
                            (eq (fields CS) Tf)
                            (trans (new C S e) (mapping of oe CS))))
     
     (define comp-obj (rule "R-Object" (trans Object (sub (braces "") Object))))
     
     
     (define comp-field (rule "R-Field" (trans (invoke phig f) (phiof G f))))
     
     (define comp-cast (rule "R-Cast" (esub G T) (trans (cast T phig) phig)))
     
     (define comp-meth (rule "R-Invk" 
                             (eq (mbody m G) (parens/comma ox (sub e 0)))
                             (trans (invoke phig m d) ((substitute ox od this phig) (sub e 0)))))
     
     (define comp-class (rule "R-Class"
                              (eq (field-vals (typeof CS)) Tfe)
                              (trans CS (mapping of oe (typeof CS)))))
     
     ; expression typing
     
     (define dgtyp (compose dgproves typ))
     ;(define dsub (compose dproves subtype))
     
     (define type-var (rule "T-Var"
                            (dgtyp x (Gam x))))
     
     (define type-cast (rule "T-Cast"
                             (dprovesok T)
                             (dgtyp e U)
                             (dgtyp (cast T e) T)))
     
     (define type-field (rule "T-Field"
                              (dgtyp e U)
                              (eq (fields (boundD U)) Tf)
                              (dgtyp (invoke e (sub f "i")) (sub T "i"))))
     
     (define type-map (rule "T-Mapping"
                            (eq (fields G) Tf)
                            (harray (dgtyp oe oS) (dsub oS oT))
                            (dgtyp (mapping of oe G) G)))
     
     (define type-invk (rule "T-Invk"
                             (eq (mtype m (boundD W)) (arrtype oU oT))
                             (harray (dgtyp r W)
                                     (dgtyp oe oV)
                                     (dsub oV oU))
                             (dgtyp (invoke r m e) T)))
     
     (define type-class (rule "T-Class"
                              (dprovesok S)
                              (dgtyp S (typeof S))))

     (define type-new (rule "T-New"
                            (harray (dprovesok CS)
                                    ((fields CS) . eq . Tf))
                            (harray (dsub oU oT) (dgtyp oe oU))
                            (dgtyp (new C S e) CS)))
     
     ; fields() and field-vals()
     
     (define fields-obj (rule "F-Object"
                              (eq (fields Object) emptyset)))
     (define fv-obj (rule "FV-Object"
                              (eq (field-vals Object) emptyset)))
     (define fv-class (rule "FV-Class"
                              (eq (field-vals CS) emptyset)))
     (define fields-class (rule "F-Class"
                             (eq (CT C) full-class)
                             (eq (fields (RforX A)) (space oU oh))
                             (eq (fields CR) (space oU oh cup (RforX oW) og))))
                              
     (define fv-typeof (rule "FV-Typeof"
                             (eq (CT C) full-class)
                             ((field-vals (typeof CR)) . eq . (RforX Tfe))))

     (define fields-typeof (rule "F-Typeof"
                             (eq (CT C) full-class)
                             ((fields (typeof CR)) . eq . (RforX Tf))))
     
     ; mtype() and mbody() and methods()
     
     (define (mdef a b nm) (rule nm (simple-method . in . (methods G)) (eq a b)))
     
     (define mtype-def (mdef (mtype m G) (arrtype oT oU) "MType"))
     
     (define mbody-def (mdef (mbody m G) (parens/comma ox oe) "MBody"))

     (define methods-obj (rule "MethodsObject" (eq (methods Object) emptyset)))
     
     (define methods-class (rule "MethodsClass" 
                                 ((CT C) . eq . full-class)
                                 ((methods CR) . eq . (space (RforX oN) cup (methods (RforX A))))))
     
     (define methods-typeof (rule "MethodsTypeof"
                                  ((CT C) . eq . full-class)
                                  ((methods (typeof CR)) . eq . (space (RforX oM) cup (methods (RforX B))))))
     
     ; override
     
     (define override-def (rule "Override"
                                (space ((mtype m G) . eq . (arrtype oU oV))
                                       (textrm "implies")
                                       (eq oU oW)
                                       (textrm "and")
                                       (eq oT oV))
                                (override m G (arrtype oW oT))))
     
     ; super

     (define super-class (rule "Super"
                               (eq (CT C) simple-class)
                               (eq (super CS) A)))
       
     (define super-typeof (rule "SuperTypeof"
                               (eq (CT C) simple-class)
                               (eq (super (typeof CS)) B)))
     ; params
     
     (define params-class (rule "Params"
                                (eq (CT C) simple-class)
                                (eq (type-params CS) XIJ)))
     
     (define params-typeof (rule "ParamsTypeof"
                                (eq (CT C) simple-class)
                                (eq (type-params (typeof CS)) XIJ)))
     
     
     
     
     )
   