#cs(module simple-sem mzscheme
     (require "scheme-tex.scm")
     (require "semantics-helper.scm" "sem-rules.scm" "sem-proofs.scm")
     (require (lib "quasistring.ss" "quasistring"))
     (require (lib "etc.ss") (lib "list.ss") (lib "match.ss"))
          
     (define the-document
       (tex 
        "simple-sem.tex"
        (documentclass 'article 10)
        (packages 'amssymb 'graphicx 'fullpage)
        (input "semantics-macros.tex" "semantics-rules.tex" "semantics-proofs.tex")
        (title "Formal Semantics for Core Fortress with Traits")
        (author "Sun PLRG")
        
        (document
         (section "Preliminaries"
           (section "Metavariables" metavars)
           (section "Syntax"
             fortress-syntax)

           (newpage)
           )
         (section "Evalution"
           (section "Congruence Rules"
             (rule-line "Rules for congruence")
             (rule-line cong-field cong-meth cong-new)
             (rule-line cong-arg cong-map cong-cast)
             (qs "$oee means one of the $e's step.")
             )
           (section "Reduction Rules"
             (rule-line comp-obj comp-field)
             (rule-line comp-new comp-class)
             (rule-line comp-cast comp-meth)
             )
           )
         (newpage)
         (section "Typing"
           (section "Subtyping"
             (rule-line "Subtyping rules")
             (rule-line subtype-refl)
             (rule-line subtype-var subtype-trans)
             (rule-line subtype-inter subtype-kind)
             (rule-line subtype-impl subtype-super)
             (rule-line subtype-cimpl)
             )
           (section "Type Bounds"
             (rule-line bound-var  bound-class  bound-typeof))
           (section "Well-Formed Constructs"
             (rule-line "Well-formedness checks")
             (rule-line object-ok typeof-ok var-ok)
             (rule-line classref-ok)
             (rule-line method-ok)
             (rule-line classdef-ok)
             )
           (section "Expression Typing"
             (rule-line "Rules for typing expressions.")
             (rule-line type-var type-cast type-class)
             (rule-line type-field type-map)
             (rule-line type-invk)
             (rule-line type-new)
             )
           )
         (section "Auxilliary Functions"
           (section "Field Lookup"
             (rule-line fields-obj fv-obj fv-class)
             (rule-line fields-class)
             (rule-line fields-typeof)
             (rule-line fv-typeof)
             )
           (section "Method Lookup"
             (rule-line mtype-def mbody-def)
             (rule-line methods-obj)
             (rule-line methods-class)
             (rule-line methods-typeof)
             )
           (section "Overriding"
             (rule-line override-def))
           (section "Paramaters"
             (rule-line params-class params-typeof))
           (section "Super"
             (rule-line super-class super-typeof))
           )
         (newpage)
         (section "Soundness Proof"
           (section "Subject Reduction"
             (preservation preservation-proof)
             )
           
           (section "Progress"
             (progress progress-proof)
             )
           
           (section "Type Soundness"
             (soundness soundness-proof-short)
             )
           
           (section "Lemmas"
             typeSubstSubtypeLemma
             typeSubstSubtypeProof
             (type-sub-preserves-typing tspt-proof)
             (substitution-preserves-typing spt-proof)
             fieldsPreservedLemma
             fieldsPreservedProof
             substDistFieldsLemma
             substDistFieldsProof
             methodTypingLemma
             methodTypingProof
             (mtype-mbody-lemma mtype-mbody-proof)
             methodsDefinedLemma
             (predef0 'methodsDefinedProof)
             substOKLemma
             substOKProof
             fieldsAgreeLemma
             (predef0 'fieldsAgreeProof)
             )
           )
         )))
     )
   