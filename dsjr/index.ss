(require (lib "unitsig.ss")
         (lib "servlet-sig.ss" "web-server")
         (lib "finddoc.ss" "help")
         (lib "framework.ss" "framework")
         (lib "xml.ss" "xml"))

(unit/sig ()
  (import servlet^)

; (send/finish  
 
 `(HTML ()
	 (TITLE ()
	 "PLT Help Desk")
         (H1 () "PLT Help Desk")
  
         (UL ()
             (LI ()
                 (B ()
                    (A ((HREF "howtouse.html")) "Help Desk"))
                 ":  How to find help"))
         
         (UL ()
             (LI ()
                 (B ()
                    (A ((HREF "howtoscheme.html")) "Software"))
                 ": How to run programs"
                 (BR)
                 'nbsp 'nbsp 'nbsp 'nbsp 'nbsp 'nbsp
                 (FONT ((SIZE "-2"))
                       (A ((HREF "tour/index.html")) "Tour") ","
                       (A ((HREF "scheme/what.html")) "Languages") ","
                       (A ((HREF "../../help/manuals.html")) "Manuals") ","
                       (A ((HREF "releaseinfo.html")) "Release") ","
                       ,(xml->xexpr (document-element (read-xml (open-input-string (finddoc "drscheme" "frequently asked questions" "FAQ")))))
                       "...")))
         
         (UL ()
             (LI ()
                 (B ()
                    (A ((HREF "howtoprogram.html")) "Program Design"))
                 ": Learning to program in Scheme"             
                 (BR) 'nbsp 'nbsp 'nbsp 'nbsp 'nbsp 'nbsp 
                 (FONT ((SIZE "-2"))
                       (A ((HREF "../teachpack/index.html")) "Teachpacks") ","
                       (A ((HREF "research/why.html")) "Why DrScheme?") ","
                       "...")))
         
         (UL ()
             (LI ()
                 (B () 
                    (A ((HREF "resources.html")) "External Resources")) 
                 ": Additional information"
                 
                 (BR)
                 'nbsp 'nbsp 'nbsp 'nbsp 'nbsp 'nbsp 
                 (FONT ((SIZE "-2"))
                       (A ((HREF "resources/teachscheme.html")) "TeachScheme!") ","
                       (A ((HREF "resources/libext.html")) "Libraries") ","
                       (A ((HREF "resources/maillist.html")) "Mailing List") ","
                       "...")))
         (P)
         
         'nbsp 'nbsp 'nbsp
         (B ()
            (A ((HREF "acknowledge.html"))
               (FONT ((COLOR "lime green"))
                     "Acknowledgements")))
         'nbsp 'nbsp 'nbsp
         (B ()
            (A ((HREF "junk.html")) (FONT ((COLOR "lime green")) "Submit a bug report")))
         
         (P)
         
         (I () "Version:" ,(version:version))))  
  