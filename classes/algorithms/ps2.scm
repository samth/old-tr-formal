(require "../../scheme-tex.scm")
(require (planet "quasistring.ss" ("jacob" "quasistring.plt" 1 0)))
(require (lib "etc.ss") (lib "list.ss") (lib "match.ss"))

(define ps2
  (tex 
   "ps2.tex"
   (documentclass 'article 12)
   (title "Problem Set 2")
   (author "Sam Tobin-Hochstadt")
   (document
    (section "Problem 1"
	     (group "Consider a decision tree for a comparison sorting algorithm applied to a"
		    "list of $n$ elements.  If this algorithm was linear for half of the possible"
		    "inputs, then "))
    (section "Problem 2"
	     (group "Paste in stuff here."))
    (section "Problem 3")
    (section "Problem 4")
    (section "Problem 5")
    (section "Problem 6")
    (section "Problem 7")
    )
   ))