(module fool-present (lib "slideshow.ss" "slideshow")

  (require (prefix : (lib "symbol.ss" "texpict")))
  (require "jcode.scm")
  
  (define (jcode/l . args) (page-para (apply jcode args)))

  (define (small t) (text t (current-main-font) (* 2 (quotient (current-font-size) 3))))
  (define (sub t) (text t (cons 'subscript (current-main-font)) (current-font-size)))
  
  (define (many-subitems . bullets)
    (let ((items (map car bullets))
          (subitems (map cadr bullets)))
      (let loop ((si (car subitems))
                 (other-si (cdr subitems))
                 (past-it '())
                 (it (car items))
                 (other-it (cdr items)))
        (cons
         (append
          (map page-item past-it)
          (list* (page-item it)
                 (page-subitem si)
                 (map page-item other-it)))
         (if (null? other-si) '()
             (loop (car other-si) 
                   (cdr other-si)
                   (append past-it (list it))
                   (car other-it)
                   (cdr other-it)))
        ))))
  
  (slide/center
   (titlet "A Core Calculus of Metaclasses")
   (blank)
   (blank)
   (t "Sam Tobin-Hochstadt")
   (t "Eric Allen")
   (blank)
   (small "Sun Microsystems Inc.")
   (small "Northeastern University")
   )
  
  (define outline
    (make-outline 
     
     'motivation
     "Why Metaclasses?"
     #f
     
     'mcj
     "A Simple Language with Metaclasses"
     #f
     
     'benefit
     "An Unexpected Benefit"
     #f
     
     'details
     "Interesting Design Questions"
     #f))
  
  (outline 'motivation)
  
  (slide/title "Why Metaclasses?"
               (page-item "Modeling the World")
               (page-item "Flexible Hierarchies")
               (page-item "Generalized Static Methods")
               ;(page-item "Design Patterns")
               )

  #;(define (jcode str)
    (colorize (tt str) "blue"))
  
  (define fish (standard-fish (* 2 gap-size) gap-size))

  
  (slide/title "The Complex World (Part 1)"
               (page-para (ht-append (t "Consider Harry. ") (bitmap "eagle.JPG")))
               'next
               (page-para "Harry is an eagle." )
               #;(page-para "Now consider" (it "Eaglensis Latinus") "."
                          "This is the species Harry belongs to.")
               'next
               (page-para "This relationship is easy to model in an object-oriented world.")
               (jcode "Harry : Eagle")
               'next
               (page-para "We can easily model other species as well.")
               (page-para/c fish (jcode " : Salmon")))
  
  (slide/title "The Complex World (Part 2)"
               (page-para "In a language with static methods, we can "
                          "even ask this question:")
               (jcode "Eagle.isEndagered()")
               'next
               (page-para "But if" (jcode "Salmon") "is a species, will this work?")
               (jcode "Salmon.isEndangered()")
               'next
               (blank)
               (blank)
               (page-para (it "Who knows?") "We have" (bt "no") 
                          "guarantees about the relationship"
                          "between" (jcode "Salmon") "and" (jcode "Eagle") ".")
               'next 
               (page-para "That's because we can't express relationships"
                          "between classes.")
               )
  
  (slide/title "Subtyping is not enough"
               (page-para "But object-oriented languages do provide a mechanism" 
                          "for relating classes: subtyping!")
               'next
               (page-para "So let's try to use subtyping to express the relationship we"
                          "want. Then we get the following relationships:")
               (blank)
               (jcode "Eagle <: Species")
               (jcode "Salmon <: Species")
               (jcode "Harry : Eagle")
               (blank)
               (page-para "What's wrong here?")
               'next
               (jcode "Harry : Species")
               )
  
  (slide/title "What Do We Want?"
               (page-para "We would like to define a group of entities,"
                          "all of which must respond to certain messages.")
               'next
               (page-para "That sounds an awful lot like a type.")
               (blank) (blank)
               (page-para "What if we could make" (jcode "Species")
                          "the type of" (jcode "Eagle") "?")
               (jcode "Eagle : Species")
               'next
               (page-para "Then we have a guarantee about the behavior of "(jcode "Eagle")
                          ","
                          "since it is an element of" (jcode "Species") ".")
               (page-para "And this guarantee holds for other such elements,"
                          "such as" (jcode "Salmon") ".")
               )

  (slide/title "Modeling Dimensions"
               (jcode "3 meter : Length")
               
               (blank)
               (jcode "5 hours : Time")
               'next
               (blank)
               (page-para "What are Length and Time?")
               'next
               (blank)
               (jcode "Length : Dimension")
               (jcode "Time : Dimension")
               (blank)
               (page-para "To appropriately model dimensions, we need"
                          "to express relationships between classes that are not subtypes.")
               (page-para "See" (it "Object-Oriented Units of Measurement") "in OOPSLA 2004."))

    
  (slide/title "Where are we now?"
               (page-item "We have classes as expressions:")
               (page-subitem (jcode "Eagle.isEndangered()"))
               'next
               (page-item "We have classes that have classes:")
               (page-subitem (jcode "Length : Dimension"))
               'next
               (blank)
               (page-para/c "We have Metaclasses.")
               (blank)
               (page-para "The need for more flexible hierarchies, and constraints on the behavior of classes led us naturally to metaclasses."))
  
  
  (outline 'mcj)
  
  (slide/title "MCJ: A Extension of FGJ with Metaclasses"
               'next
               (page-item "Classes can be used anywhere an expression is expected.")
  ;             (blank) 

               (jcode "Eagle.population() + 7")

               (blank)
               
               'next
               (page-item "Classes have" (jcode "class") "members, which are the methods of the class when used as an expression.")
 ;              (blank)
               
               (jcode "class Eagle { "
                      "    class population() { return pop; }"
                      "}")
               (blank)
               'next
               
               (page-item "Every class has a metaclass (also referred to as" 
                          (it "kind" )"), and is an instance of its metaclass.")
;               (blank)
               (jcode "class Eagle kind Species")

               'next
               (blank)
               (page-item "Classes inherit some of their class methods from their kinds.")
               
               )
  
  (define (page-subitem/color first color . rest)
    (apply page-subitem first (map (lambda (x) (if (string? x)
                                                   (colorize (t x) color)
                                                   (colorize x color))) rest)))
  
  (slide/title "A Simple Example" ; FIXME - REFORMAT!!
               'alts
               (let ((class-c (jcode "class C {"
                                 "    int x;"
                                 "}"))
                     (myclass (jcode "class MyClass kind C {"
                                     "    class int x = 5;"
                                     "    int m(int y) { return y+2; }"
                                     "}") )) 
                 (list 
                  (list (vl-append class-c (ghost myclass)))
                  (list (vl-append class-c  myclass))))
               'next
               (page-para "All of the following are valid expressions:")
               (page-subitem (jcode "C"))
               (page-subitem (jcode "MyClass.x"))
               (page-subitem/color (jcode "mc.m(5)") "blue" "   if" (jcode "mc") 
                            "is an instance of" (jcode "MyClass"))
               (page-subitem/color  (jcode "c.x") "blue" "  if" (jcode "c") "is an instance of "
                            (jcode "C"))
               )
  
  (slide/title "Inheritance"
               (page-para "As in many other language, classes inherit instance"
                          "members from their superclass.")
               (blank)
               'next
               (page-para "But classes also inherit class members from their metaclasses."
                          )
               (page-para "Since classes are instances of their kind, they must inherit the"
                          (it "instance") "members of their kind as" (it "class") 
                          "members.")
               'next
               (page-para "For example, if" (jcode "C") "has kind" (jcode "K") "with the following definitions:")
               (page-para/c (hc-append
                             (jcode "class K {"
                                    "    class int m() { ... }"
                                    "}")
                             (jcode "class C kind K {"
                                    "    class int n() { ... }"
                                    "}")))
               (blank)
               (page-para "Then" (jcode "C") "has two class methods, m and n.")
               )
  
  (slide/title "Object Creation with Constructors"
               (page-para "To create an instance of class C, we call the constructor as follows:")
               (jcode "new(e1)")
               (page-para "which initializes all the fields of class C in order"
                          "and produces an instance of C.")
               'next
               (blank)
               (page-para "For parametric classes," (jcode "new") "can take type parameters.")
               (jcode "new<T>(e1,e2)")
               'next 
               (blank)
               (page-para "In these examples, we didn't specify which class.  We'll see soon why that isn't neccessary.")
               )
  
  (slide/title "Object Creation with Classes"
               (page-para "Since classes are instances of their kinds, declaring a class"
                          "also creates an instance.")
               (page-para "So how do we initialize fields?")
               'next
               (page-para "We have to give values to all" (jcode "class") "fields,"
                          "including those inherited from the kind.")
               'next
               (jcode "class MyClass kind C {"
                                 "    class int x = 5;"
                                 "    int m(int y) { y+2; }"
                                 "}")
               (page-para "We initialize the inherited class field" (jcode "x"))
               )
  
  (let ((item-0 (colorize (page-item/bullet 
                           (colorize (t "0") "blue")
                           "Look in the definition of the class.") "green")))
    (slide/title "Method Dispatch"
               
                 (page-para "Where do we look to find the method to call?")
                 (blank)
                 'alts
                 (list 
                  (list
                   (page-para "For invoking methods on" 
                              (colorize (t "objects created by constructors") "green") ":")
                   (ghost item-0)
                   (page-item/bullet (colorize (t "1") "blue")
                                     "Look in the definition of the class for which" 
                                   "this" (colorize (t"object") "green") "is an instance.")
                 (page-item/bullet (colorize (t "2") "blue")
                                   "Look in the superclass of the class you're looking in.")
                 (page-item/bullet (colorize (t "3") "blue")
                                   "Repeat step 2."))
                (list
                 (page-para "For invoking methods on" 
                            (colorize (t "instance classes") "green") ":")
                 
                  item-0
                 (page-item/bullet (colorize (t "1") "blue")
                                   "Look in the definition of the class for which" 
                                   "this" (colorize (t"class") "green")"is an instance.")
                 (page-item/bullet (colorize (t "2") "blue")
                                   "Look in the superclass of the class you're looking in.")
                 (page-item/bullet (colorize (t "3") "blue")
                                   "Repeat step 2.")))
               'next
               (page-para "Since classes" (it "are") "objects, can these definitions can"
                          "be collapsed?")
               'next
               (page-para (bt "No.")  "Step 0 above has no analogue for"
                          "instances that are not classes.")
               ))
  
  (outline 'benefit)
  
  (slide/title "Rethinking Constructors"
               (page-para "As we have seen, every constructor, as in FGJ,"
                          "must initialize every field.")
               (page-para "Obviously, this is suboptimal.")
               'next
               (page-para "But unlike FGJ, we aren't stuck with this.")
               'next
               (blank)
               (page-para "Class methods give us the ability to define factory methods.")
               (jcode "Point make_origin() { return new (0,0); }")
               )
  
  (slide/title "Mandating Rethinking"
               (page-para "This is such a good idea, it's the first one reccommended in"
                          (it "Effective Java") ".")
               ; maybe a picture of the book here?
               'next
               (page-para "Therefore, we decided to make it mandatory.")
               'next
               (page-para "So, every constructor is private to the class that it constructs."
                          "Any other creation of objects must go through a factory method."))
  
  (slide/title "Design Patterns in the Language"
               (page-para "Factory Pattern")
               (page-subitem "We just saw it.")
               'next
               (page-para "Singleton Pattern :")
               (jcode "class MySingleton kind C { ... }")
               'next 
               (page-para "Prototype Pattern") 
               )
  

  
  (outline 'details)
  
  (slide/title "typeOf"
               (page-para "What is the type of the expression" (jcode "C") "?")
               'next
               (page-para "Can we just use the kind of C?")
               'next
               (page-para "No.")
               (vl-append
                (jcode "class D {}"
                       " "
                       "class C kind D {"
                       "    class int m() { ... }"
                       "}"))
               (blank)
               (page-para "Now" (jcode "C.m()") "will fail to typecheck.")
               'next
               (page-para "We need some way of referring to just the type of" (jcode "C"))
               (page-para "We refer to this type as" (jcode "typeOf[C]")))
  
  (slide/title "Generics and Metaclasses"
               (page-para "Do metaclasses have implications for the use of "
                          "parametric polymorphism?")
               (page-para "If T is a type variable, how do we typecheck")
               (jcode "T.m()")
               'next
               (page-para "We need to add bounds on the kind of type variables."))
  

  (slide/title "Related Work"
               'alts
               (many-subitems 
                (list "ObjVLisp"
                      "Very similiar model, without types")
                (list "Smalltalk"
                      "Restricted levels")
                (list "MOP"
                      "???")
                (list "Python"
                      "Similar to ObjVLisp, no published semantics")
                (list "SOL?"
                      "IBM Language from 1990's")
                (list "OOPSLA 2004"
                      "Insipration for this work, but no semantics")))
               
  #;(slide/title "Related Work"
               (page-item "ObjVLisp")
               (page-subitem "Very similiar model, without types")
               (page-item "Smalltalk")
               (page-subitem "Restricted levels")
               (page-item "MOP")
               (page-subitem "???")
               (page-item "Python")
               (page-subitem "Similar to ObjVLisp, no semantics given")
               (page-item "SOL?") ;; FIXME
               (page-subitem "IBM Language from early 90's")
               (page-item "OOPSLA 2004") ;; FIXME
               (page-subitem "Inspiration for this work, but not a semantics")
               ) 
  
  (slide/title "Formalism"
               (page-para "A simple extension of Featherweight GJ")
               (blank)
               (page-item "The only significant increase in complexity in the formalism results from classes as expressions.")
               'next
               (page-subitem "Which is even present in Java!")
               'next
               (page-item "The proof of soundness is not much more complex than for FGJ.")
               'next
               (blank)
               (page-para "Metaclasses are not that complicated!"))
  
  (slide/title "Problems and Future Work"
               (page-item "Adding mutable state would require some work. ")
               (page-item "Our constructor reform does badly for initializing superclass fields.")
               (page-item "Implementation"))
  
  (slide/title "Conclusions"
               (page-item "We've shown why metaclasses are benefical for an OO language.")
               (page-item "We have presented a way to extend a language with metaclasses.")
               (page-item "We have discovered that metaclasses can make constructors much simpler.")
               (page-item "We formalized our calculus, and it wasn't that bad.")
               )
  
  (slide/center
   (bt "Thank You"))
  
  (slide/center
   (t "Auxilliary Slides"))
  
  (slide/title "Species in Java"
               (jcode/l "class Species { ... }")
               (jcode/l "Species theEagle = new Species()")
               (jcode/l "Species theSalmon = new Species()")
               (jcode/l "class Eagle { ... }")
               (jcode/l "Eagle harry = new Eagle()")
               (blank)
               'next
               'alts
               (list
                (list (page-para "How many invariants are there in this code?"))
                (list (page-para "How many invariants are there in this code : 4"))) ; FIXME
               ) 
  )