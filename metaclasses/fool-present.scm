(module fool-present (lib "slideshow.ss" "slideshow")

  ;(require (prefix : (lib "symbol.ss" "texpict")))
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
          (if si
              (list* (colorize (page-item it) "blue")
                 (page-subitem si)
                 (map page-item other-it))
              (list* (colorize (page-item it) "blue")
                     (map page-item other-it))))
         
         (if (null? other-si) 
             '()
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

   (ht-append 
    (vc-append
     (t "Sam Tobin-Hochstadt")
     (ghost (t "blank"))
     (small "Northeastern University")
     (small "Sun Microsystems Inc."))
    (ghost (t "blank"))
    
    (vc-append
     (t "Eric Allen")
     (ghost (t "blank"))
     (small "Sun Microsystems Inc.")))


   )
  
  ;(outline 'motivation)
  
  
  (slide/center (titlet "Why Metaclasses?"))
  
  #;(slide/title "Why Metaclasses?"
               (page-item "Modeling the World")
               (page-item "Flexible Hierarchies")
               (page-item "Generalized Static Methods")
               ;(page-item "Design Patterns")
               )

  (define fish (standard-fish (* 2 gap-size) gap-size))

  
  (slide/title "The Complex World (Part 1)"
               (page-para (ht-append (t "Consider Harry. ") (bitmap "eagle.JPG")))
               ;'next
               (page-para "Harry is an eagle." )
               ;'next
               (page-para "This relationship is easy to model in an object-oriented world.")
               (jcode "Harry : Eagle")
               'next
               (page-para "We can easily model other species as well.")
               (page-para/c fish (jcode " : Salmon")))
  
  (slide/title "The Complex World (Part 2)"
               (page-para "In a language with static methods, we can "
                          "even ask this question:")
               (jcode "Eagle.isEndangered()")
               ;'next
               (page-para "But if" (jcode "Salmon") ", like "(jcode "Eagle")", is a species, will it also have an"
                          (jcode "isEndangered()") "method?")
               'next
               (blank)
               (blank)
               (page-para (it "Who knows?") "We have" (bt "no") 
                          "guarantees about the relationship"
                          "between" (jcode "Salmon") "and" (jcode "Eagle") ".")
               ;'next 
               (page-para "This is because we can't express the fact that they are both species.")
               )
  
  (slide/title "Subtyping is not enough"
               (page-para "But object-oriented languages do provide a mechanism" 
                          "for relating classes: subtyping!")
               ;'next
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
               ;'next
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
               ;'next
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
  
      (slide/title "The Current State of the Art"
                   (page-para "In many languages we can already give behavior to classes"
                              "as opposed to instances:")
                   'alts
                   (list
                    (list
                     (page-subitem "Static Methods")
                     (page-subitem "Constructors"))
                    (list
                     (page-subitem "Static Methods - Global Variables in Disguise!")
                     (page-subitem "Constructors - Complicated and Anomolous!"))
                    )
                   (blank)
                   'next
                   (page-para "Static behavior is important, but it needs to be done in a principled way."
                              "Metaclasses offer us a way to do that."))
  ;(outline 'mcj)
  
  (slide/center (titlet "A Simple Language With Metaclasses"))
  
  (slide/title "MCJ: A Extension of FGJ with Metaclasses"
               'next
               (page-item "Classes can be used anywhere an expression is expected.")
               (jcode "Eagle.population() + 7")
               (blank)
               'next
               (page-item "Classes have" (jcode "static") "members, which are the methods"
                          "of the class when used as an expression.")
               (jcode "class Eagle { "
                      "    static population() { return popl; }"
                      "}")
               (blank)
               'next
               (page-item "Every class has a metaclass (also referred to as" 
                          (it "kind" )"), and is an instance of its metaclass.")
               (jcode "class Eagle kind Species")
               'next
               (blank)
               (page-item "Classes inherit some of their static methods from their kinds.")
               )
  
  (define (page-subitem/color first . rest)
    (apply page-subitem first (map (lambda (x) (if (string? x)
                                                   (colorize (t x) "blue")
                                                   (colorize x "blue"))) rest)))
  
  (slide/title "A Simple Example"
               (let ((class-c (jcode "class C {"
                                 "    int x;"
                                 "}"))
                     (myclass (jcode "class MyClass kind C {"
                                     "    static int x = 5;"
                                     "    int m(int y) { return y+2; }"
                                     "}") )) 
                  
                 (vl-append class-c  myclass))
               'alts
               (list
                (list (page-para "All of the following are valid expressions:")
                      (page-subitem (jcode "C"))
                      (page-subitem (jcode "MyClass.x"))
                      (page-subitem/color (jcode "mc.m(5)") " -- if" (jcode "mc") 
                                          "is an instance of" (jcode "MyClass"))
                      (page-subitem/color  (jcode "c.x")  " -- if" (jcode "c") "is an instance of "
                                           (jcode "C")))
                (list
                 (page-para "All of the following are" (bt "invalid") ":")
                 (page-subitem/color (jcode "MyClass.m(5)") " --" (jcode "m") "is an instance method")
                 (page-subitem/color (jcode "C.x") " --" (jcode "x") "is an instance field of" (jcode "C"))
                 (page-subitem/color (jcode "mc.x") " --" (jcode "x") "is a static field of" (jcode "MyClass"))))
               )
  
  (slide/title "Inheritance"
               (page-para "As in many other languages, classes inherit instance"
                          "members from their superclass.")
               (blank)
               'next
               (page-para "But classes also inherit static members from their metaclasses."
                          )
               (page-para "Since classes are instances of their kind, they must inherit the"
                          (it "instance") "members of their kind as" (it "static") 
                          "members.")
               'next
               (page-para "For example, if" (jcode "C") "has kind" (jcode "K") "with the following definitions:")
               (page-para/c (hc-append
                             (jcode "class K {"
                                    "    int m() { ... }"
                                    "}")
                             (jcode "class C kind K {"
                                    "    static int n() { ... }"
                                    "}")))
               (blank)
               (page-para "Then" (jcode "C") "has two static methods, m and n.")
               )
  
  (slide/title "Object Creation with Constructors"
               (page-para "To create an instance of class C, we call the constructor as follows:")
               (jcode "new C(e1)")
               (page-para "which initializes all the fields of class C in order"
                          "and produces an instance of C.")
               'next
               (blank)
               (page-para "For parametric classes," (jcode "new") "can take type parameters.")
               (jcode "new D<T>(e1,e2)")
               )
  
  (slide/title "Object Creation with Classes"
               (page-para "Since classes are instances of their kinds, declaring a class"
                          "also creates an instance.")
               (page-para "So how do we initialize fields?")
               'next
               (page-para "We have to give values to all" (jcode "static") "fields,"
                          "including those inherited from the kind.")
               'next
               (jcode "class MyClass kind C {"
                                 "    static int x = 5;"
                                 "    int m(int y) { y+2; }"
                                 "}")
               (page-para "We initialize the inherited static field" (jcode "x"))
               )
  
  (let ((item-0 (colorize (page-item/bullet 
                           (colorize (t "0") "blue")
                           "Look in the definition of the class.") "blue")))
    (slide/title "Method Dispatch"
               
                 (page-para "Where do we look to find the method to call?")
                 (blank)
                 'alts
                 (list 
                  (list
                   (page-para "For invoking methods on" 
                              (colorize (t "objects created by constructors") "blue") ":")
                   (ghost item-0)
                   (page-item/bullet (colorize (t "1") "blue")
                                     "Look in the definition of the class for which" 
                                   "this" (colorize (t"object") "blue") "is an instance.")
                 (page-item/bullet (colorize (t "2") "blue")
                                   "Look in the superclass of the class you're looking in.")
                 (page-item/bullet (colorize (t "3") "blue")
                                   "Continue up the superclass hierarchy."))
                (list
                 (page-para "For invoking methods on" 
                            (colorize (t "instance classes") "blue") ":")
                 
                  item-0
                 (page-item/bullet (colorize (t "1") "blue")
                                   "Look in the definition of the class for which" 
                                   "this" (colorize (t"class") "blue") "is an instance.")
                 (page-item/bullet (colorize (t "2") "blue")
                                   "Look in the superclass of the class you're looking in.")
                 (page-item/bullet (colorize (t "3") "blue")
                                   "Continue up the superclass hierarchy.")))
               
               ))
  
  (slide/center (titlet "An Unexpected Benefit"))
  ;(outline 'benefit)
  
  (slide/title "Rethinking Constructors"
               (page-para "As we have seen, every constructor, as in FGJ,"
                          "must initialize every field.")
               (page-para "Obviously, this is suboptimal.")
               'next
               (page-para "But unlike FGJ, we aren't stuck with this.")
               'next
               (blank)
               (page-para "Static methods give us the ability to define factory methods.")
               (jcode "static Point make_origin() { return new (0,0); }")
               )
  
  (slide/title "Mandating Rethinking"
               (page-para "This is such a good idea, it's the first one reccommended in"
                          (it "Effective Java") ".")
               (page-para "Therefore, we decided to make it mandatory.")
               'next
               (page-para "So, every constructor is private to the class that it constructs."
                          "Any other creation of objects must go through a factory method."))
  (slide/title "Why is this an Advantage?"
               (page-para "What have we gained over factory methods in other languages?")
               (page-subitem "We can construct instances of type variables easily.")
               (page-subitem "We can pass around factories without tricks.")
               (page-subitem "We have static checking on the methods of a factory.")
               (page-subitem "We've greatly simplified the system for constructors."))
  
  (slide/title "Design Patterns in the Language"
               (page-para "Factory Pattern")
               (page-subitem "We just saw it.")
               'next
               (page-para "Singleton Pattern :")
               (jcode "class MySingleton kind C { ... }")
               'next 
               (page-para "Prototype Pattern")
               (page-subitem "Kinds resemble prototype classes.")
               )
  

  
  ;(outline 'details)
  
  (slide/center (titlet "Two Important Details"))
  
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
                       "    static int m() { ... }"
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
               (page-para "We need to add bounds on the kind of type variables.")
               (jcode "class C<T extends S kind K> { ... }")
               (page-para "This means that it's now possible to use static methods and"
                          "construct instances of type variables.")
               (page-subitem "Even without first-class generics"))

  (slide/center (titlet "Where Are We Now?"))


  
               
  
  
  (slide/title "Formalism"
               (page-para "A simple extension of Featherweight GJ")
               (blank)
               (page-item "The type soundness theorem is unchanged.")
               (page-item "The only significant increase in complexity in the formalism results from classes as expressions.")
               ;'next
               (page-subitem "Which is even present in Java!")
               ;'next
               (page-item "The proof of soundness is not much more complex than for FGJ.")
               'next
               (blank)
               (page-para "Metaclasses are not that complicated!"))
  
  (slide/title "Problems and Future Work"
               (page-item "Adding mutable state would require some work. ")
               (page-item "Just as in FGJ, superclass fields are a problem")
               (page-item "Implementation"))
  
  (slide/title "Related Work"
               'alts
               (many-subitems 
                (list "ObjVLisp"
                      "Very similiar model, without types")
                (list "Smalltalk"
                      "Restricted levels")
                (list "MOP"
                      #f)
                (list "Python"
                      "Similar to ObjVLisp, no published semantics")
                (list "IBM SOM"
                      "Dynamic Class Creation, Meta-Object Protocol")
                (list "Allen, Chase, Luchangco, Maessen and Steele - OOPLSA 2004"
                      "Insipration for this work, but no semantics")))
  
  (slide/title "Conclusions"
               (page-item "We've shown why metaclasses are benefical for an OO language.")
               (page-item "We have presented a way to extend a language with metaclasses.")
               (page-item "We have discovered several ways that metaclasses can make object creation simpler.")
               (page-item "We formalized our calculus, and proved it sound.")
               )
  
  (slide/center
   (bt "Thank You")
   (blank)
   (t "samth@ccs.neu.edu")
   (t "http://research.sun.com/project/plrg"))
  
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