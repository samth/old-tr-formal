(module fool-present (lib "slideshow.ss" "slideshow")

  (require (prefix : (lib "symbol.ss" "texpict")))
  (require "jcode.scm")

  (define (small t) (text t (current-main-font) (* 2 (quotient (current-font-size) 3))))
  (define (sub t) (text t (cons 'subscript (current-main-font)) (current-font-size)))
  
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
               (page-item "Generalized Statics")
               ;(page-item "Design Patterns")
               )

  #;(define (jcode str)
    (colorize (tt str) "blue"))
  
  (define fish (standard-fish (* 2 gap-size) gap-size))

  
  (slide/title "The Complex World (Part 1)"
               (page-para (ht-append (t "Consider Harry. ") (bitmap "eagle.JPG")))
               'next
               (page-para "Harry is an eagle." )
               #;(page-para "Now consider " (it "Eaglensis Latinus") "."
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
               (page-para "But if " (jcode "Salmon") "is a species, will this work?")
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
               (page-para "What if we could make " (jcode "Species")
                          "the type of " (jcode "Eagle") "?")
               (jcode "Eagle : Species")
               'next
               (page-para "Then we have a guarantee about the behavior of "(jcode "Eagle")
                          ","
                          "since it is an element of " (jcode "Species") ".")
               (page-para "And this guarantee holds for other such elements,"
                          "such as " (jcode "Salmon") ".")
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
               (page-para "See " (it "Object-Oriented Units of Measurement") "in OOPSLA 2004."))

    
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
               (page-item "Classes have " (jcode "class") "members, which are the methods of the class when used as an expression.")
 ;              (blank)
               
               (jcode "class Eagle { "
                      "    class population() { return pop; }"
                      "}")
               (blank)
               'next
               
               (page-item "Every class has a metaclass (also referred to as " 
                          (it "kind" )")")
;               (blank)
               (jcode "class Eagle kind Species")

               'next
               (blank)
               (page-item "Classes inherit some of their class methods from their kinds.")
               
               )
  
  (slide/title "Object Creation with Constructors"
               (page-para "To create an instance of class C, we call the constructor as follows:")
               (jcode "new(e1,e2)")
               (page-para "which initializes all the fields of class C in order"
                          "and produces an instance of C.")
               'next
               (blank)
               (page-para "For parametric classes, " (jcode "new") "can take type parameters.")
               (jcode "new<T>(e1,e2)")
               'next 
               (blank)
               (page-para "In these examples, we didn't specify which class.  We'll see soon why that isn't neccessary.")
               )
  
  (slide/title "Object Creation with Classes")
  
  (slide/title "Method Dispatch")
  
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
               (page-para "So, every constructor is private to the class that it constructs.  Any other creation of objects must go through a factory method."))
  
  (slide/title "Design Patterns in the Language")
  
  (slide/title "Singleton Pattern")
  
  (slide/title "Factory Pattern")
  
  (outline 'details)
  
  (slide/title "typeOf"
               (page-para "What is the type of the expression" (jcode "C") "?"))
  
  (slide/title "Generics and Metaclasses"
               (page-para "Do metaclasses have implications for the use of "
                          "parametric polymorphism?"))
  
  (slide/center
   (bt "Thank You")))