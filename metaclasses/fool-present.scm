(module fool-present (lib "slideshow.ss" "slideshow")

  (require (prefix : (lib "symbol.ss" "texpict")))

  (define (blank2) (vl-append (blank) (blank)))
  
  (define (small t) (text t (current-main-font) (* 2 (quotient (current-font-size) 3))))
  
  (slide/center
   (page-para* (titlet "A Core Calculus of Metaclasses"))
   (blank)
   (blank)
   (page-para* "Sam Tobin-Hochstadt")
   (page-para* "Eric Allen")
   (blank)
   (page-para* (small "Sun Microsystems Inc."))
   (page-para* (small "Northeastern University"))
   )
  
  (define outline
    (make-outline 
     
     'motivation
     "Why Metaclasses?"
     #f
     
     'mcj
     "A Simple Language with Metaclasses"
     #f
     
     'benifit
     "An Unexpected Benifit"
     #f
     
     'details
     "Interesting Design Questions"
     #f))
  
  (outline 'motivation)
  
  (slide/title "Why Metaclasses?"
               (page-item "Modeling the World")
               (page-item "Flexible Hierarchies")
               (page-item "Generalized Statics")
               (page-item "Design Patterns"))

  (define (code str)
    (colorize (tt str) "blue"))
  
  (define fish (standard-fish (* 2 gap-size) gap-size))

  
  (slide/title "The Complex World (Part 1)"
               (page-para "Consider Harry. EAGLE IMAGE HERE")
               'next
               (page-para "Harry is an eagle." )
               #;(page-para "Now consider " (it "Eaglensis Latinus") "."
                          "This is the species Harry belongs to.")
               'next
               (page-para "This relationship is easy to model in a object-oriented world.")
               (code "Harry : Eagle")
               'next
               (page-para "We can easily model other species as well.")
               (page-para/c fish (code " : Salmon")))
  (slide/title "The Complex World (Part 2)"
               (page-para "In a language with static methods, we can "
                          "even ask this question:")
               (code "Eagle.isEndagered()")
               'next
               (page-para "But if " (code "Salmon") "is a species, will this work?")
               (code "Salmon.isEndangered()")
               'next
               (blank)
               (blank)
               (page-para (it "Who knows?") "We have" (bt "no") 
                          "guarantees about the relationship"
                          "between" (code "Salmon") "and" (code "Eagle") ".")
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
               (code "Eagle <: Species")
               (code "Salmon <: Species")
               (code "Harry : Eagle")
               (blank)
               (page-para "What's wrong here?")
               'next
               (code "Harry : Species")
               )
  
  (slide/title "What Do We Want?"
               (page-para "We would like to define a group of entities,"
                          "all of which must respond to certain messages.")
               'next
               (page-para "That sounds an awful lot like a type.")
               (blank) (blank)
               (page-para "What if we could make " (code "Species")
                          "the type of " (code "Eagle") "?")
               (code "Eagle : Species")
               'next
               (page-para "Then we have a guarantee about the behavior of Eagle,"
                          "since it is an element of " (code "Species") ".")
               (page-para "And this guarantee holds for other such elements,"
                          "such as " (code "Salmon") ".")
               )
  
  (slide/title "Where are we now?"
               (page-item "We have classes as expressions:")
               (page-subitem (code "Eagle.isEndangered()"))
               'next
               (page-item "We have classes that have classes:")
               (page-subitem (code "Eagle : Species"))
               'next
               (blank)
               (page-para/c "We have Metaclasses."))
  
  
  (outline 'mcj)
  
  (slide/title "MCJ: A Extension of FGJ with Metaclasses"
               'next
               (page-item "Classes can be used anywhere an expression is expected.")
               (blank) 

               (code "Eagle.population() + 7")

               (blank2)
               
               'next
               (page-item "Classes have " (code "class") "members, which are the methods of the class when used as an expression.")
               (blank)
               
               (code "class Eagle { class population() { return pop; } }")
               (blank2)
               'next
               
               (page-item "Every class has a metaclass (also referred to as " 
                          (it "kind" )")")
               (blank)
               (code "class Eagle kind Species")

               'next
               (blank2)
               (page-item "Classes inherit some of their class methods from their kinds.")
               
               )
  
  (outline 'benifit)
  
  (slide/title "Rethinking Constructors"
               (page-para "As we have seen, every constructor, as in FGJ,"
                          "must initialize every field.")
               (page-para "Obviously, this is suboptimal.")
               'next
               (page-para "But unlike FGJ, we aren't stuck with this.")
               'next
               (blank2)
               (page-para "Class methods give us the ability to define factory methods.")
               (code "Point make_origin() { return new (0,0); }")
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
               (page-para "What is the type of " (code "C") "?"))
  
  (slide/title "Generics and Metaclasses"
               (page-para "Do metaclasses have implications for the use of parametric polymorphism."))
  
  (slide/center
   (bt "Thank You")))