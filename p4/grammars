
All grammars are created by extension, so first we create an empty
one.

let gram = Grammar.gcreate (Plexer.gmake ());;

let expr = Grammar.Entry.create gram "expr";;

This is a very simple grammar for parsing arithmetic expressions.  

       EXTEND
         expr:
           [ [ x = expr; "+"; y = expr -> x + y
             | x = expr; "-"; y = expr -> x - y 
             | x = expr; "*"; y = expr -> x * y
             | x = expr; "/"; y = expr -> x / y 
             |  x = INT -> int_of_string x
             | "("; e = expr; ")" -> e ] ]
         ;
       END;;


Now we can do things like:

Grammar.Entry.parse expr (Stream.of_string "8 * (5 - 2)")

Which will produce 24.

But we have no operator precedence, which means that 

 Grammar.Entry.parse expr (Stream.of_string "8 - 5 * 2");;

evaluates to 6 instead of the correct -2.

Fortunately, it's easy to add precedence to these grammars.

       EXTEND
         expr:
           [ [ x = expr; "+"; y = expr -> x + y
             | x = expr; "-"; y = expr -> x - y ]
           | [ x = expr; "*"; y = expr -> x * y
             | x = expr; "/"; y = expr -> x / y ]
           | [ x = INT -> int_of_string x
             | "("; e = expr; ")" -> e ] ]
         ;
       END;;

And now the above examples work.

In order to manipulate this grammar, we can also name the levels, and
     give them different kinds of precedence.
     
     EXTEND
     expr:
     [ "add" LEFTA
         [ x = expr; "+"; y = expr -> x + y
         | x = expr; "-"; y = expr -> x - y ]
     | "mult" RIGHTA
         [ x = expr; "*"; y = expr -> x * y
         | x = expr; "/"; y = expr -> x / y ]
     | "simple" NONA
	 [ x = INT -> int_of_string x
     | "("; e = expr; ")" -> e ] ]
       ;
     END;;

Now that we've done that, we have a handle on the various parts.  So
  we can add variables.


let env = ref [];;

EXTEND
expr: LEVEL "simple" [ [ x = LIDENT -> List.assoc x !env ] ];
END;;

Not the most elegant solution, but it works.  Note that this working
  means referential transparceny is out the window.  

So now we have a system for defining domain-specific languages for
  writing whatever we want, and the evaluator goes right in the action
  routines.  So it's easy to embed DSLs in OCaml.  

The other way of looking at it is that we now have an ugly syntax for
  parser generators.  But the parsing technology is quite
  interesting. And we didn't have to write a lexer (since the trivial
  one is provided).
