(module ps2 (planet "qstr-lang.ss" ("jacob" "quasistring.plt" 1 0))
  (require "../../scheme-tex.scm")
  
  (require  (lib "list.ss") (lib "match.ss"))
  
  (define (math . args) (ensuremath (apply group args)))
  
  (define (function nm)
    (lambda args
      (let ((sep ", "))
        "$(math nm)($(apply string-append (interleave sep (map math args))))")))
  
  (define-values (i j k l m n x y z a b A B C S)
    (apply values (map math '(i j k l m n x y z a b A B C S))))
  
  (define nlogn (math "n \\log n"))

  (predefs0 Omega omega Theta)
  (predefs lg)
  
  (define-values (Om om o O Th xi xk) 
    (values
     (function Omega)
     (function omega)
     (function "o")
     (function "O")
     (function Theta)
     (sub x i)
     (sub x k)))
  
  (define (binop op) (lambda (a b) (math "$a $op $b")))

  (define-values (plus minus eq le)
    (apply values
           (map binop (list '+ "-" '= '<)))) 
  
  (define (index arr i) (math "$arr[$i]"))
  
  
  (define ps2
    (tex 
     "ps2.tex"
     (documentclass 'article 12)
     (title "Problem Set 2")
     (author "Sam Tobin-Hochstadt")
     (document
      (section "Problem 1"
               (group "Consider a decision tree for a comparison sorting algorithm applied to a"
                      "list of" n "elements.  If this algorithm was linear for half of the possible"
                      "inputs, then consider the portion of the tree with only the leaves of depth"
		      (minus n 1) "or less.  Then this tree, by assumtion, contains at least half"
		      "of the "(math "n!") "inputs.  But by the argument for the lower bound on sorting,"
		      "this tree must have " (math "n!/2") "leaves, and thus must have a maximum depth"
		      "of " (math (lg "n!/2")) "which is greater than $(Om nlogn), contradicting our assumption that the height of"
		      "the tree is at most $(math (minus n 1))."
		      ""
		      "By a similar argument, if we take there to be " (math "1/n") "paths of length"
		      "less than $n, we discover that the tree height must be at least " (math (lg "(n-1)!"))
		      "which is $(om n), contradicting our assumption."
		      ""
		      "Again, if we assume that there are " (math "1/$(super 2 n)") "paths of length less than"
		      n "then we get a tree with " (math "n!/$(super 2 n)") "nodes, which must have depth at least"
		      (eq (eq (lg "n!/$(super 2 n)") (minus (lg "n!") (lg (super 2 n)))) (O nlogn)) ".  Therefore, "
		      "not even " (math "1/$(super 2 n)") "of the inputs can be sorted in linear time."
		      ))
      (section "Problem 2"
               (group "Imagine that there was such an algorithm.  Then we could sort a list"
                      "in faster than " (math "n lg n") "time.  First, select the median element of the"
                      "list, via the linear time algorithm.  Then divide the list into two"
                      "halves, those smaller than the median and those larger.  Then, via the"
                      "assumed algorithm, we can sort the entire sequence in" (o (math n (lg "n/2")))
                      ". This is a contradiction, since comparison sorting is "(Om (math n (lg n)))"."
                      ))
      (section "Problem 3"
               (section "Part 1"
                        (group "[I collaborated with Felix on this problem.]"
                      "Given an input array $A of length $n, first construct an array $B of size $k initialized to 0.  Then iterate over the elements of $A, incremening $(index B (index A i)) for each $i .  This takes $(O n) time."
                      "Then iterate over the array $B, starting at $(index B 0), changing each element "
                      (math (eq (index B i) (plus (index B i) (index B "$i - 1"))))". This takes time $(O k), since B is of size $k ."
                      "Therefore, the total preprocessing time is $(O (math (plus n k)))."
                      "Then, given a question about the number of values between $a and $b, simply return "
                      (minus (index B a) (index B (minus b 1)))
                             ".  This is the correct answer, since $(index B i) is the number of values in A that are less than or equal to $i ."))
               (section "Part 2"
                        (group 
                         "[I collaborated with Owen and Carl on this problem.]"
                         "Given an array $A of number from 0 to $(minus n 1), first replace each number by its representation in base 2.  Then all the numbers are represented in at most $(math 2 (lg n)) bits each."
                         "Then, we apply Lemma 8.4.  Choose $(eq 'r (lg n)) and therefore our algorithm operates in time " (eq (eq (Th "((2 $(lg n))/r)(n + $(super 2 (lg n))))") (Th (math 2 "(n + n)"))) (Th n))))) 
      (section "Problem 5"
               (section "Part 1"
                        (group "[I collaborated with Owen on this problem.]"
                               "If radix sort is applied to a sequence of numbers, then it visits each digit of each number exactly once."
                               "Therefore, radix sort applied to numbers with a total of $n digits should run in $(O n) time.  However, we have to"
                               "avoid processing numbers after their digits have been exhausted.  This is accomplished by stopping the counting sort for each"
                               "digit once the first zero is encountered in the previous digit.  Then only one additional digit is processed for each number."
                               "This means that still only $(O n) digits are processed, and the sort runs in $(O n) time."
                               ))
               (section "Part 2"
                        "The argument from the previous problem applies exactly, except that blanks are sorted ahead of all other digits, instead of after them.")
               )
      (section 
       "Problem 6"
       (section "Part 1"
                (group "[I collaborated with Felix on this problem.]"
                       "First, find the median item.  This can be done in linear time."
                       "Second, iterate through the items, and create a new array where each element is a pair of the element and "
                       "its distance from the median.  Then, using a linear-time order statistic, find the $(values k)th largest"
                       "element of this new array, ordered by the distance from the median.  Then iterate throught the array, and"
                       "find all those elements whose distance from the median is less than or equal to $(values k).  These are the k"
                       "closest elements to the median.  This algorithm has running time $(O n) since it involves two order"
                       "statistics, which can be done in linear time, and two passes over an array of size $n, which is $(Th n).   "
                       )) 
       (section "Part 2"
                (group "The solution is simply to locate the pipeline on the median $y coordinate."
                       "This minimizes the total distance of the spur pipelines, which is simply the "
                       "sum of differences from the pipeline to all of the $y coordinates. The "
                       "Rivest-Tarjan-etc algorithm gives the median in linear time."
                       "To see why this answer is correct, consider a pairing of the oil wells.  If the "
                       "pipeline is located on the median, then for every oil well on one side"
                       "there is one on the other side.  So assume that each well is paired with a well"
                       "on the other side.  Now, if the pipeline was higher, then exactly half the oil wells would be further away, and half would be closer.  Therefore, any choice so that half the oil wells are on each side is optimal.  If there are an odd number of wells, however, any movement away from the median makes the median well further away.  Therefore, the only optimal choice is the median.")))
      
      (section "Problem 7"
               (section "Part a"
                        (group
                         "If $xk is the median element, then there are exactly as many"
                         "elements $x where $(le xi xk) as there are where $(le xk xi).  Since all elements have exactly the same weight, it must be the case that the sum of each of these partitions is 1/2, since they contain all the elements. Therefore $xk is also the weighted median."))
               (section "Part b"
                        (group 
                         "To find the weighted median, first sort the list.  This takes $(O nlogn) time.  Then iterate through the sorted sequence, keeping track of the total weight so far.  When the total weight exceeds 1/2, the most recently seen element is the weighted median element.  This algorithm involves a sort and an iteration through the list.  Thus it is $(eq (O (plus nlogn n)) (O nlogn))."))
               (section "Part c"
                        (group "To compute the weighted median in linear time, we make a slight modification to the Select algorithm.  Instead of using insertion sort"
                               "to find the median, instead use insertion sort, and then find the weighted median.  Perform this algorithm recursively, just as with Select."
                               "This computes the weighted median of the array.")))
      )
     )))