;;; Simple Structures
;;; 

;; Consider the following structure definition, with accompanying data definition

;; A student is (make-student String String Number)
(define-struct student (name major gpa))

;; List the functions produced by this data definition, and their contracts.

;; TODO:  Fill this in.

;; Design a template for functions which operate on students.

;; TODO:  Fill this in.

;; Design a function that, when given a student, tells if they are failing (gpa < 1.0)

;; TODO:  Fill this in.

;; Design a function that, given a student, produces a string with both their name and major.

;; TODO:  Fill this in.

;;; Unions
;;;

;; Give a data definition for grades, which are symbols such as 'A and 'B.

;; TODO:  Fill this in.

;; Design a function that, given a student, produces their letter
;; grade.  You may use whatever cutoffs you like.

;; TODO:  Fill this in.

;; Create a structure and data definition for teachers, with name and
;; class name, and then provide a template for working with such
;; structures.

;; TODO:  Fill this in.

;; Give a data definition for Persons, which are either teachers or
;; students.  Create a template for this data.

;; TODO:  Fill this in.

;; Design a function that given a Person, produce true if they study
;; or teach math.

;; TODO:  Fill this in.


;;; Lists
;;;

;; Give a data definition and template for lists of students.

;; TODO:  Fill this in.

;; Design a function which determines if any students are failing in a list of students.

;; TODO:  Fill this in.

;; Design a function that produces all the computer science majors from a list of students.

;; TODO:  Fill this in.

;; Design a function which determines if all the teachers in a list are science teachers.

;; TODO:  Fill this in.

;; Design a function which, given a teacher and a list of students,
;; determines if the teacher has the same field as one of the
;; students.

;; TODO:  Fill this in.


;;; Loops
;;;

;; Rewrite all of the functions from the list section using scheme loops.

;; TODO:  Fill this in.


;;; Recursive data structures
;;;

;; Consider the following data definition:
;; A Tree is one of:
;; - Number
;; - (make-node Tree Tree)

(define-struct tree (left right))

;; Produce a template for Trees.

;; TODO:  Fill this in.

;; Design a function that adds 1 to every number in a tree.

;; TODO:  Fill this in.

;; Create a data definition for trees of strings.

;; TODO:  Fill this in.

;; Design a function that appends "Hello" to every string in a tree.

;; TODO:  Fill this in.

;; Abstract the two data definitions of trees into one.

;; TODO:  Fill this in.

;; Challenge:  Abstract both functions into one.

;; TODO:  Fill this in.

;; Extra Challenge:  Design a function on Trees of Numbers with the following contract:
;; ftree: (Number -> X) (X X -> X) -> X
;; This function will be much like foldl and foldr for lists.