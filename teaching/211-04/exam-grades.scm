(define exam-grades
  '(("Aaron Portnoy" 47)
 ("Aaron Tatko" 47)
 ("Adam Gorklo" 24)
 ("Adam Koblentz" 30)
 ("Adem Chich" 45)
 ("Alex Coleman" 46)
 ("Alexander Typaldos" 35)
 ("Allen Dewberry" 17)
 ("Anatoly Feldman" 49)
 ("Andres Weber" 27)
 ("Andrew Alix" 32)
 ("Andrew Guida" 48)
 ("Andrew Kunkel" 45)
 ("Ayellet Damary" 32)
 ("Bassil Silver-Hajo" 45)
 ("Berryman, Ken" 24)
 ("Brad Turnier" 9)
 ("Brandon Schory" 53)
 ("Brendan Doherty" 35)
 ("Brian Silva" 42)
 ("Brian Tobia" 47)
 ("Caniparoli, Jacob" 48)
 ("Carmine Silano" 53)
 ("Carol Lee" 48)
 ("Chabot, Jon" 28)
 ("Chebbani, Adam" 11)
 ("Chris Chalifour" 48)
 ("Chris Masciarelli" 40)
 ("Chris Trammell" 25)
 ("Chris Willis" 46)
 ("Christina Carter" 36)
 ("Christopher Boudouvas" 35)
 ("Christopher Looney")
 ("Christopher Svenson" 36)
 ("Christopher Teixeira" 14)
 ("Christopher Umina" 43)
 ("Christos Goumenos" 45)
 ("Chua, Ryan")
 ("Corey Gamache" 47)
 ("Courtney Moores" 37)
 ("Damien Angelos" 51)
 ("Dan Gaylord" 54)
 ("Dan Schiffman" 37)
 ("Daniel Marcucci" 46)
 ("Daniel Noonan" 40)
 ("Daniel Rabinowitz" 42)
 ("Daniel Smedemark-Mar" 33)
 ("Daniela Cervasio" 23)
 ("David Benjamin" 50)
 ("Duc Tri Le" 48)
 ("Earl Robsham" 47)
 ("Eileen Ryan" 40)
 ("Elvin Taullaj" 14)
 ("Eric Blumenstyk" 32)
 ("Eric Liljebach" 34)
 ("Fardad Askarzadeh" 50)
 ("Francisco, Jeff" 52)
 ("Gagnon, Mike" 53)
 ("Gregg Hurson" 32)
 ("Halperin, David" 52)
 ("Hilary Ferraro" 42)
 ("House, Sarah" 55)
 ("Jake Dreier" 30)
 ("Jared Assmus" 55)
 ("Jeffrey Begin" 42)
 ("Jennifer Lussier" 52)
 ("Jeremiah Johnson" 44)
 ("Jeremy Mckenzie" 41)
 ("Jerry Mui" 48)
 ("John Clevesy" 49)
 ("John Patota" 26)
 ("Johnson, Nicole" 48)
 ("Jon McKenzie" 37)
 ("Jon Sporn" 50)
 ("Jonathan Albertelly" 51)
 ("JongHyun Cho" 48)
 ("Joseph Holsten" 45)
 ("Kari Karvinen" 48)
 ("Kathryn Vanderwyk" 47)
 ("Kenneth Eimer" 53)
 ("Killion, James" 51)
 ("Kristin Farris" 24)
 ("Kyle Banks" 51)
 ("Kyros, Matt" 47)
 ("Lee Fogel" 55)
 ("Lee, Alfredo" 50)
 ("Logel, Joe" 42)
 ("Manning, James" 41)
 ("Manny Batista" 54)
 ("Manolo Solis")
 ("Marc Mestre" 41)
 ("Mark Santoski" 53)
 ("Mark Shoaie" 51)
 ("Mark Spadea" 35)
 ("Mark Ursino" 50)
 ("Mathew Dombrowski" 46)
 ("Matt DeGenarro" 40)
 ("Matt Haslett" 32)
 ("Matt Horan" 50)
 ("Matthew Peterson" 44)
 ("Matthew Schroder" 50)
 ("Matthew Skolnick")
 ("Michael Altman" 45)
 ("Michael Battista" 54)
 ("Michael DiStaula" 52)
 ("Michael McIntosh" 41)
 ("Michael Reid" 46)
 ("Mike Nelligan" 50)
 ("Mike Rastello" 21)
 ("Najdzien, Derek" 28)
 ("Nate Whittier" 53)
 ("Nick Rezendes" 46)
 ("Nikolopolous, Constantine" 29)
 ("O'Grady, Matt" 46)
 ("Olga Klepikova" 49)
 ("Patrick Kaeding" 54)
 ("Peter Evans" 50)
 ("Raffile, Kyle" 41)
 ("Randall Dailey" 48)
 ("Rishi Aggarwal" 49)
 ("Ritter, Kathrin" 44)
 ("Robert Gable" 38)
 ("Ronald Thompson" 46)
 ("Ross Ramsay" 47)
 ("Ryan Lafountain" 47)
 ("Sang Hyun Lee" 32)
 ("Sean Devine Hughes" 8)
 ("Sergey Andreev" 47)
 ("Shatkovsky, Vitaly" 55)
 ("Skyler Insler" 41)
 ("Suraj Laungani" 26)
 ("Thomas Blatchford" 44)
 ("Thomas Cody" 39)
 ("Thomas Harrold" 44)
 ("Thomas Pappas" 53)
 ("Tim LaRose" 42)
 ("Travis Stone" 24)
 ("Wesley Werbeck" 28)
 ("Wilson, Janet" 50)))
(require (lib "list.ss") (lib "etc.ss"))
(define took-exam (filter (lambda (x) (= 2 (length x) )) exam-grades))

(define in-trouble (filter (lambda (x) (< (cadr x) 25)) took-exam ))

(define exam-scores (map cadr took-exam))

(define (bounded n m) (lambda (x) (and (< x m) (>= x n))))

(define (avg l) (quotient (apply + l) (length l)))

(define (median l) (list-ref (quicksort l <) (quotient (length l) 2)))

(define 50-up (filter (bounded 50 60) exam-scores))
(define 45-49 (filter (bounded 45 50) exam-scores))
(define 40-44 (filter (bounded 40 45) exam-scores))
(define 30-39 (filter (bounded 30 40) exam-scores))
(define 0-29 (filter (bounded 0 30) exam-scores))



(define (buckets size)
  (map (lambda (n)
         (cons n (filter (bounded n (+ n size)) exam-scores)))
       (map (lambda (n) (* n size))
            (build-list (+ (quotient 55 size) 1) values))))

(define (asterisks n)
  (if (= n 0) ""
      (string-append "*" (asterisks (- n 1)))))
(define (display-buckets n)
  (for-each (lambda (p)
              (let ((header
                     (if (< (car p) 10)
                         (format " ~a" (car p))
                         (format "~a"  (car p)))))
                (display (format "~a : ~a~n"
                                 header
                                 (asterisks (length (cdr p)))))))
            (buckets n)))




;;;;; ignore past here

(define ex-1
  '(
    ("Aaron Portnoy")
    ("Aaron Tatko")
    ("Adam Gorklo")
    ("Adam Koblentz" 30)
    ("Adem Chich" 45)
    ("Alex Coleman" 46)
    ("Alexander Typaldos")
    ("Allen Dewberry" 17)
    ("Anatoly Feldman")
    ("Andres Weber")
    ("Andrew Alix")
    ("Andrew Guida" 48)
    ("Andrew Kunkel" 45)
    ("Ayellet Damary")
    ("Bassil Silver-Hajo" 45)
    ("Berryman, Ken")
    ("Brad Turnier" 9)
    ("Brandon Schory" 53)
    ("Brendan Doherty" 35) 
    ("Brian Silva")
    ("Brian Tobia")
    ("Caniparoli, Jacob" 48)
    ("Carmine Silano" 53)
    ("Carol Lee" 48)
    ("Chabot, Jon")
    ("Chebbani, Adam" 11)
    ("Chris Chalifour" 48)
    ("Chris Masciarelli" 40)
    ("Chris Trammell" 25)
    ("Chris Willis")
    ("Christina Carter" 36)
    ("Christopher Boudouvas" 35)
    ("Christopher Looney")
    ("Christopher Svenson" 36)
    ("Christopher Teixeira" 14)
    ("Christopher Umina")
    ("Christos Goumenos" 45)
    ("Chua, Ryan")
    ("Corey Gamache" 47)
    ("Courtney Moores" 37)
    ("Damien Angelos" 51)
    ("Dan Gaylord" 54)
    ("Dan Schiffman")
    ("Daniel Marcucci")
    ("Daniel Noonan" 40)
    ("Daniel Rabinowitz")
    ("Daniel Smedemark-Mar" 33)
    ("Daniela Cervasio")
    ("David Benjamin")
    ("Duc Tri Le")
    ("Earl Robsham")
    ("Eileen Ryan")
    ("Elvin Taullaj")
    ("Eric Blumenstyk" 32)
    ("Eric Liljebach")
    ("Fardad Askarzadeh")
    ("Francisco, Jeff" 52)
    ("Gagnon, Mike")
    ("Gregg Hurson" 32)
    ("Halperin, David")
    ("Hilary Ferraro")
    ("House, Sarah" 55)
    ("Jake Dreier")
    ("Jared Assmus" 55)
    ("Jeffrey Begin")
    ("Jennifer Lussier" 52)
    ("Jeremiah Johnson")
    ("Jeremy Mckenzie" 41)
    ("Jerry Mui")
    ("John Clevesy" 49)
    ("John Patota" 26)
    ("Johnson, Nicole" 48)
    ("Jon McKenzie")
    ("Jon Sporn" 50)
    ("Jonathan Albertelly" 51)
    ("JongHyun Cho")
    ("Joseph Holsten")
    ("Kari Karvinen" 48)
    ("Kathryn Vanderwyk" 47)
    ("Kenneth Eimer" 53)
    ("Killion, James")
    ("Kristin Farris")
    ("Kyle Banks" 51)
    ("Kyros, Matt")
    ("Lee Fogel" 55)
    ("Lee, Alfredo" 50)
    ("Logel, Joe")
    ("Manning, James" 41)
    ("Manny Batista")
    ("Manolo Solis")
    ("Marc Mestre" 41)
    ("Mark Santoski" 53)
    ("Mark Shoaie")
    ("Mark Spadea" 35)
    ("Mark Ursino")
    ("Mathew Dombrowski" 46)
    ("Matt DeGenarro")
    ("Matt Haslett" 32)
    ("Matt Horan" 50)
    ("Matthew Peterson")
    ("Matthew Schroder")
    ("Matthew Skolnick")
    ("Michael Altman" 45)
    ("Michael Battista" 54)
    ("Michael DiStaula")
    ("Michael McIntosh" 41)
    ("Michael Reid" 46)
    ("Mike Nelligan" )
    ("Mike Rastello" 21)
    ("Najdzien, Derek" 28)
    ("Nate Whittier")
    ("Nick Rezendes" 46)
    ("Nikolopolous, Constantine" 29)
    ("O'Grady, Matt" 46)
    ("Olga Klepikova" 49)
    ("Patrick Kaeding")
    ("Peter Evans" 50)
    ("Raffile, Kyle")
    ("Randall Dailey")
    ("Rishi Aggarwal")
    ("Ritter, Kathrin")
    ("Robert Gable" 38)
    ("Ronald Thompson")
    ("Ross Ramsay")
    ("Ryan Lafountain" 47)
    ("Sang Hyun Lee" 32)
    ("Sean Devine Hughes")
    ("Sergey Andreev")
    ("Shatkovsky, Vitaly")
    ("Skyler Insler")
    ("Suraj Laungani")
    ("Thomas Blatchford")
    ("Thomas Cody")
    ("Thomas Harrold" 44)
    ("Thomas Pappas" 53)
    ("Tim LaRose" 42)
    ("Travis Stone" 24)
    ("Wesley Werbeck")
    ("Wilson, Janet")
    ))

(define ex-2 ' (("Aaron Portnoy" 47)
 ("Aaron Tatko" 47)
 ("Adam Gorklo" 24)
 ("Adam Koblentz")
 ("Adem Chich")
 ("Alex Coleman")
 ("Alexander Typaldos" 35)
 ("Allen Dewberry")
 ("Anatoly Feldman" 49)
 ("Andres Weber" 27)
 ("Andrew Alix" 32)
 ("Andrew Guida")
 ("Andrew Kunkel")
 ("Ayellet Damary" 32)
 ("Bassil Silver-Hajo")
 ("Berryman, Ken" 24)
 ("Brad Turnier")
 ("Brandon Schory")
 ("Brendan Doherty")
 ("Brian Silva" 42)
 ("Brian Tobia" 47)
 ("Caniparoli, Jacob")
 ("Carmine Silano")
 ("Carol Lee")
 ("Chabot, Jon" 28)
 ("Chebbani, Adam")
 ("Chris Chalifour")
 ("Chris Masciarelli")
 ("Chris Trammell")
 ("Chris Willis" 46)
 ("Christina Carter")
 ("Christopher Boudouvas")
 ("Christopher Looney")
 ("Christopher Svenson")
 ("Christopher Teixeira")
 ("Christopher Umina" 43)
 ("Christos Goumenos")
 ("Chua, Ryan")
 ("Corey Gamache")
 ("Courtney Moores")
 ("Damien Angelos")
 ("Dan Gaylord")
 ("Dan Schiffman" 37)
 ("Daniel Marcucci" 46)
 ("Daniel Noonan")
 ("Daniel Rabinowitz" 42)
 ("Daniel Smedemark-Mar")
 ("Daniela Cervasio" 23)
 ("David Benjamin" 50)
 ("Duc Tri Le" 48)
 ("Earl Robsham" 47)
 ("Eileen Ryan" 40)
 ("Elvin Taullaj" 14)
 ("Eric Blumenstyk")
 ("Eric Liljebach" 34)
 ("Fardad Askarzadeh" 50)
 ("Francisco, Jeff")
 ("Gagnon, Mike" 53)
 ("Gregg Hurson")
 ("Halperin, David" 52)
 ("Hilary Ferraro" 42)
 ("House, Sarah")
 ("Jake Dreier" 30)
 ("Jared Assmus")
 ("Jeffrey Begin" 42)
 ("Jenny Lussier")
 ("Jeremiah Johnson" 44)
 ("Jeremy Mckenzie")
 ("Jerry Mui" 48)
 ("John Clevesy")
 ("John Patota")
 ("Johnson, Nicole")
 ("Jon McKenzie" 37)
 ("Jon Sporn")
 ("Jonathan Albertelly")
 ("JongHyun Cho" 48)
 ("Joseph Holsten" 45)
 ("Kari Karvinen")
 ("Kathryn Vanderwyk")
 ("Kenneth Eimer")
 ("Killion, James" 51)
 ("Kristin Farris" 24)
 ("Kyle Banks")
 ("Kyros, Matt" 47)
 ("Lee Fogel")
 ("Lee, Alfredo")
 ("Logel, Joe" 42)
 ("Manning, James")
 ("Manny Batista" 54)
 ("Manolo Solis")
 ("Marc Mestre")
 ("Mark Santoski")
 ("Mark Shoaie" 51)
 ("Mark Spadea")
 ("Mark Ursino" 50)
 ("Mathew Dombrowski")
 ("Matt DeGenarro" 40)
 ("Matt Haslett")
 ("Matt Horan")
 ("Matthew Peterson" 44)
 ("Matthew Schroder" 50)
 ("Matthew Skolnick")
 ("Michael Altman")
 ("Michael Battista")
 ("Michael DiStaula" 52)
 ("Michael McIntosh")
 ("Michael Reid")
 ("Mike Nelligan" 50)
 ("Mike Rastello")
 ("Najdzien, Derek")
 ("Nate Whittier" 53)
 ("Nick Rezendes")
 ("Nikolopolous, Constantine")
 ("O'Grady, Matt")
 ("Olga Klepikova")
 ("Patrick Kaeding" 54)
 ("Peter Evans")
 ("Raffile, Kyle" 41)
 ("Randall Dailey" 48)
 ("Rishi Aggarwal" 49)
 ("Ritter, Kathrin" 44)
 ("Robert Gable")
 ("Ronald Thompson" 46)
 ("Ross Ramsay" 47)
 ("Ryan Lafountain")
 ("Sang Hyun Lee")
 ("Sean Devine Hughes" 8)
 ("Sergey Andreev" 47)
 ("Shatkovsky, Vitaly" 55)
 ("Skyler Insler" 41)
 ("Suraj Laungani" 26)
 ("Thomas Blatchford" 44)
 ("Thomas Cody" 39)
 ("Thomas Harrold")
 ("Thomas Pappas")
 ("Tim LaRose")
 ("Travis Stone")
 ("Wesley Werbeck" 28)
 ("Wilson, Janet" 50)
 )
  )