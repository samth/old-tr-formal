  (define jeff-grades ;; up to date 11-8
'(;                        hw01 hw02   hw03   hw04   hw05        hw07       hw08
 ("Rishi Aggarwal"        15   (19 1) (22 1) (29 0) (30     0)  (47     1) (29 1)) ; rishi@rjsnetworks.com
 ("Jonathan Albertelly"   18   (0  1) (21 1) (30 1) (29     1)  (44     1) (29 1))
 ("Andrew Alix"           19   (14 1) (13 1) (30 1) (32     0)  (27     0) (28 1)) ; alix.an@neu.edu
 ("Thomas Blatchford"      6   (8  1) (23 1) (30 1) (21     1)  (19     1) (35 1)) ; tomb@ccs.neu.edu
 ("Chris Chalifour"       19   (21 1) (32 1) (37 0) (31     0)  (47     0) (29 1)) ; cchali4@ccs.neu.edu
 ("Adem Chich"            17   (18 1) (13 1) (29 0) (30     0)  (40     1) (24 1)) ; achich@ccs.neu.edu
 ("Kristin Farris"        16   (0  1) (29 1) (33 0) (28     1)  (48     1) (36 1)) ; farris.k@neu.edu
 ("Corey Gamache"         20   (0  1) (16 1) (24 1) (28     1)  (17     1) (31 1)) ; gamache.c@neu.edu
 ("Thomas Harrold"        18   (18 1) (13 1) (29 1) (30     1)  (40     0) (24 1)) ; tharrold@ccs.neu.edu
 ("Skyler Insler"         ?    (22 1) (0  1) (0  0) (00 false)  (0  false) (0  1))
 ("Kari Karvinen"         18   (0  1) (16 1) (24 1) (28     0)  (17     1) (31 1)) ; kkarvine@ccs.neu.edu
 ("Olga Klepikova"        19   (20 1) (23 1) (31 0) (26     0)  (44     1) (33 1)) ; olgak@ccs.neu.edu
 ("Carol Lee"             16   (0  1) (29 1) (33 1) (28     1)  (48     1) (36 1))
 ("Sang Hyun Lee"          8   (8  1) (23 1) (30 0) (21     1)  (19     0) (35 1)) ; lee.san@neu.edu
 ("Christopher Looney"    14   (16 1) (0  1) (0  0) (00 false)  (0  false) (0  1))
 ("Daniel Marcucci"       19   (12 1) (17 1) (34 1) (31     1)  (30     1) (36 1))
 ("Jeremy Mckenzie"       ?    (0  1) (21 1) (30 0) (29     0)  (44 false) (0  1)) ; aquila@ccs.neu.edu
 ("Mike Nelligan"         16   (7  1) (17 1) (0  0) (27     1)  (7      1) (24 1)) ; nelligan.mic@neu.edu
 ("Daniel Noonan"         16   (19 1) (22 1) (29 0) (30     0)  (34     1) (34 1)) ; djn@ccs.neu.edu
 ("Thomas Pappas"         ?    (20 1) (23 1) (31 1) (26     1)  (44     1) (33 1))
 ("Daniel Rabinowitz"     17   (0  1) (19 1) (34 1) (30     0)  (40     1) (33 1)) ; drabino9@ccs.neu.edu
 ("Ross Ramsay"           17   (14 1) (13 1) (30 1) (32     1)  (27     1) (28 1))
 ("Eileen Ryan"           20   (16 1) (0  1) (0  0) (31     0)  (30     1) (36 1)) ; ryan.ei@neu.edu
 ("Mark Shoaie"           15   (16 1) (27 1) (0  1) (29     0)  (47     1) (31 1)) ; shoaiem@ccs.neu.edu
 ("Matthew Skolnick"      17   (12 1) (17 1) (34 0) (00 false)  (0  false) (0  1))
 ("Manolo Solis"          17   (21 1) (32 1) (37 1) (00 false)  (0  false) (0  1))
 ("Jon Sporn"             ?    (16 1) (27 1) (0  1) (29     1)  (47     0) (31 1)) ; ssporn@ccs.neu.edu
 ("Brian Tobia"           ?    (0  1) (19 1) (34 1) (30     1)  (40 false) (33 1))
 ("Andres Weber"           8   (7  1) (17 1) (0  1) (27 false)  (7      0) (24 1)) ; fayth@ccs.neu.edu
 ("Chris Willis"          18   (19 1) (22 1) (29 0) (30 false)  (34     1) (34 1)) ; chrismw@ccs.neu.edu


))


  (define sam-grades ;; up to date 11-12
    '(("Aaron Tatko"               #f (7 1)  (#f 1) (21 1) (24 0) (23 1) 18 27 (0 1))
      ("Alexander Typaldos"        17 (7 1)  (#f 1) (21 1) (24 0) (23 0) 18 27 (0 0))
      ("Adam Koblentz"             15 (20 1) (26 1) (33 1) (27 1) (33 0) 33 38 (10 1))
      ("Ryan Lafountain"           17 (20 1) (26 1) (33 1) (27 1) (33 1) 33 38 (10 1))
      ("Andrew Kunkel"             14 (19 1) (19 1) (27 1) (27 0) (23 1) 17 48 (1 1))
      ("Christopher Boudouvas"     #f (19 1) (19 1) (27 1) (27 0) (23 1) 17 48 (1 1))
      ("Ayellet Damary"            17 (11 1) (21 1) (33 1) (28 0) (39 1) 29 44 (1 0))
      ("Daniel Smedemark-Mar"      17 (11 1) (21 1) (33 1) (28 0) (39 1) 29 44 (1 0))
;      ("Wesley Werbeck"            18 (12 1) (20 1) (25 1) (28 0) (29 1) 29 44)
      ("Bassil Silver-Hajo"        16 (15 1) (#f 1) (13 1) (25 1) (41 1) 21 43 (0 1))
      ("Eric Blumenstyk"           13 (15 1) (#f 1) (13 1) (25 1) (41 1) 21 43 (0 1))
      ("Carmine Silano"            20 (11 1) (25 1) (21 1) (29 0) (38 1) 19 38 (0 1))
      ("Suraj Laungani"            #f (11 1) (25 1) (21 0) (29 1) (38 1) 19 38 (0 1))
      ("Chris Masciarelli"         17 (17 1) (3 1)  (11 0) (9 0)  (4 0)  2  #f (0 1))
      ("Matt Haslett"              #f (12 0) (3 1)  (11 1) (9 0)  (4 0)  2  #f (0 1))
      ("Christos Goumenos"         19 (13 1) (26 1) (26 1) (24 1) (36 1) 37 42 (7 1))
      ("Marc Mestre"               15 (13 1) (26 1) (26 1) (24 0) (36 1) 37 42 (7 1))
      ("Dan Schiffman"             #f (#f 1) (13 1) (8 1)  (26 0) (42 1) 26 39 (0 1)) 
      ("Jerry Mui"                 12 (13 1) (10 1) (8 1)  (26 0) (42 0) 26 39 (0 1))
;      ("Elvin Taullaj"             #f (16 1) (27 1) (34 0) (28 0) (43 #f)25 45 (? #f))
      ("Kenneth Eimer"             18 (16 1) (27 1) (34 1) (28 1) (43 1) 25 45 (10 1))
;      ("Gregg Hurson"              1  (7 1)  (8 1)  (20 1) (20 0) (32 0) 23 32 (? #f))
      ("Jeffrey Begin"             14 (7 1)  (8 1)  (20 1) (20 0) (32 1) 23 32 (0 1))
      ("Lee Fogel"                 19 (14 1) (29 1) (28 1) (28 1) (37 1) 25 36 (6 1))
      ("Christina Carter"          #f (18 1) (29 1) (28 1) (28 0) (37 0) 25 36 (6 1))
      ("Mark Spadea"               7  (19 1) (15 1) (29 0) (16 0) (38 0) 24 42 (#f 1))
      ("Matthew Schroder"          20 (19 1) (15 1) (29 1) (16 1) (38 1) 24 42 (#f 1))
      ("Matt Horan"                14 (21 1) (28 1) (33 1) (29 0) (41 1) 31 53 (9 1))
      ("Peter Evans"               19 (21 1) (28 1) (33 1) (29 0) (41 1) 31 53 (9 1))
      ("Michael Reid"              19 (13 1) (30 1) (31 1) (28 1) (45 0) 21 35 (5 1))
      ("Thomas Cody"               16 (13 1) (30 1) (31 1) (28 0) (45 1) 21 35 (5 1))
      ))


  (define rebecca-grades ;; up to date 11-12
'(("Allen Dewberry"  15 (15 1) (31 0) (34 1) (29 0) (49 0) 36 43)
 ("Mark Ursino"  17 (15 1) (31 0) (34 1) (29 1) (49 1) 36 43)
 ("Travis Stone"  19 (19 1) (20 1) (28 1) (22 0) (40 1) 28 36)
 ("Anatoly Feldman" 18 (19 1) (20 1) (28 1) (22 1) (40 1) 28 36)
 ("JongHyun Cho" 15 (6 1) (18 1) (26 1) (22 0) (35 1) 32 40)
 ("Robert Gable" 11 (6 1) (18 1) (26 1) (22 0) (35 1) 32 40)
 ("Dan Gaylord" 17 (20 1) (26 1) (34 1) (27 1) (39 1) 35 49)
 ("Randall Dailey" 14 (20 1) (26 1) (34 1) (27 0) (39 1) 35 49)
 ("John Patota"  10 (10 1) (15 0) (28 0) (#f 0) (19 0) 16 34)
 ("Nick Rezendes" 17 (10 1) (15 1) (28 1) (#f 0) (19 1) 16 34)
 ("Matthew Peterson" 16 (16 1) (32 1) (32 1) (32 1) (49 1) 35 45)
 ("Jon McKenzie" 12 (16 1) (32 0) (32 0) (32 1) (49 1) 35 45)
 ("Duc Tri Le" #f (12 1) (29 0) (33 1) (30 1) (44 1) 36 41)
 ("Sean Devine Hughes" 14 (12 1) (29 0) (33 1) (30 0) (44 1) #f #f)
 ("Courtney Moores" 16 (17 1) (26 1) (36 1) (33 0) (49 1) 34 56)
 ("Earl Robsham" 17 (17 1) (26 1) (36 1) (33 1) (49 1) 34 56)
 ("Hilary Ferraro" 20 (16 1) (29 0) (27 1) (29 1) (38 1) 35 42)
 ("Mathew Dombrowski" 20 (16 1) (29 0) (27 1) (29 0) (38 1) 35 42)
 ("Eric Liljebach"  16 (17 1) (21 0) (19 0) (27 0) (42 1) 36 42)
 ("Ronald Thompson" 17 (17 1) (21 0) (19 1) (27 0) (42 1) 36 42)
 ("Brad Turnier" 19 (#f #f) (#f 1) (8 1) (26 0) (42 1) #f #f)
 ("Jeremiah Johnson" 20 (18 1) (29 0) (17 1) (24 0) (36 1) 36 41)
 ("Jenny Lussier"  20 (18 1) (29 1) (17 1) (24 0) (36 1) 36 41)
 ("Fardad Askarzadeh" 11 (#f 1) (21 1) (29 1) (30 1) (48 1) 35 55)
 ("David Benjamin" 20 (#f 1) (21 1) (29 1) (30 1) (48 1) 35 55)
 ("Kyle Banks" 15 (10 1) (15 0) (26 1) (30 0) (43 1) 36 14)
 ("Manny Batista" 19 (17 1) (26 1) (26 1) (30 1) (47 1) 35 54)
 ("Nate Whittier" 18 (19 1) (32 1) (26 1) (32 1) (47 1) 35 54)
 ("Mike Rastello" 15 (2 1) (17 0) (26 0) (30 0) (43 1) 35 14)
 ("Daniela Cervasio" 13 (18 1) (17 0) (7 0) (11 0) (11 1) #f #f)
 ("Michael Altman" 14 (16 1) (17 0) (26 1) (25 0) (13 1) 31 38)
 ("Joseph Holsten" #f (22 1) (31 0) (#f 1) (28 1) (44 1) 35 50)
("Skyler Insler"   #f (22 1) (31 1) (#f 0) (28 0) (44 1) 35 50)
 ("Brian Silva" 16 (16 1) (17 0) (26 1) (25 0) (13 1) 31 38)
 ("Aaron Portnoy" #f (18 1) (17 0) (7 1) (11 1) (11 1) 31 50)))
    

   (define carl-grades ;; up to date : 11-12
'
(
("Ken Berryman"             17 (16 1) 18 (29 0) (30  0) (47  1) 30 #f)
("Jacob Caniparoli"         16 (16 1) 18 (29 1) (30  0) (47  1) 30 #f)
("Jon Chabot"               17 (12 1) 17 ( 9 1) (21  0) (31  1) 34 35)
("Adam Chebbani"            16 (#f 1) 16 (29 1) (18  0) (#f #f) #f #f)
("Jeff Francisco"           16 (11 1) 17 (32 1) (32  1) (29  1) 32 41)
("Mike Gagnon"              18 (16 1) 26 (25 1) (30  1) (46  1) 37 43)
("David Halperin"           20 (21 1) 21 (35 1) (31  1) (50  1) 35 42)
("Sarah House"              18 (13 1) 32 (36 1) (31  1) (43  1) 20 42)
("Nicole Johnson"           20 (14 1) 27 (37 1) (32  1) (45  1) 31 52)
("James Killion"            20 (17 1) 24 (30 1) (27  0) (44  1) 31 32)
("Matt Kyros"               #f (17 1) 16 (29 1) (18  0) (#f #f) 31 41)
("Alfredo Lee"              15 (16 1) 26 (25 1) (30  1) (46  1) 37 43)
("Joe Logel"                16 (21 1) 21 (35 1) (31  0) (50  0) 35 42)
("James Manning"            17 (17 1) 24 (30 1) (27  1) (44  1) 31 32)
("Derek Najdzien"           #f (15 1) 14 (16 0) (18  0) (#f #f) #f #f)
("Constantine Nikolopolous" 17 (#f 1) 29 (26 1) (31  0) (41  1) 26 45)
("Matt O'Grady"             #f (12 1) 17 ( 9 1) (21 #f) (31  1) 34 35)
("Kyle Raffile"             16 (11 1) 17 (32 1) (32  0) (29  1) 32 41)
("Kathrin Ritter"           20 (14 1) 27 (37 1) (32  1) (45  0) 31 52)
("Vitaly Shatkovsky"        #f (#f 1) 29 (26 1) (31  1) (41  1) 26 45)
("Janet Wilson"             20 (13 1) 32 (36 1) (31  1) (43  1) 20 42)
))



(define stevie-grades ;; up to date 11-5
'(("Brendan Doherty"     19 (14  1) ( 7  1) (14  1) (28  0) (#f #f) #f)
  ("Damien Angelos"      19 (20  1) (30  1) (25  1) (30  1) (38  1) 24)
  ("Mark Santoski"       16 (20  1) (30  1) (25  1) (30  0) (38  1) 24)
  ("Chris Trammell"      #f (14  1) ( 7  1) (14  1) (28  0) (#f  0) 36)
  ("Sergey Andreev"      #f ( 8  1) ( 9  1) (33  1) (28  1) (43  1) 36)
  ("Kathryn Vanderwyk"   17 (10  1) (32  1) (33  1) (28  1) (43  1) 22)
  ("Jake Dreier"         19 (10  1) (32  1) (33  1) (28  0) (43  1) 22)
  ("Michael Battista"    #f (21  1) (32  1) (34  1) (32  1) (48  1) 35)
  ("Brandon Schory"      19 (21  1) (32  1) (34  1) (32  1) (48  1) 35)
  ("Michael DiStaula"    14 ( 8  1) (21  1) (29  1) (28  1) (40  1) 34)
  ("Michael McIntosh"    #f ( 8  1) (21  1) (29  1) (28  1) (40  1) 34)
  ("Alex Coleman"        18 (11  1) (24  1) (36  1) (29  1) (42  1) 37)
  ("Tim LaRose"          19 (11  1) (24  1) (36  1) (29  0) (42  1) 37)
  ("John Clevesy"        17 (11  1) (25  1) (21  1) (19  0) (32  1) 22)
  ("Matt DeGenarro"      19 (11  1) (25  1) (21  1) (19  0) (32  1) 22)
  ("Christopher Svenson" 18 (11  1) (19  1) (30  1) (25  0) (22  1) 20)
  ("Christopher Umina"   #f (11  1) (19  1) (30  1) (25  0) (22  1) 20)
  ("Adam Gorklo"         14 (20  1) (21  1) (31  1) (32  0) (35 #f) 32)
  ("Patrick Kaeding"     19 (20  1) (21  1) (31  1) (32  1) (35  1) 32)
  ("Andrew Guida"        15 (16  1) (32  1) (36  1) (26  1) (46  1) 33)
  ("Jared Assmus"        20 (16  1) (32  1) (36  1) (26  0) (46  1) 33))
)
