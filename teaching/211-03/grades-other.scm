(module grades-other mzscheme
  (require (lib "list.ss"))
  (provide d:grades f:grades j:grades c:grades)

(define jeffs-grades
 `(
("2825" "AGURKIS,JASON P"          9 Jeff vkp ( 8 10  9 10 2) ((1 21) (1 22) (1 29) (35) (0 14) (1 22) (19) (19) (1 30) (44) ))
("4420" "ANIKUL, ALEXANDER"        9 Jeff  mf (10 15 15 10 4) ((1 21) (1 26) (1 37) (36) (1 13) (1 35) (20) (21) (1 29) (36) ))
("4786" "BARBEE, LINDSEY A"        9 Jeff vkp ( 9 15 15 10 1) ((1 21) (1 26) (1 37) (36) (1 13) (1 35) (20) (21) (1 29) (36) ))
("3644" "BIRON, TIMOTHY W"         9 Jeff  mf (10 14 11 10 4) ((1 21) (1 22) (1 29) (35) (1 14) (1 22) (19) (19) (1 30) (44) ))
("3079" "BRUEN, PATRICK J"         9 Jeff vkp (10 15  9 10 4) ((1 21) (1 27) (1 29) (35) (1 15) (0 35) (25) (21) (1 34) (39) )) 
;("1039" "CHWICK, ADAM S"           8 JEFF RJW ( 6  3  6  3 0) ((0 21) (1 26) (1 38) (36) (0 12) (0 28) (23) (19) (0 33) (43) ))
("2257" "COCUZZO, DANIEL C"        9 JEFF VKP (10 15 15 10 5) ((1 21) (1 22) (1 38) (34) (1 16) (1 35) (21) (21) (1 33) (36) ))
("3931" "DAVENPORT, ZACHARY J"     9 JEFF VKP (10 13 15 10 1) ((1 20) (1 26) (1 31) (35) (1 12) (1 32) (22) (21) (1 30) (39) ))
("2371" "DELORME, NOAH D"          9 JEFF  MF (10 15 15 10 5) ((1 21) (1 26) (1 38) (35) (1 16) (1 32) (22) (17) (1 33) (46) ))
("1098" "DELOUISE, CHRISTOPHER"    9 JEFF  MF ( 6  6  3  1 0) ((1 16) (0 13) (1 24) (34) (0  9) (0 30) (19) (15) (0 20) (36) ))
("7717" "DICKSON, TREVOR J"        8 JEFF RJW ( 9 11 10  5 0) ((1 19) (0 11) (1 24) (36) (0 12) (1 23) (21) (18) (1 28) (25) ))
("9664" "DILLANE, KEVIN W"         9 JEFF  MF (10 15 11  9 4) ((1 16) (1 13) (1 24) (34) (1  9) (1 30) (19) (15) (0 20) (36) ))
("3772" "DONOVAN, MATTHEW D"       9 JEFF VKP (10 15 12 10 4) ((1 21) (1 27) (1 29) (35) (1 15) (1 35) (25) (21) (1 34) (39) ))
;; CARL ("8910" "DURNIAK, CAROLYN S"       8 JEFF VKP ( 8  6  9  6 1) ((1 21) (1 24) (1 37) (35) (1 13) (0 25)))
("2932" "ESPINOLA, ROMINA M"       8 JEFF VKP ( 8 14 15 10 5) ((1 21) (1 23) (1 39) (37) (1 10) (1 32) (21) (17) (1 34) (45) ))
("7006" "FERNANDEZ, JUAN"          8 JEFF  MF ( 8 14 14 10 4) ((0 21) (1 11) (1 36) (36) (1 15) (0 27) (22) (15) (1 33) (33) ))
("8154" "FIER, DAVID"              9 JEFF VKP ( 9 15 12 10 4) ((1 17) (1 22) (1 38) (34) (1 16) (1 35) (21) (21) (1 33) (36) ))
("7128" "FLAMOUROPOULO, DIMITRIOS" 8 JEFF VKP ( 8 15 15  9 4) ((1 21) (1 15) (1 35) (37) (1  9) (1 25) (23) (15) (1 33) (43) ))
("2262" "FRANKLIN, BRIAN J"        9 JEFF RJW (10 11 10  9 2) ((1 18) (1 26) (1 31) (35) (1 12) (0 32) (22) (21) (1 30) (39) ))
("1245" "GARCIA, ARISTIDES"        8 JEFF RJW (10  9  6  7 0) ((1 17) (1 11) (1 36) (36) (1 15) (1 27) (22) (15) (1 33) (33) ))
("6888" "HICKEY, BRIAN W"          8 JEFF RJW ( 9 11  7  8 0) ((1  0) (1  0) (1 29) (35) (1  6) (0 21) (19) (17) (1 00) (32) ))
("6337" "KANESHIRO, CRAIG S"       8 JEFF VKP (10 15 13 10 5) ((1 21) (1 19) (1 36) (28) (1 15) (1 27) (27) (18) (1 32) (40) ))
("5921" "LAFERRIERE, BRIAN S"      8 JEFF  MF (10 15 13 10 5) ((1 21) (1 26) (1 38) (36) (1 12) (1 28) (23) (19) (1 33) (43) ))
("5565" "LEONARD, JONATHAN G"      8 JEFF VKP (10 12 12 10 5) ((1 21) (1 23) (1 28) (31) (0  0) (1 29) (19) (18) (1 32) (36) ))
("1798" "MARTIN, ANDREW A"         8 JEFF  MF (10 14 15 10 4) ((1 21) (1 25) (1 29) (33) (1 16) (1 31) (25) (18) (1 31) (00) ))
;("1252" "MINDER, ALEX"             8 JEFF  MF ( 9  6  7  8 0) ((19) (0) (0) (0) (0) (0 00) (0) (0) (0) (0)))
("7418" "MUI, JERRY C"             8 JEFF RJW ( 8 14 15 10 3) ((1 21) (0 19) (1 36) (28) (0 15) (0 27) (27) (18) (0 32) (40) ))
("3596" "O'CONNOR, MATTHEW N"      9 JEFF  MF ( 7 12 11  7 3) ((1 15) (1 26) (1 38) (35) (0 16) (0 32) (24) (17) (1 33) (46) ))
("9553" "ONIGBANJO, TOLANI L"      8 JEFF  MF (10 10  6  7 1) ((1 21) (0  7) (1 30) (35) (0  6) (0 00) (19) (17) (0 00) (32) ))
("6117" "PECK, DAVID J"            8 JEFF  MF (10 15 12 10 5) ((1  0) (0 25) (1 36) (33) (0 11) (1 31) ( 9) (16) (1 27) (39) ))
("8085" "PETKOV, VENTZISLAV"       8 JEFF VKP (10 14 14 10 5) ((1 21) (1 23) (1 39) (37) (1 10) (1 32) (21) (17) (1 34) (45) ))
;("0787" "POLAD, AHMAD Z"           8 JEFF  MF (             ) ((1 13) (0 11) (1 24) (36) (0 12) (0 23) (21) (18) (0 28) (25) ))
("5366" "SICKLER, JOSHUA D"        8 JEFF  MF ( 8  9 11 10 0) ((1 21) (0 15) (1 35) (37) (0  9) (0 25) (23) (15) (0 33) (43) ))
("3184" "VASQUEZ, CHRISTOPHER"     8 JEFF  MF ( 9 14 13  7 3) ((1 20) (1  7) (1 30) (30) (0 14) (0 27) (17) ( 0) (1 23) (34) ))
("3162" "VEGA, ZYLER"              8 JEFF VKP (10 10 15  8 4) ((1  2) (1 23) (1 28) (31) (1  0) (1 29) (19) (18) (1 32) (36) ))
("6068" "VIGEANT, MATTHEW J"       8 JEFF VKP ( 8 15 12 10 5) ((1 21) (1 25) (1 36) (33) (1 11) (0 31) ( 9) (16) (1 27) (39) ))
("7391" "WEAVER, SAMUEL C"         8 JEFF  MF ( 8 15 15  9 3) ((1 19) (1  0) (1  0) (36) (0  0) (0 00) (0 00) (0) (0) (0)))
("2301" "WISNIEWSKI, DAVID V"      8 JEFF  MF ( 8 11  4 10 1) ((0  0) (1  7) (1 30) (30) (0 14) (1 27) (17) ( 0) (0 23) (34) ))
;("0345" "ZHU, WEN"                 8 JEFF VKP ( 8 11  7  5 0) ((0  0) (1 25) (1 29) (33) (0 16) (0 31) (25) (18) (1 31) (00) ))


))

(define daria-grades
   `(
   ("0092" "AL-DHAMEN, ALI" 1 Daria mf (10 12 13 8 3) ((21) (27) (36) (38) 
(12) (26) (23) (17) (28) (41)))
;   ("8786" "ANDRE, PIERRETTE" 4 Daria vkp (0 0 0 0 0) ((0) (20 0) (35) (37) (0) (0) (0) (0) (0) (0)))
   ("3222" "ATLAS, MICHAEL R" 1 Daria vkp (10 15 14 9 5) ((17) (16) (36) 
(37) (12) (24) (23) (22) (29) (43)))
   ("6378" "BACHUN, NAZAR R" 1 Daria mf (8 6 0 0 0) ((0) (24 0) (37) (35) 
(13 0) (29 0) (23) (18) (31) (43 0)))
   ("1844" "BAXTER, RYAN J" 1 Daria mf (5 15 7 9 1) ((19) (22 0) (35) (37) 
(9 0) (31) (21) (15) (25) (35 0)))
   ("9997" "BERNADEL, KARL-HENS B" 1 Daria mf (8 11 7 7 2) ((20) (23 0) 
(24) (31) (10 0) (20) (20) (18) (26) (38 0)))
   ("9493" "BERNHARDT, CHRISTINE E" 1 Daria vkp (8 15 14 9 4) ((21) (23) 
(24) (31) (10) (20) (20) (18) (26) (38)))
   ("8617" "BONANNO, BRIAN C" 1 Daria mf (9 7 8 9 2) ((17) (26) (39) (0) 
(13 0) (33) (21) (16) (29) (44 0)))
   ("9243" "BUCKLEY, PAUL R" 4 Daria mf (10 12 11 9 3) ((21) (12) (37) (29) 
(11) (17) (3) (16) (30) (17)))
   ("4587" "CALDWELL, ETHAN J" 1 Daria mf (10 14 14 10 5) ((20) (24) (37) 
(35) (13) (29) (23) (18) (31) (43)))
   ("0026" "CATALANO, MARK S" 1 Daria vkp (10 13 14 10 3) ((21) (27) (36) 
(38) (12 0) (26 0) (23) (17) (28) (41)))
("5491" "CIABURRI, NICHOLAS F" 1 Daria vkp (10 15 13 6 4) ((19) (16) 
(36) (37) (12) (24) (23) (22) (29) (43)))
;   ("2292" "CUNNINGHAM, MAURICE L" 1 Daria mf (4 4 4 8 1) ((0) (27 0) (36) 
;(38) (11) (34) (22) (18) (30) (36 0)))
   ("1818" "DILEO, JONATHAN R" 4 Daria mf (10 11 9 1 1) ((19) (12) (37) 
(29) (11 0) (17 0) (3) (16) (30) (17 0)))
   ("2085" "EGAN, JARED M" 1 Daria mf (8 15 10 6 4) ((20) (26) (39) (0) 
(13) (33) (21) (16) (29) (44)))
   ("2808" "GILLMOR, ALEXANDER S" 1 Daria mf (10 15 12 10 5) ((20) (27) 
(36) (38) (11) (34) (22) (18) (30) (36)))
   ("9366" "HANNON-RIZZA, ANDREW M" 4 Daria mf (10 15 11 9 5) ((0) (27) 
(39) (36) (13) (34) (23) (18) (28) (37)))
   ("7082" "HEINEGG, EVAN T" 4 Daria vkp (10 13 14 9 4) ((26) (25) (31) 
(37) (13) (27) (27) (20) (32) (45)))
   ("6311" "HENDERSON, ROBYN L" 4 Daria vkp (10 14 15 10 4) ((21) (25) (24) 
(37) (13) (23) (0) (21) (28) (45)))
   ("0183" "HONICKEL, GARY S" 4 Daria mf (10 15 11 10 2) ((16) (25) (38) 
(29) (11) (17) (8) (18) (25) (42)))
   ("0561" "HUYNH, PHUC N" 4 Daria rjw (10 15 10 6 4) ((19) (25) (38) (29) 
(11) (17) (8) (18) (25) (42)))
   ("7629" "JOHNSON, BRETT M" 4 Daria mf (10 15 15 10 5) ((21) (22) (39) 
(37) (14) (32) (21) (21) (28) (46)))
   ("6425" "JONES, MATTHEW B" 1 Daria mf (10 12 11 8 4) ((17) (22) (35) 
(37) (9) (31) (21) (15) (25) (35  0)))
   ("6434" "KARAMBELAS, CHRISTOPHER" 4 Daria rjw (7 14 12 8 2) ((17) (19) 
(28) (33) (13) (8) (17) (15) (14) (38 0))) ; note 23 changed to 28 in hw3
;   ("3458" "LEWIS, JOHN" 4 Daria mf (10 12 5 10 0) ((17) (15) (23) (35) (10 0) (10) (22) (19) (27) (34 0)))
   ("3769" "LI, ZHONGHUA" 4 Daria vkp (8 11 10 4 0) ((21) (25) (24) (37) 
(13 0) (23) (0) (21) (28) (45)))
   ("9149" "MARTIN, SCOTT F" 4 Daria mf (8 12 12 7 2) ((21) (24 0) (34) 
(37) (11 0) (18 0) (18) (17) (16) (45 0)))
   ("9060" "MERGLER, SLOAN D" 4 Daria rjw (5 9 10 9 3) ((21) (20 0) (35) 
(37) (13 0) (27) (16) (19) (26) (38)))
   ("0680" "NGUYEN, VIET T" 4 Daria mf (7 14 6 4 1) ((0) (5 0) (30) (36) (0 
0) (27) (16) (19) (26) (38)))
   ("4238" "POULOS, GEORGE M" 4 Daria vkp (10 15 15 8 3) ((0) (21) (36) 
(37) (8) (10) (16) (20) (0) (41)))
   ("6893" "ROGODZINSKI, ANDREW" 4 Daria vkp (8 12 14 10 4) ((21) (15) (23) 
(35) (10) (10) (22) (19) (27) (34)))
   ("2741" "SEITELMAN, ARI B" 4 Daria vkp (10 13 15 9 5) ((19) (25) (31) 
(37) (13) (27) (27) (20) (0) (45)))
   ("5552" "SMITH, JONATHAN T" 4 Daria mf (10 15 12 10 5) ((20) (27) (39) 
(36) (13) (34) (23) (18) (28) (37)))
   ("9216" "SOLOMON, JASON K" 4 Daria rjw (6 14 6 4 0) ((14) (19) (28) (33) (13 0) (8 0) (17) (15) (14) (38 0)))
   ("6737" "TAMOWSKI, DANIEL J" 4 Daria mf (10 15 11 10 0) ((21) (24) (34) 
(37) (11 0) (18) (18) (17) (16) (45)))
   ("0420" "TON, PETER" 1 Daria rjw (8 15 15 10 5) ((21) (27) (36) (38) (12) 
(27) (23) (17) (28) (0)))
   ("7667" "TORGERSEN, MARK P" 4 Daria mf (7 9 5 3 0) ((0) (5 0) (30) (36) 
(13 0) (27 0) (16) (19) (26) (38 0)))
;   ("5357" "WARD, WILLIAM J" 4 Daria mf (10 14 11 6 0) ((14) (21) (36) (37) (8) (10 0) (16) (20) (0) (41 0)))
   ("3694" "ZHU, XUAN" 4 Daria vkp (7 10 15 10 5) ((21) (25) (24) (37) (13 0) 
(23) (0) (21) (28) (45)))
   ("2436" "ZHURAVLEVA, NATALIE A" 4 Daria mf (10 13 12 9 1) ((19) (22) 
(39) (37) (14) (32) (21) (21) (28) (46)))))

(define felix-grades 
'(
;("CUFONE, AGOSTINO J"  ((18) (0 0) (35) (36) (#f 7) (#f 18) (18) (#f) (#f #f) (#f))) 
;("LAI, BAO" ((19) (0 0) (26) (35) (0 7) (0 23) (20) (20) (#f #f) (#f))) 
("CAPRICE, JOHN J"  ((19) (1 21) (33) (35) (1 13) (1 30) (21) (21) (1 27) (#f))) ("AROMANDO, MATTHEW T"  ((20) (0 0) (33) (35) (0 13) (0 30) (21) (21) (0 27) (#f))) ("CZERW, ANASTASIA M"  ((19) (1 18) (35) (36) (0 7) (0 18) (18) (18) (1 11) (#f))) ("ARANGO, NICHOLAS J"  ((15) (1 18) (29) (35) (1 7) (0 17) (18) (16) (1 11) (#f))) ("CLARK, DARYL W" ((19) (1 18) (29) (35) (0 7) (1 17) (18) (16) (1 11) (#f))) ("SWEENEY, BRIAN G"  ((20) (1 26) (35) (33) (1 10) (0 25) (17) (20) (0 32) (32))) ("FOWLER, MATTHEW S"  ((20) (1 26) (35) (33) (1 10) (1 25) (17) (20) (1 32) (32))) ("MARCHENKO, IGOR A"  ((21) (1 24) (35) (33) (1 10) (1 25) (17) (20) (1 32) (32))) ("JOSEPH, ISAAC L" ((8) (0 0) (35) (15) (0 6) (0 10) (4) (#f) (1 21) (14))) 
;("MINDER, ALEX" ((19) (0 0) (35) (15) (0 6) (0 10) (4) (#f) (#f 21) (14))) 
("OBER, RACHEL A" ((18) (1 19) (31) (23) (0 #f) (0 17) (7) (15) (1 21) (15))) ("MCCORMACK, KATE M"  ((18) (1 19) (31) (23) (0 #f) (0 17) (7) (15) (1 21) (15))) ("TASSINARI, TIMOTHY P"  ((20) (1 21) (33) (36) (1 13) (1 18) (21) (19) (1 28) (25))) ("JOHNSON, RASHAINE A"  ((18) (1 21) (33) (36) (1 13) (0 18) (21) (19) (#f #f) (25))) ("SIMONS, JONATHAN S"  ((21) (1 26) (39) (36) (1 10) (1 30) (23) (18) (1 30) (36))) ("SEVIGNY, RICHARD F"  ((21) (1 26) (39) (36) (0 10) (1 30) (23) (18) (1 30) (36))) ("LEBLANC, ANDREW R"  ((21) (1 22) (34) (31) (1 12) (1 28) (17) (19) (1 27) (30))) ("PEZZUTO, DOMINIC S"  ((21) (1 22) (34) (31) (1 12) (0 28) (17) (19) (1 27) (30))) ("ELWOOD, GREGORY R"  ((21) (1 25) (39) (34) (1 6) (1 21) (20) (20) (1 22) (26))) ("ROSS, DAVID W"  ((13) (#f 25) (39) (34) (#f 6) (0 21) (20) (20) (#f #f) (26))) ("MURPHY, DANIEL J"  ((21) (1 20) (36) (35) (0 13) (1 #f) (22) (21) (1 27) (37))) 
;("LANDRY, JOSEPH R"  ((17) (1 20) (36) (35) (0 13) (#f #f) (22) (21) (#f 27) (37))) 
("CHICK, GREGORY E"  ((21) (1 27) (32) (28) (0 #f) (1 27) (21) (18) (1 29) (39))) ("GUNKEL, ADAM K" ((#f) (1 27) (32) (28) (1 #f) (1 27) (21) (18) (1 29) (39))) ("BAUERMEISTER, MISCHA K"  ((17) (1 17) (26) (31) (1 8) (1 27) (15) (#f) (1 33) (37))) ("WANAMAKER, BONNI M"  ((21) (1 17) (26) (31) (0 8) (1 27) (15) (#f) (0 33) (37))) ("ALLECA, DAVID J"  ((21) (1 27) (39) (35) (1 11) (1 18) (26) (21) (1 33) (39))) ("BARRY, CHRISTOPHER"  ((20) (0 0) (39) (35) (0 11) (0 18) (26) (21) (1 33) (39))) ("LOMBARDO, JASON I"  ((21) (1 21) (35) (33) (1 12) (1 26) (21) (17) (1 31) (35))) ("WASKEWICH, RYAN G"  ((21) (0 0) (35) (33) (0 12) (#f 26) (21) (17) (#f 31) (35))) ("ALDRICH, THOMAS P"  ((21) (1 25) (28) (37) (1 9) (1 27) (22) (17) (1 31) (31))) ("BRENDEL, WILLIAM E"  ((19) (1 25) (28) (37) (1 9) (1 27) (22) (17) (1 31) (31))) ("MLODZIANOSKI, STEVEN J"  ((21) (1 19) (28) (38) (1 10) (1 31) (24) (20) (1 32) (31))) ("STRAUSS, DAVID A"  ((19) (#f 19) (28) (38) (#f 10) (#f 31) (24) (20) (#f #f) (31))) ("SPINNEY, KIMBERLY C"  ((18) (0 0) (30) (33) (0 #f) (0 30) (20) (16) (0 27) (35))) ("TRANG, HU J" ((21) (1 26) (30) (33) (0 #f) (0 30) (20) (16) (1 27) (35))) 
("LU, JIMMY" ((18) (1 14) (26) (35) (0 7) (0 23) (20) (20) (1 28) (39))) ("ROSENHOLTZ, JENNIFER L"  ((18) (1 20) (29) (#f) (#f #f) (#f #f) (#f) (16) (#f 28) (39))))
)
  
  
  (define carl-grades   
   `(
;("2023" "BADALAMENTI, ALEXANDER"  5 Carl mf  ( 3 10  0 03  0) ((16)   ( 0)   (22)   (31)   ( 9 0) (21 0) (20)   (13)   (23 0) (39) ))     
("9016" "BUCK, JEFFREY R"         5 Carl mf  (10 15 10  9 00) ((11)   (20)   (28)   (24)   ( 8 0) ( 0 0) ( 4)   ( 0)   ( 4 0) ( 0) ))     ("3082" "CABRAL, ROBERTO M"      10 Carl mf  (10 14  9 10  1) ((19)   (17)   (26)   (30)   (10)   (17 0) (13)   (17)   (21 1) ( 9) ))     ("6783" "CASHORALI, TANYA M"     10 Carl vkp (10 14 14  9 03) ((20)   (24)   (27)   (29)   ( 9)   (21 1) (18)   (15)   (26 1) (27) ))     
;("4922" "CHAN, TIMOTHY C"         5 Carl rjw ( 4 12  6 06  0) (( 0)   (24)   (36)   (37)   ( 7 0) (17 0) (16)   (15)   (17 0) (21) ))     
("4806" "CONNOR, SHAUN D"         5 Carl mf  (10 13 13  7 03) ((16)   (24)   (36)   (37)   ( 7)   (17 0) (16)   (15)   (17 1) (21) ))     
("3549" "CUNDARI, GEOFFREY F"     5 Carl rjw ( 7 11  9 03  0) ((11)   ( 0)   (28)   (24)   ( 8 0) ( 0 0) ( 4)   ( 0)   ( 4 0) ( 0) ))     
("5622" "DESTEFANO, STEVEN E"     5 Carl vkp (10 13 15 10  4) ((19 0) ( 0)   (38)   (35)   (13 0) (22 0) (17)   (19)   (32 1) (42) ))     ("8910" "DURNIAK, CAROLYN S"      8 Jeff vkp ( 8  6  9  6  1) ((21)   (24)   (37)   (35)   (13)   (29 0) (18)   (16)   (30 1) (39) ))     ("1881" "HANRAHAN, KAITLYN F"    10 Carl vkp (10 15 15 10  5) ((19)   (15)   (27)   (30)   (10)   (23 0) (12)   (15)   (28 1) (31) ))     ("2186" "HOLDER, HASANI"          5 Carl vkp (10 15 15 10  4) ((19)   (20)   (38)   (35)   (13)   (22 1) (17)   (19)   (32 1) (42) ))     ("7271" "HUBER, LAURA A"          5 Carl mf  (10 12 15 10  5) ((16)   (18)   (37)   (37)   ( 7)   (25 1) (18)   (19)   (30 1) (38) ))     ("2449" "JARMEL, DAVID C"        10 Carl mf  ( 8 15 11 10  1) ((13)   (19)   (27)   (23)   ( 9)   (21 1) (13)   (14)   ( 0 1) (34) ))     ("0358" "KACZYNSKI, KATARZYNA"   10 Carl rjw (10 14 10  3 00) ((19)   ( 0)   (34)   (24)   ( 9)   (19 1) (12)   (15)   (28 1) (31) ))     ("4466" "LEE, JOHN F"             5 Carl vkp (10 13  9 10  3) ((16)   ( 0)   (22)   (32)   ( 9)   (21 0) (20)   (13)   (23 1) (39) ))     ("0027" "LESZCZYNSKI, MICHAEL T"  5 Carl rjw ( 8 13 12 10  3) ((20)   (12)   (20)   (29)   (10 0) (21 0) (18)   (13)   (27 1) (40) ))     ("1496" "LUMBIS, ALFRED P"        5 Carl vkp ( 8 07 12  7 03) ((20)   (24)   (20)   (29)   (10)   (21 1) (18)   (13)   (27 1) (40) ))     ("5880" "MACLELLAN, PETER L"     10 Carl vkp (10 15 12 10  5) ((19)   (15)   (27)   (30)   (10)   (23 0) (12)   (16)   (29 1) (30) ))     ("7239" "MARK, AMY"              10 Carl vkp (10 15 13 10  5) ((19)   (22)   (30)   ( 6)   (10)   (12 1) (14)   (20)   ( 0 0) (28) ))     ("2951" "MEDICO, ANDREW"         10 Carl vkp ( 9 14 15 10  5) ((21)   (24)   (37)   (31)   (13)   (29 1) (18)   (16)   (30 1) (39) ))     ("8171" "MULLEN, JAMES H"        10 Carl vkp (10 15 15 10  5) ((12)   (25)   (32)   (32)   (11)   (29 1) (20)   (16)   (32 0) (37) ))     ("3395" "NOAD, DEREK A"          10 Carl mf  (10 15 15 10  5) ((15)   (19)   (32)   (23)   (13)   (20 1) (17)   (13)   (25 1) (28) ))     ("7682" "OTTO, GEORGIA M"        10 Carl rjw ( 8 13 12  9 05) ((21)   ( 0)   (30)   (28)   (11 0) (29 1) (20)   (16)   (32 1) (37) ))     ("4761" "PARRELLA, DANIEL S"     10 Carl rjw ( 9 14 10  9 00) ((13)   (15)   (27)   (30)   (10 0) (23 1) (12)   (16)   (29 1) (30) ))     ("3139" "REILLY, BRETT W"        10 Carl vkp (10 15 14 10  5) ((16)   (12)   (17)   (31)   (12)   ( 8 1) ( 0)   (13)   (17 1) (34) ))     ("7983" "ROGERS, BRETT E"        10 Carl vkp (10 10 13 10  0) ((19)   (24)   (27)   (29)   ( 9 0) (21 0) (18)   (15)   (26 1) (27) ))     ("1379" "RYEE, TAE-HYUNG"        10 Carl vkp (10 15 12  4 00) (( 0)   (17)   (26)   (30)   (10)   (17 0) (13)   (17)   (21 0) ( 9) ))     ("4449" "SABANTY, CHRISTOPHER"   10 Carl mf  ( 7 13  4 08  1) (( 9)   ( 0)   (27)   (19)   ( 2 0) ( 5 0) ( 3)   ( 5)   ( 2 0) (10) ))     ("3681" "SCHAFFER, RYAN H"       10 Carl mf  (10 11 14 10  0) (( 0)   (22)   (30)    (6)   (10 0) (12 0) (14)   (20)   ( 0 1) (28) ))     ("1371" "SCHMITT, KURT"          10 Carl mf  (10 11 11  9 01) ((15)   (19)   (32)   (23)   (13 0) (20 1) (17)   (13)   (25 1) (28) ))     
;("1792" "SCHNEIDER, ALAIN"       10 Carl rjw ( 1 11  4 00  0) ((19)   ( 0)   (27)   (19)   ( 2 0) ( 5 0) ( 3)   ( 5)   ( 2 0) (10) ))     
("5011" "SPELMAN, JAMES J"       10 Carl vkp ( 7 11 14  7 05) ((16)   ( 0)   (32)   (28)   (12 0) (11 1) (11)   (15)   (18 1) (32) ))     ("5842" "ST-JOHN, WILLIAM"       10 Carl mf  (10 15 13  8 00) ((13)   ( 0)   (32)   (28)   (12)   (11 1) (11)   (15)   (18 1) (32) ))     ("2973" "WILLIAMS, CATHERINE P"  10 Carl rjw (10 15 11  9 00) ((19)   ( 0)   (34)   (24)   ( 9)   (19 0) ( 4)   (16)   ( 6 0) ( 0) ))))
    
  
  (define f:grades (map (lambda (x) (cons (car x) (cadr x))) felix-grades)) 
  (define (transform l) (map (lambda (x) (cons (cadr x) (list-ref x 6))) l))
  (define (swap x) 
    (if (= 2 (length x))
        (list (cadr x) (car x))
        x))
  (define (transform2 l) (map (lambda (x) (cons (cadr x) (map swap (list-ref x 6)))) l))
  (define d:grades (transform2 daria-grades))
  (define j:grades (transform jeffs-grades))
  (define c:grades (transform2 carl-grades))
  
  
  )
