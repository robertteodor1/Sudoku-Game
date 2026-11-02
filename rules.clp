
;Functie care returneaza lista fara primul element
(deffunction rest-list (?list)
  (if (<= (length$ ?list) 1) then
    return (create$)
  else
    return (subseq$ ?list 2 (length$ ?list))
  )
)
;Functie care calculeaza numarul de zero-uri din lista
(deffunction count-nonzero (?list)
  (if (eq (length$ ?list) 0) then
    return 0
  else
    return (+ (if (neq (nth$ 1 ?list) 0) then 1 else 0)
              (count-nonzero (rest-list ?list)))
  )
)
;Regula pentru completarea unei celule atunci cand este singura celula libera de pe o linie
;(completează <coord_i> <coord_j> <n> ) : Jucătorul dorește să pună cifra n pe poziția (i,j).
;(coloana <coord_j> ):Coloana i din tablă de joc.
;(linie <coord_i> ):Linia i din tablă de joc.
;(celula  <coord_i>  <coord_j>  <n> )  : Cifra n alesa de jucător pentru celulă(i,j).

(defrule R_linie
   (declare (salience 8))
   ?a <- (completeaza ?i ?j ?n)
   ?l <- (linie ?i $?v)
   ?c <- (coloana ?j $?val)
   ?x <- (celula ?i ?j 0)
   (test (and 
           (eq (length$ $?v) 9)
           (eq (count-nonzero $?v) 8)
           (eq (nth$ ?i $?v) 0)))
=>
   (retract ?x ?a ?l ?c)
   (assert (celula ?i ?j ?n))
   (bind ?noua-linie (replace$ $?v ?j ?j ?n))
   (assert (linie ?i ?noua-linie))
   (bind ?noua-coloana (replace$ $?val ?i ?i ?n))
   (assert (coloana ?j ?noua-coloana))
   (printout t "Celula completata cu " ?n " la coordonatele (" ?i "," ?j ") pe linie." crlf)
)

;Regula pentru completarea unei celule atunci cand este singura celula libera de pe o coloana 
;(completează <coord_i> <coord_j> <n> ) : Jucătorul dorește să pună cifra n pe poziția (i,j).
;(coloana <coord_j> ):Coloana i din tablă de joc.
;(linie <coord_i> ):Linia i din tablă de joc.
;(celula  <coord_i>  <coord_j>  <n> )  : Cifra n alesa de jucător pentru celulă(i,j).	

(defrule R_coloana
  (declare (salience 8))
  ?a <- (completeaza ?i ?j ?n)
  ?c <- (coloana ?j $?val)
  ?b <- (linie ?i $?v)
  ?x <- (celula ?i ?j 0)
  (test (and 
    (eq (length$ $?val) 9)
    (eq (count-nonzero $?val) 8)
    (eq (nth$ ?j $?v) 0)))
=>
  (retract ?x ?a ?b ?c)
  (assert (celula ?i ?j ?n))
  (bind ?noua-linie (replace$ $?v ?j ?j ?n))
  (assert (linie ?i ?noua-linie))
  (bind ?noua-coloana (replace$ $?val ?i ?i ?n))
  (assert (coloana ?j ?noua-coloana))
  (printout t "Celula completata cu " ?n " la coordonatele (" ?i "," ?j ") pe coloana." crlf)
)

;Regula de invalidare unei cifre care este deja pe coloana 
;(completează <coord_i> <coord_j> <n> ) : Jucătorul dorește să pună cifra n pe poziția (i,j).
;(celula  <coord_i>  <coord_j>  <n> ): Cifra n alesa de jucător pentru celulă(i,j).	
;(este-pe-coloana <coord_j>  cifra  <n> <coord_i_celula> <coord_k_celula> )  : Cifra n există deja în coloana j pe poziția (i,k).

(defrule R_invalidare-coloana
	
	(declare(salience 10))
	;(completează <coord_i> <coord_j> <n> )
    ?a <- (completeaza ?i ?j ?n)
	(celula ?i ?j 0)
    (este-pe-coloana ?j cifra ?n ?x2 ?y2)
=>
	
	(assert (elimina-candidat ?n ?i ?j))
    (printout t "Eroare: cifra " ?n " nu se poate pune la pozitiile: " ?i " " ?j " este deja pe coloana " ?j crlf)
    (retract ?a)
)

;Regula de invalidare daca cifra este pe linie deja   
;(completează <coord_i> <coord_j> <n> ) : Jucătorul dorește să pună cifra n pe poziția (i,j).
;(celula  <coord_i>  <coord_j>  <n> ): Cifra n alesa de jucător pentru celulă(i,j).	
;(este-pe-rând  <coord_i>  cifra  <n>  <coord_j_celula> <coord_k_celula> )  :  Cifra n există deja în rândul i, pe poziția (j,k).

(defrule R_invalidare-linie
	(declare(salience 10))
	;(completează <coord_i> <coord_j> <n> )
    ?a <- (completeaza ?i ?j ?n)
	(celula ?i ?j 0)
    (este-pe-rand ?i cifra ?n ?x1 ?y1) 

=>
	(assert (elimina-candidat ?n ?i ?j))
    (printout t "Eroare: cifra " ?n " nu se poate pune la pozitiile: " ?i " " ?j " este deja pe linia " ?i crlf)
    (retract ?a)
)

;Regula pentru invalidarea unei cifre daca exista deja in patrat
;(completează <coord_i> <coord_j> <n> ) : Jucătorul dorește să pună cifra n pe poziția (i,j).
;(celula  <coord_i>  <coord_j>  <n> ): Cifra n alesa de jucător pentru celulă(i,j).	
;(este-în-pătrat <nr> cifra  <n>  <coord_i_celula> <coord_j_celula>)  : Cifra n există deja în pătratul 3x3 cu pozitia nr , pe poziția (i,j).

(defrule R_invalidare-patrat
	(declare(salience 10))
	;(completează <coord_i> <coord_j> <n> )
    ?a <- (completeaza ?i ?j ?n)
	(celula ?i ?j 0)
    (este-in-patrat ?nr cifra ?n ?x3 ?y3)
	(test (= ?nr (+ (* (div (- ?i 1) 3) 3) (div (- ?j 1) 3) 1)))

 
=>
	(assert (elimina-candidat ?n ?i ?j))
    (printout t "Eroare: cifra " ?n " nu se poate pune la pozitiile: " ?i " " ?j " este deja in patratul " ?nr crlf)
    (retract ?a)
)

;Regula de invalidarea unei cifre daca celula este deja completata
;(completează <coord_i> <coord_j> <n> ) : Jucătorul dorește să pună cifra n pe poziția (i,j).
;(celula  <coord_i>  <coord_j>  <n> ): Cifra n alesa de jucător pentru celulă(i,j).	

(defrule R_invalidare
	(declare(salience 10))
	;(completează <coord_i> <coord_j> <n> )
    ?a <- (completeaza ?i ?j ?n)
	(celula ?i ?j ?x)
	(test (neq ?x 0))

=>
	(assert (elimina-candidat ?n ?i ?j))
    (printout t "Eroare: cifra " ?n " nu se poate pune la pozitiile:" ?i " " ?j   crlf)
    (retract ?a)
)

; Regula de completarea unei cifre in patrat unde se regasesc deja 8 numere
;(completează <coord_i> <coord_j> <n> ) : Jucătorul dorește să pună cifra n pe poziția (i,j).
;(celula  <coord_i>  <coord_j>  <n> ): Cifra n alesa de jucător pentru celulă(i,j).
;(linie <coord_i> ):Linia i din tablă de joc.
;(coloana <coord_j> ):Coloana i din tablă de joc.
;(este-în-pătrat <nr> cifra  <n>  <coord_i_celula> <coord_j_celula>)  : Cifra n există deja în pătratul 3x3 cu pozitia nr , pe poziția (i,j).

	
(defrule R_completare-patrat-simplu
	(declare(salience 6))
	;(completează <coord_i> <coord_j> <n> )
    ?a <- (completeaza ?i ?j ?n)
    ?x <- (celula ?i ?j 0)
    ?r <- (linie ?i $?v)
    ?c <- (coloana ?j $?val)
	?b<-(este-in-patrat ?nr cifra 0 ?i ?j)
    (test (= ?nr (+ (* (div (- ?i 1) 3) 3) (div (- ?j 1) 3) 1)))
    (not (este-pe-rand ?i cifra ?n ? ?))
    (not (este-pe-coloana ?j cifra ?n ? ?))
=>
    (retract ?a ?x ?r ?c ?b)
    (assert (celula ?i ?j ?n))
    (bind ?v_noua (replace$ ?v ?j ?j ?n))
    (assert (linie ?i ?v_noua))
    (bind ?c_noua (replace$ ?val ?i ?i ?n))
    (assert (coloana ?j ?c_noua))
    (assert (este-pe-rand ?i cifra ?n ?i ?j))
    (assert (este-pe-coloana ?j cifra ?n ?i ?j))
    (assert (este-in-patrat ?nr cifra ?n ?i ?j))
    (printout t "Cifra " ?n " a fost completata pe pozitia (i:" ?i " j:" ?j ") in patratul " ?nr crlf)
)

(defrule R_completare-patrat-general
  (declare(salience 6))
  ;(completează <coord_i> <coord_j> <n> )
  ?c <- (celula ?i ?j 0)
  (test (>= ?i 1)) (test (<= ?i 9))
  (test (>= ?j 1)) (test (<= ?j 9))
  (test (neq (mod (- ?i 1) 3) -1))
  (test (neq (mod (- ?j 1) 3) -1))
  ?a <- (este-in-patrat ?nr cifra ?n1 ?i1 ?j1)
  (test (= ?nr (+ (* (div (- ?i 1) 3) 3) (div (- ?j 1) 3) 1)))
  (este-in-patrat ?nr cifra ?n2 ?i2 ?j2&:(neq ?n2 ?n1))
  (este-in-patrat ?nr cifra ?n3 ?i3 ?j3&:(and (neq ?n3 ?n1) (neq ?n3 ?n2)))
  (este-in-patrat ?nr cifra ?n4 ?i4 ?j4&:(and (neq ?n4 ?n1) (neq ?n4 ?n2) (neq ?n4 ?n3)))
  (este-in-patrat ?nr cifra ?n5 ?i5 ?j5&:(and (neq ?n5 ?n1) (neq ?n5 ?n2) (neq ?n5 ?n3) (neq ?n5 ?n4)))
  (este-in-patrat ?nr cifra ?n6 ?i6 ?j6&:(and (neq ?n6 ?n1) (neq ?n6 ?n2) (neq ?n6 ?n3) (neq ?n6 ?n4) (neq ?n6 ?n5)))
  (este-in-patrat ?nr cifra ?n7 ?i7 ?j7&:(and (neq ?n7 ?n1) (neq ?n7 ?n2) (neq ?n7 ?n3) (neq ?n7 ?n4) (neq ?n7 ?n5) (neq ?n7 ?n6)))
  (este-in-patrat ?nr cifra ?n8 ?i8 ?j8&:(and (neq ?n8 ?n1) (neq ?n8 ?n2) (neq ?n8 ?n3) (neq ?n8 ?n4) (neq ?n8 ?n5) (neq ?n8 ?n6) (neq ?n8 ?n7)))
  ?x<-(completeaza ?i ?j ?n)
=>
  (retract ?x ?c)
  (assert (celula ?i ?j ?n))
  (bind ?toate (create$ 1 2 3 4 5 6 7 8 9))
  (bind ?cifre (create$ ?n1 ?n2 ?n3 ?n4 ?n5 ?n6 ?n7 ?n8))
  (if (not (member$ 1 ?cifre)) then (bind ?lipsa 1)
 else (if (not (member$ 2 ?cifre)) then (bind ?lipsa 2)
 else (if (not (member$ 3 ?cifre)) then (bind ?lipsa 3)
 else (if (not (member$ 4 ?cifre)) then (bind ?lipsa 4)
 else (if (not (member$ 5 ?cifre)) then (bind ?lipsa 5)
 else (if (not (member$ 6 ?cifre)) then (bind ?lipsa 6)
 else (if (not (member$ 7 ?cifre)) then (bind ?lipsa 7)
 else (if (not (member$ 8 ?cifre)) then (bind ?lipsa 8)
 else (bind ?lipsa 9)))))))))
  (bind ?nr (+ (* (div (- ?i 1) 3) 3) (div (- ?j 1) 3) 1))
   (assert(este-pe-rand ?i cifra ?n ?i ?j))
   (assert(este-pe-coloana ?j cifra ?n ?i ?j))
   (bind ?linie (div (- ?i 1) 3))
   (bind ?coloana (div (- ?j 1) 3))
   (bind ?nr (+ (* ?linie 3) ?coloana 1))
   (assert (este-in-patrat ?nr cifra ?n ?i ?j))
  (printout t " Patrat " ?nr ": completam (" ?i "," ?j ") cu cifra lipsa " ?lipsa crlf)
)

;Regula de completarea unei cifre daca nu este pe linie, coloana sau in patrat
;(completează <coord_i> <coord_j> <n> ) : Jucătorul dorește să pună cifra n pe poziția (i,j).
;(celula  <coord_i>  <coord_j>  <n> ): Cifra n alesa de jucător pentru celulă(i,j).
;(linie <coord_i> ):Linia i din tablă de joc.
;(coloana <coord_j> ):Coloana i din tablă de joc.
;(este-în-pătrat <nr> cifra  <n>  <coord_i_celula> <coord_j_celula>)  : Cifra n există deja în pătratul 3x3 cu pozitia nr , pe poziția (i,j)

(defrule R_validare-completare
	(declare(salience 5))
   ;(completează <coord_i> <coord_j> <n> )
   ?a <- (completeaza ?i ?j ?n)
   ?b <- (celula ?i ?j 0)
   ?c <- (coloana ?j $?val)
   ?d <- (linie ?i $?v)
    (not(este-in-patrat ?nr cifra ?n ?i ?j))
    (not(este-pe-rand ?i cifra ?n ?i ?j))
	(not(este-pe-coloana ?j cifra ?n ?i ?j))
	(not(elimina-candidat ?n ?i ?j))
    
=>
   (assert(este-pe-rand ?i cifra ?n ?i ?j))
   (assert(este-pe-coloana ?j cifra ?n ?i ?j))
   (bind ?linie (div (- ?i 1) 3))
   (bind ?coloana (div (- ?j 1) 3))
   (bind ?nr (+ (* ?linie 3) ?coloana 1))
   (assert (este-in-patrat ?nr cifra ?n ?i ?j))
   (retract ?a ?b)
   (printout t "Cifra " ?n " a fost completata pe pozitia cu coordonatele i:" ?i " si j:" ?j crlf)
)