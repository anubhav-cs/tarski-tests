; IPC5 Domain: Pathways Propositional
; Authors: Yannis Dimopoulos, Alfonso Gerevini and Alessandro Saetti

(define (domain Pathways-Propositional) 
(:requirements :typing :adl)  

(:types level molecule - object
        simple complex - molecule) 

(:constants c-Abl-pRbp1p2 cdc25A cdc25Ap1 cdk1 cdk1p1p2p3-cycA cdk1p3-cycA cdk1p3-cycB cdk2-cycA-E2F13p1 cdk2-cycEp1 cdk2p1-cycA-E2F13p1 cdk2p2-cycA-E2F13 cdk46 cdk46-cycD cdk46-cycDp1 cdk46p2 cdk46p2-cycD cdk46p2-cycDp1 CEBP-pRbp1-gP DMP1p1-cycD HDAC1-pRb-E2F13-DP12-gE2 p107 p130-E2F4-DP12p1-gE2 p16-cdk46 p16-cdk46p2 p27-cdk2p1-cycA p27-cdk2p2-cycEp1 p27-cdk46-cycD p27-cdk46-cycDp1 p27-cdk46p1p2-cycD p27-cdk46p2-cycD p27-cdk46p2-cycDp1 p27p1-cdk2-cycA p27p1-cdk2-cycEp1 p27p1-cdk2p1-cycA p27p1-cdk2p1-cycEp1 p27p1-cdk2p1p2-cycA p27p1-cdk2p2-cycE p27p1-cdk46-cycD p27p1-cdk46-cycDp1 p27p1-cdk46p1-cycD p27p1-cdk46p1-cycDp1 p27p1-cdk46p1p2-cycDp1 p27p1-cdk46p2-cycD p27p1-cdk46p2-cycDp1 p57-cdk2p1-cycA p57-cdk46-cycD p57-cdk46-cycDp1 p57-cdk46p2-cycD p57-cdk46p2-cycDp1 p57p1-cdk46-cycD p57p1-cdk46-cycDp1 p57p1-cdk46p1p2-cycD p57p1-cdk46p2-cycD p57p1-cdk46p2-cycDp1 p68p1p2 pRbp1-E2F4-DP12p1 Raf1-cdc25A Raf1-cdc25Ap1 Skp2-cdk2p1-cycA Skp2-cdk2p1p2-cycA Skp2p1-Skp1p1 Skp2-Skp1p1-cdk2-cycA Skp2-Skp1p1-cdk2p1-cycA Skp2-Skp1p1-cdk2p1p2-cycA Skp2-Skp1p1-cdk2p2-cycA SL1p1 SP1-E2F13p1 SP1-E2F13p1-gP  - complex)

(:predicates 
	     (association-reaction ?x1 ?x2 - molecule ?x3 - complex)
	     (catalyzed-association-reaction ?x1 ?x2 - molecule ?x3 - complex)
	     (synthesis-reaction ?x1 ?x2 - molecule)
             (possible ?x - molecule) 	
	     (available ?x - molecule)
             (chosen ?s - simple)
	     (next ?l1 ?l2 - level)
	     (num-subs ?l - level)
	     (goal1)
	     (goal2)
	     (goal3)
	     (goal4)
	     (goal5)
	     (goal6)
	     (goal7)
	     (goal8)
	     (goal9)
	     (goal10)
	     (goal11)
	     (goal12)
	     (goal13)
	     (goal14)
	     (goal15)
	     (goal16)
	     (goal17)
	     (goal18)
	     (goal19)
	     (goal20)
	     (goal21)
	     (goal22)
	     (goal23)
	     (goal24)
	     (goal25)
	     (goal26)
	     (goal27)
	     (goal28)
	     (goal29)
	     (goal30)
	     (goal31)
	     (goal32)
	     (goal33)
	     (goal34))


(:action choose
 :parameters (?x - simple ?l1 ?l2 - level)
 :precondition (and (possible ?x) (not (chosen ?x)) 
		    (num-subs ?l2) (next ?l1 ?l2))
 :effect (and (chosen ?x) (not (num-subs ?l2)) (num-subs ?l1)))

(:action initialize
  :parameters (?x - simple)
  :precondition (and (chosen ?x))
  :effect (and (available ?x)))

(:action associate
 :parameters (?x1 ?x2 - molecule ?x3 - complex)
 :precondition (and (association-reaction ?x1  ?x2  ?x3) 
		    (available ?x1) (available ?x2))
 :effect (and  (not (available ?x1)) (not (available ?x2)) (available ?x3)))

(:action associate-with-catalyze 
 :parameters (?x1 ?x2 - molecule ?x3 - complex)
 :precondition (and (catalyzed-association-reaction ?x1 ?x2 ?x3) 
		    (available ?x1) (available ?x2))
 :effect (and (not (available ?x1)) (available ?x3)))

(:action synthesize
 :parameters (?x1 ?x2 - molecule)
 :precondition (and (synthesis-reaction ?x1 ?x2) (available ?x1))
 :effect (and (available ?x2)))



(:action DUMMY-ACTION-1
 :parameters ()
 :precondition
	(or (available pRbp1-E2F4-DP12p1)
	    (available cdk1p1p2p3-cycA))
 :effect (and (goal1)))

(:action DUMMY-ACTION-2
 :parameters ()
 :precondition
	(or (available p27p1-cdk46p2-cycD)
	    (available p27-cdk46-cycDp1))
 :effect (and (goal2)))

(:action DUMMY-ACTION-3
 :parameters ()
 :precondition
	(or (available cdk46p2-cycD)
	    (available HDAC1-pRb-E2F13-DP12-gE2))
 :effect (and (goal3)))

(:action DUMMY-ACTION-4
 :parameters ()
 :precondition
	(or (available p57p1-cdk46p2-cycDp1)
	    (available p27p1-cdk46-cycD))
 :effect (and (goal4)))

(:action DUMMY-ACTION-5
 :parameters ()
 :precondition
	(or (available cdk46-cycDp1)
	    (available p16-cdk46p2))
 :effect (and (goal5)))

(:action DUMMY-ACTION-6
 :parameters ()
 :precondition
	(or (available p57-cdk46-cycDp1)
	    (available Raf1-cdc25Ap1))
 :effect (and (goal6)))

(:action DUMMY-ACTION-7
 :parameters ()
 :precondition
	(or (available p16-cdk46)
	    (available p130-E2F4-DP12p1-gE2))
 :effect (and (goal7)))

(:action DUMMY-ACTION-8
 :parameters ()
 :precondition
	(or (available p27p1-cdk46-cycDp1)
	    (available p27p1-cdk46p2-cycDp1))
 :effect (and (goal8)))

(:action DUMMY-ACTION-9
 :parameters ()
 :precondition
	(or (available p27p1-cdk2p1-cycEp1)
	    (available cdk46p2))
 :effect (and (goal9)))

(:action DUMMY-ACTION-10
 :parameters ()
 :precondition
	(or (available p57p1-cdk46p2-cycD)
	    (available cdk46))
 :effect (and (goal10)))

(:action DUMMY-ACTION-11
 :parameters ()
 :precondition
	(or (available p27-cdk46-cycD)
	    (available p57p1-cdk46p1p2-cycD))
 :effect (and (goal11)))

(:action DUMMY-ACTION-12
 :parameters ()
 :precondition
	(or (available cdk46-cycD)
	    (available cdk46p2-cycDp1))
 :effect (and (goal12)))

(:action DUMMY-ACTION-13
 :parameters ()
 :precondition
	(or (available p57-cdk46p2-cycDp1)
	    (available SP1-E2F13p1-gP))
 :effect (and (goal13)))

(:action DUMMY-ACTION-14
 :parameters ()
 :precondition
	(or (available p57-cdk46-cycD)
	    (available p57p1-cdk46-cycDp1))
 :effect (and (goal14)))

(:action DUMMY-ACTION-15
 :parameters ()
 :precondition
	(or (available Skp2-Skp1p1-cdk2-cycA)
	    (available Skp2-Skp1p1-cdk2p1-cycA))
 :effect (and (goal15)))

(:action DUMMY-ACTION-16
 :parameters ()
 :precondition
	(or (available cdk2-cycEp1)
	    (available Skp2-Skp1p1-cdk2p1p2-cycA))
 :effect (and (goal16)))

(:action DUMMY-ACTION-17
 :parameters ()
 :precondition
	(or (available Raf1-cdc25A)
	    (available p57-cdk46p2-cycD))
 :effect (and (goal17)))

(:action DUMMY-ACTION-18
 :parameters ()
 :precondition
	(or (available Skp2-Skp1p1-cdk2p2-cycA)
	    (available SL1p1))
 :effect (and (goal18)))

(:action DUMMY-ACTION-19
 :parameters ()
 :precondition
	(or (available p57p1-cdk46-cycD)
	    (available cdc25Ap1))
 :effect (and (goal19)))

(:action DUMMY-ACTION-20
 :parameters ()
 :precondition
	(or (available p27-cdk46p2-cycD)
	    (available p27p1-cdk2p1-cycA))
 :effect (and (goal20)))

(:action DUMMY-ACTION-21
 :parameters ()
 :precondition
	(or (available p68p1p2)
	    (available p27p1-cdk2-cycEp1))
 :effect (and (goal21)))

(:action DUMMY-ACTION-22
 :parameters ()
 :precondition
	(or (available p27-cdk46p2-cycDp1)
	    (available SP1-E2F13p1))
 :effect (and (goal22)))

(:action DUMMY-ACTION-23
 :parameters ()
 :precondition
	(or (available p57-cdk2p1-cycA)
	    (available cdk1p3-cycB))
 :effect (and (goal23)))

(:action DUMMY-ACTION-24
 :parameters ()
 :precondition
	(or (available p27p1-cdk46p1-cycD)
	    (available Skp2p1-Skp1p1))
 :effect (and (goal24)))

(:action DUMMY-ACTION-25
 :parameters ()
 :precondition
	(or (available Skp2-cdk2p1p2-cycA)
	    (available CEBP-pRbp1-gP))
 :effect (and (goal25)))

(:action DUMMY-ACTION-26
 :parameters ()
 :precondition
	(or (available p27-cdk46p1p2-cycD)
	    (available cdk2p2-cycA-E2F13))
 :effect (and (goal26)))

(:action DUMMY-ACTION-27
 :parameters ()
 :precondition
	(or (available p27-cdk2p2-cycEp1)
	    (available p27p1-cdk46p1-cycDp1))
 :effect (and (goal27)))

(:action DUMMY-ACTION-28
 :parameters ()
 :precondition
	(or (available p27p1-cdk2-cycA)
	    (available p27-cdk2p1-cycA))
 :effect (and (goal28)))

(:action DUMMY-ACTION-29
 :parameters ()
 :precondition
	(or (available p107)
	    (available cdk1p3-cycA))
 :effect (and (goal29)))

(:action DUMMY-ACTION-30
 :parameters ()
 :precondition
	(or (available DMP1p1-cycD)
	    (available c-Abl-pRbp1p2))
 :effect (and (goal30)))

(:action DUMMY-ACTION-31
 :parameters ()
 :precondition
	(or (available cdk2-cycA-E2F13p1)
	    (available cdk2p1-cycA-E2F13p1))
 :effect (and (goal31)))

(:action DUMMY-ACTION-32
 :parameters ()
 :precondition
	(or (available p27p1-cdk2p2-cycE)
	    (available cdk1))
 :effect (and (goal32)))

(:action DUMMY-ACTION-33
 :parameters ()
 :precondition
	(or (available Skp2-cdk2p1-cycA)
	    (available p27p1-cdk2p1p2-cycA))
 :effect (and (goal33)))

(:action DUMMY-ACTION-34
 :parameters ()
 :precondition
	(or (available p27p1-cdk46p1p2-cycDp1)
	    (available cdc25A))
 :effect (and (goal34)))
)

