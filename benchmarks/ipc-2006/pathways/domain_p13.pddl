; IPC5 Domain: Pathways Propositional
; Authors: Yannis Dimopoulos, Alfonso Gerevini and Alessandro Saetti

(define (domain Pathways-Propositional) 
(:requirements :typing :adl)  

(:types level molecule - object
        simple complex - molecule) 

(:constants cdc25A cdc25Ap1 cdk2-cycA-E2F13 cdk2p1-cycA-E2F13 cdk46 cdk46-cycD cdk46-cycDp1 cdk46p1-cycD cdk46p1-cycDp1 DMP1-cycDp1 DMP1p1-gp19ARF Mdm2-E2F13-DP12p1 p21-cdk2p1-cycA p21-cdk46-cycD p21-cdk46-cycDp1 p27-cdk2p1-cycA p27-cdk46-cycD p27-cdk46-cycDp1 p57-cdk2-cycE p57-cdk2-cycEp1 p57-cdk2p1-cycA p57-cdk46-cycD p57-cdk46-cycDp1 PCNA-Gadd45 PCNA-p21-cdk2p1-cycA PCNA-p21-cdk46-cycD PCNA-p21-cdk46-cycDp1 pRbp1p2-Jun Raf1-cdc25A Raf1-cdc25Ap1 Raf1-p130-E2F5-DP12-gE2 Skp2-cdk2p1-cycA Skp2-Skp1-cdk2-cycA Skp2-Skp1-cdk2p1-cycA  - complex)

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
	     (goal17))


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
	(or (available p27-cdk46-cycD)
	    (available DMP1-cycDp1))
 :effect (and (goal1)))

(:action DUMMY-ACTION-2
 :parameters ()
 :precondition
	(or (available PCNA-p21-cdk46-cycDp1)
	    (available cdk46))
 :effect (and (goal2)))

(:action DUMMY-ACTION-3
 :parameters ()
 :precondition
	(or (available cdk46-cycD)
	    (available p21-cdk46-cycD))
 :effect (and (goal3)))

(:action DUMMY-ACTION-4
 :parameters ()
 :precondition
	(or (available p57-cdk46-cycD)
	    (available cdk46-cycDp1))
 :effect (and (goal4)))

(:action DUMMY-ACTION-5
 :parameters ()
 :precondition
	(or (available p57-cdk46-cycDp1)
	    (available PCNA-p21-cdk46-cycD))
 :effect (and (goal5)))

(:action DUMMY-ACTION-6
 :parameters ()
 :precondition
	(or (available p27-cdk46-cycDp1)
	    (available cdc25Ap1))
 :effect (and (goal6)))

(:action DUMMY-ACTION-7
 :parameters ()
 :precondition
	(or (available p21-cdk46-cycDp1)
	    (available Raf1-cdc25Ap1))
 :effect (and (goal7)))

(:action DUMMY-ACTION-8
 :parameters ()
 :precondition
	(or (available Raf1-cdc25A)
	    (available Skp2-cdk2p1-cycA))
 :effect (and (goal8)))

(:action DUMMY-ACTION-9
 :parameters ()
 :precondition
	(or (available p57-cdk2-cycE)
	    (available Skp2-Skp1-cdk2p1-cycA))
 :effect (and (goal9)))

(:action DUMMY-ACTION-10
 :parameters ()
 :precondition
	(or (available cdk2p1-cycA-E2F13)
	    (available Raf1-p130-E2F5-DP12-gE2))
 :effect (and (goal10)))

(:action DUMMY-ACTION-11
 :parameters ()
 :precondition
	(or (available cdk46p1-cycDp1)
	    (available PCNA-p21-cdk2p1-cycA))
 :effect (and (goal11)))

(:action DUMMY-ACTION-12
 :parameters ()
 :precondition
	(or (available p21-cdk2p1-cycA)
	    (available p57-cdk2-cycEp1))
 :effect (and (goal12)))

(:action DUMMY-ACTION-13
 :parameters ()
 :precondition
	(or (available p57-cdk2p1-cycA)
	    (available cdc25A))
 :effect (and (goal13)))

(:action DUMMY-ACTION-14
 :parameters ()
 :precondition
	(or (available PCNA-Gadd45)
	    (available Mdm2-E2F13-DP12p1))
 :effect (and (goal14)))

(:action DUMMY-ACTION-15
 :parameters ()
 :precondition
	(or (available cdk2-cycA-E2F13)
	    (available pRbp1p2-Jun))
 :effect (and (goal15)))

(:action DUMMY-ACTION-16
 :parameters ()
 :precondition
	(or (available cdk46p1-cycD)
	    (available p27-cdk2p1-cycA))
 :effect (and (goal16)))

(:action DUMMY-ACTION-17
 :parameters ()
 :precondition
	(or (available Skp2-Skp1-cdk2-cycA)
	    (available DMP1p1-gp19ARF))
 :effect (and (goal17)))
)

