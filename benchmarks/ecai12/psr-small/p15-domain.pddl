(define (domain grounded-STRIPS-PSR)
(:requirements
:strips
)
(:predicates
(NOT-CLOSED-CB1)
(UPDATED-CB1)
(NOT-CLOSED-CB2)
(CLOSED-SD5)
(CLOSED-SD6)
(NOT-CLOSED-SD1)
(NOT-CLOSED-SD2)
(NOT-CLOSED-SD3)
(NOT-CLOSED-SD4)
(NOT-CLOSED-SD7)
(NOT-CLOSED-SD8)
(NOT-CLOSED-SD9)
(NOT-CLOSED-SD10)
(NOT-UPDATED-CB2)
(CLOSED-CB1)
(CLOSED-CB2)
(UPDATED-CB2)
(CLOSED-SD10)
(CLOSED-SD9)
(CLOSED-SD8)
(CLOSED-SD7)
(CLOSED-SD4)
(CLOSED-SD3)
(CLOSED-SD2)
(CLOSED-SD1)
(NOT-CLOSED-SD6)
(NOT-CLOSED-SD5)
(NOT-UPDATED-CB1)
(GOAL-REACHED)
(do-CLOSE_SD10-condeffs)
(do-CLOSE_SD9-condeffs)
(do-CLOSE_SD8-condeffs)
(do-CLOSE_SD7-condeffs)
(do-CLOSE_SD4-condeffs)
(do-CLOSE_SD3-condeffs)
(do-CLOSE_SD2-condeffs)
(do-CLOSE_SD1-condeffs)
(do-WAIT_CB2-condeffs)
(do-CLOSE_SD6-condeffs)
(do-CLOSE_SD5-condeffs)
(do-WAIT_CB1-condeffs)
(do-normal)
(done-0)
(done-1)
)
(:action REACH-GOAL-0
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD6)
(CLOSED-SD9)
(CLOSED-SD8)
(CLOSED-SD7)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-1
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-2
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-3
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-4
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-5
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-6
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-7
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-8
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-9
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-10
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-11
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-12
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-13
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-14
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-15
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-CB1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-16
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-CB2)
(CLOSED-SD6)
(CLOSED-SD9)
(CLOSED-SD8)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-17
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-18
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-19
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-20
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-21
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-22
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-23
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-24
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-25
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-26
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-27
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-28
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-29
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-30
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-31
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-CB1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-32
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD6)
(CLOSED-SD9)
(CLOSED-SD8)
(CLOSED-SD7)
(CLOSED-CB2)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-33
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-34
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-35
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-36
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-37
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-38
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-39
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-40
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-41
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-42
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-43
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-44
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-45
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-46
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-47
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-CB1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-48
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD6)
(CLOSED-SD9)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-49
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-50
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-51
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-52
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-53
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-54
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-55
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-56
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-57
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-58
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-59
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-60
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-61
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-62
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-63
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-CB1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-64
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD6)
(CLOSED-SD9)
(CLOSED-SD8)
(CLOSED-SD7)
(CLOSED-CB2)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-65
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-66
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-67
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-68
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-69
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-70
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-71
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-72
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-73
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-74
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-75
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-76
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-77
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-78
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-79
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-CB1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-80
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-CB2)
(CLOSED-SD6)
(CLOSED-SD9)
(CLOSED-SD8)
(CLOSED-SD7)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-81
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-82
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-83
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-84
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-85
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-86
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-87
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-88
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-89
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-90
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-91
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-92
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-93
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-94
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-95
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-CB1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-96
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD6)
(CLOSED-SD9)
(CLOSED-SD8)
(CLOSED-SD7)
(CLOSED-CB2)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-97
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-98
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-99
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-100
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-101
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-102
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-103
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-104
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-105
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-106
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-107
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-108
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-109
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-110
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-111
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-CB1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-112
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD6)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-113
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-114
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-115
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-116
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-117
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-118
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-119
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-120
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-121
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-122
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-123
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-124
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-125
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-126
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-127
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-CB1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-128
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD6)
(CLOSED-SD9)
(CLOSED-SD8)
(CLOSED-SD7)
(CLOSED-CB2)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-129
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-130
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-131
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-132
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-133
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-134
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-135
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-136
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-137
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-138
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-139
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-140
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-141
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-142
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-143
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-CB1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-144
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-CB2)
(CLOSED-SD6)
(CLOSED-SD9)
(CLOSED-SD8)
(CLOSED-SD7)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-145
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-146
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-147
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-148
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-149
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-150
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-151
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-152
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-153
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-154
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-155
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-156
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-157
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-158
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-159
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-CB1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-160
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD6)
(CLOSED-SD9)
(CLOSED-SD8)
(CLOSED-SD7)
(CLOSED-CB2)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-161
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-162
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-163
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-164
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-165
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-166
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-167
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-168
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-169
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-170
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-171
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-172
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-173
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-174
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-175
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-CB1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-176
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD6)
(CLOSED-SD9)
(CLOSED-SD8)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-177
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-178
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-179
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-180
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-181
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-182
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-183
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-184
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-185
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-186
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-187
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-188
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-189
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-190
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-191
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-CB1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-192
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD6)
(CLOSED-SD9)
(CLOSED-SD8)
(CLOSED-SD7)
(CLOSED-CB2)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-193
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-194
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-195
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-196
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-197
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-198
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-199
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-200
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-201
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-202
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-203
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-204
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-205
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-206
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-207
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-CB1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-208
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-CB2)
(CLOSED-SD6)
(CLOSED-SD9)
(CLOSED-SD8)
(CLOSED-SD7)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-209
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-210
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-211
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-212
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-213
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-214
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-215
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-216
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-217
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-218
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-219
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-220
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-221
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-222
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-223
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-CB1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-224
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD6)
(CLOSED-SD9)
(CLOSED-SD8)
(CLOSED-SD7)
(CLOSED-CB2)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-225
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-226
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-227
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-228
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-229
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-230
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-231
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-232
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-233
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-234
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-235
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-236
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-237
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-238
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-239
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-CB1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-240
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-241
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-242
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-243
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-244
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-245
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-246
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-247
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-248
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-249
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-250
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-251
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-252
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-253
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-254
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-255
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-CB1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-256
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD6)
(CLOSED-SD9)
(CLOSED-SD8)
(CLOSED-SD7)
(CLOSED-CB2)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-257
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-258
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-259
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-260
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-261
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-262
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-263
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-264
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-265
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-266
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-267
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-268
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-269
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-270
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-271
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-CB1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-272
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-CB2)
(CLOSED-SD6)
(CLOSED-SD9)
(CLOSED-SD8)
(CLOSED-SD7)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-273
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-274
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-275
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-276
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-277
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-278
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-279
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-280
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-281
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-282
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-283
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-284
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-285
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-286
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-287
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-CB1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-288
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD6)
(CLOSED-SD9)
(CLOSED-SD8)
(CLOSED-SD7)
(CLOSED-CB2)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-289
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-290
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-291
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-292
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-293
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-294
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-295
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-296
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-297
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-298
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-299
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-300
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-301
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-302
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-303
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-CB1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-304
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD6)
(CLOSED-SD9)
(CLOSED-SD8)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-305
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-306
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-307
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-308
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-309
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-310
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-311
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-312
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-313
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-314
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-315
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-316
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-317
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-318
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-319
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-CB1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-320
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD6)
(CLOSED-SD9)
(CLOSED-SD8)
(CLOSED-SD7)
(CLOSED-CB2)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-321
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-322
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-323
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-324
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-325
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-326
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-327
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-328
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-329
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-330
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-331
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-332
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-333
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-334
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-335
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-CB1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-336
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-CB2)
(CLOSED-SD6)
(CLOSED-SD9)
(CLOSED-SD8)
(CLOSED-SD7)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-337
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-338
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-339
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-340
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-341
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-342
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-343
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-344
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-345
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-346
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-347
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-348
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-349
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-350
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-351
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-CB1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-352
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD6)
(CLOSED-SD9)
(CLOSED-SD8)
(CLOSED-SD7)
(CLOSED-CB2)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-353
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-354
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-355
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-356
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-357
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-358
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-359
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-360
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-361
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-362
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-363
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-364
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-365
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-366
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-367
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-CB1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-368
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD6)
(CLOSED-SD9)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-369
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-370
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-371
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-372
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-373
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-374
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-375
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-376
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-377
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-378
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-379
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-380
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-381
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-382
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-383
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-CB1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-384
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD6)
(CLOSED-SD9)
(CLOSED-SD8)
(CLOSED-SD7)
(CLOSED-CB2)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-385
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-386
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-387
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-388
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-389
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-390
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-391
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-392
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-393
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-394
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-395
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-396
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-397
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-398
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-399
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-CB1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-400
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-CB2)
(CLOSED-SD6)
(CLOSED-SD9)
(CLOSED-SD8)
(CLOSED-SD7)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-401
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-402
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-403
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-404
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-405
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-406
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-407
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-408
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-409
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-410
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-411
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-412
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-413
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-414
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-415
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-CB1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-416
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD6)
(CLOSED-SD9)
(CLOSED-SD8)
(CLOSED-SD7)
(CLOSED-CB2)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-417
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-418
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-419
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-420
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-421
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-422
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-423
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-424
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-425
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-426
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-427
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-428
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-429
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-430
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-431
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-CB1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-432
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD6)
(CLOSED-SD9)
(CLOSED-SD8)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-433
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-434
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-435
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-436
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-437
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-438
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-439
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-440
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-441
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-442
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-443
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-444
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-445
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-446
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-447
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-CB1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-448
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD6)
(CLOSED-SD9)
(CLOSED-SD8)
(CLOSED-SD7)
(CLOSED-CB2)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-449
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-450
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-451
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-452
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-453
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-454
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-455
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-456
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-457
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-458
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-459
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-460
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-461
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-462
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-463
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-CB1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-464
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-CB2)
(CLOSED-SD6)
(CLOSED-SD9)
(CLOSED-SD8)
(CLOSED-SD7)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-465
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-466
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-467
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-468
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-469
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-470
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-471
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-472
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-473
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-474
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-475
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-476
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-477
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-478
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-479
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-CB1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-480
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD6)
(CLOSED-SD9)
(CLOSED-SD8)
(CLOSED-SD7)
(CLOSED-CB2)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-481
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-482
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-483
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-484
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-485
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-486
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-487
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-488
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-489
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-490
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-491
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-492
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-493
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-494
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-495
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-CB1)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-496
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-497
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-498
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-499
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-500
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-501
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-502
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-503
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB1)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-504
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-505
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-506
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-507
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-508
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-SD1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-509
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-510
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action REACH-GOAL-511
:parameters ()
:precondition
(and
(do-normal)
(UPDATED-CB2)
(UPDATED-CB1)
(CLOSED-CB2)
(CLOSED-SD7)
(CLOSED-SD8)
(CLOSED-SD9)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-SD2)
(CLOSED-SD3)
(CLOSED-SD10)
)
:effect
(and
(GOAL-REACHED)
)
)
(:action CLOSE_SD10
:parameters ()
:precondition
(and
(do-normal)
(NOT-CLOSED-SD10)
(UPDATED-CB1)
(UPDATED-CB2)
)
:effect
(and
(not (do-normal))
(do-CLOSE_SD10-condeffs)
(CLOSED-SD10)
(not (NOT-CLOSED-SD10))
)
)
(:action CLOSE_SD10-condeff0-yes
:parameters ()
:precondition
(and
(do-CLOSE_SD10-condeffs)
(CLOSED-SD5)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
)
:effect
(and
(done-0)
(NOT-CLOSED-CB1)
(not (CLOSED-CB1))
)
)
(:action CLOSE_SD10-condeff0-no-0
:parameters ()
:precondition
(and
(do-CLOSE_SD10-condeffs)
(NOT-CLOSED-SD5)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD10-condeff0-no-1
:parameters ()
:precondition
(and
(do-CLOSE_SD10-condeffs)
(NOT-CLOSED-SD6)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD10-condeff0-no-2
:parameters ()
:precondition
(and
(do-CLOSE_SD10-condeffs)
(NOT-CLOSED-SD1)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD10-condeff0-no-3
:parameters ()
:precondition
(and
(do-CLOSE_SD10-condeffs)
(NOT-CLOSED-CB1)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD10-condeff1-yes
:parameters ()
:precondition
(and
(do-CLOSE_SD10-condeffs)
(CLOSED-SD5)
(CLOSED-SD9)
(CLOSED-SD8)
(CLOSED-SD7)
(CLOSED-CB2)
)
:effect
(and
(done-1)
(NOT-CLOSED-CB2)
(not (CLOSED-CB2))
)
)
(:action CLOSE_SD10-condeff1-no-0
:parameters ()
:precondition
(and
(do-CLOSE_SD10-condeffs)
(NOT-CLOSED-SD5)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD10-condeff1-no-1
:parameters ()
:precondition
(and
(do-CLOSE_SD10-condeffs)
(NOT-CLOSED-SD9)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD10-condeff1-no-2
:parameters ()
:precondition
(and
(do-CLOSE_SD10-condeffs)
(NOT-CLOSED-SD8)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD10-condeff1-no-3
:parameters ()
:precondition
(and
(do-CLOSE_SD10-condeffs)
(NOT-CLOSED-SD7)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD10-condeff1-no-4
:parameters ()
:precondition
(and
(do-CLOSE_SD10-condeffs)
(NOT-CLOSED-CB2)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD10-endof-condeffs
:parameters ()
:precondition
(and
(do-CLOSE_SD10-condeffs)
(done-0)
(done-1)
)
:effect
(and
(do-normal)
(not (do-CLOSE_SD10-condeffs))
(not (done-0))
(not (done-1))
)
)
(:action CLOSE_SD9
:parameters ()
:precondition
(and
(do-normal)
(NOT-CLOSED-SD9)
(UPDATED-CB1)
(UPDATED-CB2)
)
:effect
(and
(not (do-normal))
(do-CLOSE_SD9-condeffs)
(CLOSED-SD9)
(not (NOT-CLOSED-SD9))
)
)
(:action CLOSE_SD9-condeff0-yes
:parameters ()
:precondition
(and
(do-CLOSE_SD9-condeffs)
(CLOSED-SD4)
(CLOSED-SD3)
(CLOSED-SD2)
(CLOSED-SD6)
(CLOSED-SD8)
(CLOSED-SD7)
(CLOSED-CB2)
)
:effect
(and
(done-0)
(NOT-CLOSED-CB2)
(not (CLOSED-CB2))
)
)
(:action CLOSE_SD9-condeff0-no-0
:parameters ()
:precondition
(and
(do-CLOSE_SD9-condeffs)
(NOT-CLOSED-SD4)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD9-condeff0-no-1
:parameters ()
:precondition
(and
(do-CLOSE_SD9-condeffs)
(NOT-CLOSED-SD3)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD9-condeff0-no-2
:parameters ()
:precondition
(and
(do-CLOSE_SD9-condeffs)
(NOT-CLOSED-SD2)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD9-condeff0-no-3
:parameters ()
:precondition
(and
(do-CLOSE_SD9-condeffs)
(NOT-CLOSED-SD6)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD9-condeff0-no-4
:parameters ()
:precondition
(and
(do-CLOSE_SD9-condeffs)
(NOT-CLOSED-SD8)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD9-condeff0-no-5
:parameters ()
:precondition
(and
(do-CLOSE_SD9-condeffs)
(NOT-CLOSED-SD7)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD9-condeff0-no-6
:parameters ()
:precondition
(and
(do-CLOSE_SD9-condeffs)
(NOT-CLOSED-CB2)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD9-condeff1-yes
:parameters ()
:precondition
(and
(do-CLOSE_SD9-condeffs)
(CLOSED-SD5)
(CLOSED-SD10)
(CLOSED-SD8)
(CLOSED-SD7)
(CLOSED-CB2)
)
:effect
(and
(done-1)
(NOT-CLOSED-CB2)
(not (CLOSED-CB2))
)
)
(:action CLOSE_SD9-condeff1-no-0
:parameters ()
:precondition
(and
(do-CLOSE_SD9-condeffs)
(NOT-CLOSED-SD5)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD9-condeff1-no-1
:parameters ()
:precondition
(and
(do-CLOSE_SD9-condeffs)
(NOT-CLOSED-SD10)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD9-condeff1-no-2
:parameters ()
:precondition
(and
(do-CLOSE_SD9-condeffs)
(NOT-CLOSED-SD8)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD9-condeff1-no-3
:parameters ()
:precondition
(and
(do-CLOSE_SD9-condeffs)
(NOT-CLOSED-SD7)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD9-condeff1-no-4
:parameters ()
:precondition
(and
(do-CLOSE_SD9-condeffs)
(NOT-CLOSED-CB2)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD9-endof-condeffs
:parameters ()
:precondition
(and
(do-CLOSE_SD9-condeffs)
(done-0)
(done-1)
)
:effect
(and
(do-normal)
(not (do-CLOSE_SD9-condeffs))
(not (done-0))
(not (done-1))
)
)
(:action CLOSE_SD8
:parameters ()
:precondition
(and
(do-normal)
(NOT-CLOSED-SD8)
(UPDATED-CB1)
(UPDATED-CB2)
)
:effect
(and
(not (do-normal))
(do-CLOSE_SD8-condeffs)
(CLOSED-SD8)
(not (NOT-CLOSED-SD8))
)
)
(:action CLOSE_SD8-condeff0-yes
:parameters ()
:precondition
(and
(do-CLOSE_SD8-condeffs)
(CLOSED-SD4)
(CLOSED-SD3)
(CLOSED-SD2)
(CLOSED-SD6)
(CLOSED-SD9)
(CLOSED-SD7)
(CLOSED-CB2)
)
:effect
(and
(done-0)
(NOT-CLOSED-CB2)
(not (CLOSED-CB2))
)
)
(:action CLOSE_SD8-condeff0-no-0
:parameters ()
:precondition
(and
(do-CLOSE_SD8-condeffs)
(NOT-CLOSED-SD4)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD8-condeff0-no-1
:parameters ()
:precondition
(and
(do-CLOSE_SD8-condeffs)
(NOT-CLOSED-SD3)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD8-condeff0-no-2
:parameters ()
:precondition
(and
(do-CLOSE_SD8-condeffs)
(NOT-CLOSED-SD2)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD8-condeff0-no-3
:parameters ()
:precondition
(and
(do-CLOSE_SD8-condeffs)
(NOT-CLOSED-SD6)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD8-condeff0-no-4
:parameters ()
:precondition
(and
(do-CLOSE_SD8-condeffs)
(NOT-CLOSED-SD9)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD8-condeff0-no-5
:parameters ()
:precondition
(and
(do-CLOSE_SD8-condeffs)
(NOT-CLOSED-SD7)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD8-condeff0-no-6
:parameters ()
:precondition
(and
(do-CLOSE_SD8-condeffs)
(NOT-CLOSED-CB2)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD8-condeff1-yes
:parameters ()
:precondition
(and
(do-CLOSE_SD8-condeffs)
(CLOSED-SD5)
(CLOSED-SD10)
(CLOSED-SD9)
(CLOSED-SD7)
(CLOSED-CB2)
)
:effect
(and
(done-1)
(NOT-CLOSED-CB2)
(not (CLOSED-CB2))
)
)
(:action CLOSE_SD8-condeff1-no-0
:parameters ()
:precondition
(and
(do-CLOSE_SD8-condeffs)
(NOT-CLOSED-SD5)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD8-condeff1-no-1
:parameters ()
:precondition
(and
(do-CLOSE_SD8-condeffs)
(NOT-CLOSED-SD10)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD8-condeff1-no-2
:parameters ()
:precondition
(and
(do-CLOSE_SD8-condeffs)
(NOT-CLOSED-SD9)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD8-condeff1-no-3
:parameters ()
:precondition
(and
(do-CLOSE_SD8-condeffs)
(NOT-CLOSED-SD7)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD8-condeff1-no-4
:parameters ()
:precondition
(and
(do-CLOSE_SD8-condeffs)
(NOT-CLOSED-CB2)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD8-endof-condeffs
:parameters ()
:precondition
(and
(do-CLOSE_SD8-condeffs)
(done-0)
(done-1)
)
:effect
(and
(do-normal)
(not (do-CLOSE_SD8-condeffs))
(not (done-0))
(not (done-1))
)
)
(:action CLOSE_SD7
:parameters ()
:precondition
(and
(do-normal)
(NOT-CLOSED-SD7)
(UPDATED-CB1)
(UPDATED-CB2)
)
:effect
(and
(not (do-normal))
(do-CLOSE_SD7-condeffs)
(CLOSED-SD7)
(not (NOT-CLOSED-SD7))
)
)
(:action CLOSE_SD7-condeff0-yes
:parameters ()
:precondition
(and
(do-CLOSE_SD7-condeffs)
(CLOSED-SD4)
(CLOSED-SD3)
(CLOSED-SD2)
(CLOSED-SD6)
(CLOSED-SD9)
(CLOSED-SD8)
(CLOSED-CB2)
)
:effect
(and
(done-0)
(NOT-CLOSED-CB2)
(not (CLOSED-CB2))
)
)
(:action CLOSE_SD7-condeff0-no-0
:parameters ()
:precondition
(and
(do-CLOSE_SD7-condeffs)
(NOT-CLOSED-SD4)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD7-condeff0-no-1
:parameters ()
:precondition
(and
(do-CLOSE_SD7-condeffs)
(NOT-CLOSED-SD3)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD7-condeff0-no-2
:parameters ()
:precondition
(and
(do-CLOSE_SD7-condeffs)
(NOT-CLOSED-SD2)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD7-condeff0-no-3
:parameters ()
:precondition
(and
(do-CLOSE_SD7-condeffs)
(NOT-CLOSED-SD6)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD7-condeff0-no-4
:parameters ()
:precondition
(and
(do-CLOSE_SD7-condeffs)
(NOT-CLOSED-SD9)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD7-condeff0-no-5
:parameters ()
:precondition
(and
(do-CLOSE_SD7-condeffs)
(NOT-CLOSED-SD8)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD7-condeff0-no-6
:parameters ()
:precondition
(and
(do-CLOSE_SD7-condeffs)
(NOT-CLOSED-CB2)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD7-condeff1-yes
:parameters ()
:precondition
(and
(do-CLOSE_SD7-condeffs)
(CLOSED-SD5)
(CLOSED-SD10)
(CLOSED-SD9)
(CLOSED-SD8)
(CLOSED-CB2)
)
:effect
(and
(done-1)
(NOT-CLOSED-CB2)
(not (CLOSED-CB2))
)
)
(:action CLOSE_SD7-condeff1-no-0
:parameters ()
:precondition
(and
(do-CLOSE_SD7-condeffs)
(NOT-CLOSED-SD5)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD7-condeff1-no-1
:parameters ()
:precondition
(and
(do-CLOSE_SD7-condeffs)
(NOT-CLOSED-SD10)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD7-condeff1-no-2
:parameters ()
:precondition
(and
(do-CLOSE_SD7-condeffs)
(NOT-CLOSED-SD9)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD7-condeff1-no-3
:parameters ()
:precondition
(and
(do-CLOSE_SD7-condeffs)
(NOT-CLOSED-SD8)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD7-condeff1-no-4
:parameters ()
:precondition
(and
(do-CLOSE_SD7-condeffs)
(NOT-CLOSED-CB2)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD7-endof-condeffs
:parameters ()
:precondition
(and
(do-CLOSE_SD7-condeffs)
(done-0)
(done-1)
)
:effect
(and
(do-normal)
(not (do-CLOSE_SD7-condeffs))
(not (done-0))
(not (done-1))
)
)
(:action CLOSE_SD4
:parameters ()
:precondition
(and
(do-normal)
(NOT-CLOSED-SD4)
(UPDATED-CB1)
(UPDATED-CB2)
)
:effect
(and
(not (do-normal))
(do-CLOSE_SD4-condeffs)
(CLOSED-SD4)
(not (NOT-CLOSED-SD4))
)
)
(:action CLOSE_SD4-condeff0-yes
:parameters ()
:precondition
(and
(do-CLOSE_SD4-condeffs)
(CLOSED-SD3)
(CLOSED-SD2)
(CLOSED-SD1)
(CLOSED-CB1)
)
:effect
(and
(done-0)
(NOT-CLOSED-CB1)
(not (CLOSED-CB1))
)
)
(:action CLOSE_SD4-condeff0-no-0
:parameters ()
:precondition
(and
(do-CLOSE_SD4-condeffs)
(NOT-CLOSED-SD3)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD4-condeff0-no-1
:parameters ()
:precondition
(and
(do-CLOSE_SD4-condeffs)
(NOT-CLOSED-SD2)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD4-condeff0-no-2
:parameters ()
:precondition
(and
(do-CLOSE_SD4-condeffs)
(NOT-CLOSED-SD1)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD4-condeff0-no-3
:parameters ()
:precondition
(and
(do-CLOSE_SD4-condeffs)
(NOT-CLOSED-CB1)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD4-condeff1-yes
:parameters ()
:precondition
(and
(do-CLOSE_SD4-condeffs)
(CLOSED-SD3)
(CLOSED-SD2)
(CLOSED-SD6)
(CLOSED-SD9)
(CLOSED-SD8)
(CLOSED-SD7)
(CLOSED-CB2)
)
:effect
(and
(done-1)
(NOT-CLOSED-CB2)
(not (CLOSED-CB2))
)
)
(:action CLOSE_SD4-condeff1-no-0
:parameters ()
:precondition
(and
(do-CLOSE_SD4-condeffs)
(NOT-CLOSED-SD3)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD4-condeff1-no-1
:parameters ()
:precondition
(and
(do-CLOSE_SD4-condeffs)
(NOT-CLOSED-SD2)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD4-condeff1-no-2
:parameters ()
:precondition
(and
(do-CLOSE_SD4-condeffs)
(NOT-CLOSED-SD6)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD4-condeff1-no-3
:parameters ()
:precondition
(and
(do-CLOSE_SD4-condeffs)
(NOT-CLOSED-SD9)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD4-condeff1-no-4
:parameters ()
:precondition
(and
(do-CLOSE_SD4-condeffs)
(NOT-CLOSED-SD8)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD4-condeff1-no-5
:parameters ()
:precondition
(and
(do-CLOSE_SD4-condeffs)
(NOT-CLOSED-SD7)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD4-condeff1-no-6
:parameters ()
:precondition
(and
(do-CLOSE_SD4-condeffs)
(NOT-CLOSED-CB2)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD4-endof-condeffs
:parameters ()
:precondition
(and
(do-CLOSE_SD4-condeffs)
(done-0)
(done-1)
)
:effect
(and
(do-normal)
(not (do-CLOSE_SD4-condeffs))
(not (done-0))
(not (done-1))
)
)
(:action CLOSE_SD3
:parameters ()
:precondition
(and
(do-normal)
(NOT-CLOSED-SD3)
(UPDATED-CB1)
(UPDATED-CB2)
)
:effect
(and
(not (do-normal))
(do-CLOSE_SD3-condeffs)
(CLOSED-SD3)
(not (NOT-CLOSED-SD3))
)
)
(:action CLOSE_SD3-condeff0-yes
:parameters ()
:precondition
(and
(do-CLOSE_SD3-condeffs)
(CLOSED-SD4)
(CLOSED-SD2)
(CLOSED-SD1)
(CLOSED-CB1)
)
:effect
(and
(done-0)
(NOT-CLOSED-CB1)
(not (CLOSED-CB1))
)
)
(:action CLOSE_SD3-condeff0-no-0
:parameters ()
:precondition
(and
(do-CLOSE_SD3-condeffs)
(NOT-CLOSED-SD4)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD3-condeff0-no-1
:parameters ()
:precondition
(and
(do-CLOSE_SD3-condeffs)
(NOT-CLOSED-SD2)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD3-condeff0-no-2
:parameters ()
:precondition
(and
(do-CLOSE_SD3-condeffs)
(NOT-CLOSED-SD1)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD3-condeff0-no-3
:parameters ()
:precondition
(and
(do-CLOSE_SD3-condeffs)
(NOT-CLOSED-CB1)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD3-condeff1-yes
:parameters ()
:precondition
(and
(do-CLOSE_SD3-condeffs)
(CLOSED-SD4)
(CLOSED-SD2)
(CLOSED-SD6)
(CLOSED-SD9)
(CLOSED-SD8)
(CLOSED-SD7)
(CLOSED-CB2)
)
:effect
(and
(done-1)
(NOT-CLOSED-CB2)
(not (CLOSED-CB2))
)
)
(:action CLOSE_SD3-condeff1-no-0
:parameters ()
:precondition
(and
(do-CLOSE_SD3-condeffs)
(NOT-CLOSED-SD4)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD3-condeff1-no-1
:parameters ()
:precondition
(and
(do-CLOSE_SD3-condeffs)
(NOT-CLOSED-SD2)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD3-condeff1-no-2
:parameters ()
:precondition
(and
(do-CLOSE_SD3-condeffs)
(NOT-CLOSED-SD6)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD3-condeff1-no-3
:parameters ()
:precondition
(and
(do-CLOSE_SD3-condeffs)
(NOT-CLOSED-SD9)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD3-condeff1-no-4
:parameters ()
:precondition
(and
(do-CLOSE_SD3-condeffs)
(NOT-CLOSED-SD8)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD3-condeff1-no-5
:parameters ()
:precondition
(and
(do-CLOSE_SD3-condeffs)
(NOT-CLOSED-SD7)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD3-condeff1-no-6
:parameters ()
:precondition
(and
(do-CLOSE_SD3-condeffs)
(NOT-CLOSED-CB2)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD3-endof-condeffs
:parameters ()
:precondition
(and
(do-CLOSE_SD3-condeffs)
(done-0)
(done-1)
)
:effect
(and
(do-normal)
(not (do-CLOSE_SD3-condeffs))
(not (done-0))
(not (done-1))
)
)
(:action CLOSE_SD2
:parameters ()
:precondition
(and
(do-normal)
(NOT-CLOSED-SD2)
(UPDATED-CB1)
(UPDATED-CB2)
)
:effect
(and
(not (do-normal))
(do-CLOSE_SD2-condeffs)
(CLOSED-SD2)
(not (NOT-CLOSED-SD2))
)
)
(:action CLOSE_SD2-condeff0-yes
:parameters ()
:precondition
(and
(do-CLOSE_SD2-condeffs)
(CLOSED-SD4)
(CLOSED-SD3)
(CLOSED-SD1)
(CLOSED-CB1)
)
:effect
(and
(done-0)
(NOT-CLOSED-CB1)
(not (CLOSED-CB1))
)
)
(:action CLOSE_SD2-condeff0-no-0
:parameters ()
:precondition
(and
(do-CLOSE_SD2-condeffs)
(NOT-CLOSED-SD4)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD2-condeff0-no-1
:parameters ()
:precondition
(and
(do-CLOSE_SD2-condeffs)
(NOT-CLOSED-SD3)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD2-condeff0-no-2
:parameters ()
:precondition
(and
(do-CLOSE_SD2-condeffs)
(NOT-CLOSED-SD1)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD2-condeff0-no-3
:parameters ()
:precondition
(and
(do-CLOSE_SD2-condeffs)
(NOT-CLOSED-CB1)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD2-condeff1-yes
:parameters ()
:precondition
(and
(do-CLOSE_SD2-condeffs)
(CLOSED-SD4)
(CLOSED-SD3)
(CLOSED-SD6)
(CLOSED-SD9)
(CLOSED-SD8)
(CLOSED-SD7)
(CLOSED-CB2)
)
:effect
(and
(done-1)
(NOT-CLOSED-CB2)
(not (CLOSED-CB2))
)
)
(:action CLOSE_SD2-condeff1-no-0
:parameters ()
:precondition
(and
(do-CLOSE_SD2-condeffs)
(NOT-CLOSED-SD4)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD2-condeff1-no-1
:parameters ()
:precondition
(and
(do-CLOSE_SD2-condeffs)
(NOT-CLOSED-SD3)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD2-condeff1-no-2
:parameters ()
:precondition
(and
(do-CLOSE_SD2-condeffs)
(NOT-CLOSED-SD6)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD2-condeff1-no-3
:parameters ()
:precondition
(and
(do-CLOSE_SD2-condeffs)
(NOT-CLOSED-SD9)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD2-condeff1-no-4
:parameters ()
:precondition
(and
(do-CLOSE_SD2-condeffs)
(NOT-CLOSED-SD8)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD2-condeff1-no-5
:parameters ()
:precondition
(and
(do-CLOSE_SD2-condeffs)
(NOT-CLOSED-SD7)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD2-condeff1-no-6
:parameters ()
:precondition
(and
(do-CLOSE_SD2-condeffs)
(NOT-CLOSED-CB2)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD2-endof-condeffs
:parameters ()
:precondition
(and
(do-CLOSE_SD2-condeffs)
(done-0)
(done-1)
)
:effect
(and
(do-normal)
(not (do-CLOSE_SD2-condeffs))
(not (done-0))
(not (done-1))
)
)
(:action CLOSE_SD1
:parameters ()
:precondition
(and
(do-normal)
(NOT-CLOSED-SD1)
(UPDATED-CB1)
(UPDATED-CB2)
)
:effect
(and
(not (do-normal))
(do-CLOSE_SD1-condeffs)
(CLOSED-SD1)
(not (NOT-CLOSED-SD1))
)
)
(:action CLOSE_SD1-condeff0-yes
:parameters ()
:precondition
(and
(do-CLOSE_SD1-condeffs)
(CLOSED-SD4)
(CLOSED-SD3)
(CLOSED-SD2)
(CLOSED-CB1)
)
:effect
(and
(done-0)
(NOT-CLOSED-CB1)
(not (CLOSED-CB1))
)
)
(:action CLOSE_SD1-condeff0-no-0
:parameters ()
:precondition
(and
(do-CLOSE_SD1-condeffs)
(NOT-CLOSED-SD4)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD1-condeff0-no-1
:parameters ()
:precondition
(and
(do-CLOSE_SD1-condeffs)
(NOT-CLOSED-SD3)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD1-condeff0-no-2
:parameters ()
:precondition
(and
(do-CLOSE_SD1-condeffs)
(NOT-CLOSED-SD2)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD1-condeff0-no-3
:parameters ()
:precondition
(and
(do-CLOSE_SD1-condeffs)
(NOT-CLOSED-CB1)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD1-condeff1-yes
:parameters ()
:precondition
(and
(do-CLOSE_SD1-condeffs)
(CLOSED-SD5)
(CLOSED-SD10)
(CLOSED-SD6)
(CLOSED-CB1)
)
:effect
(and
(done-1)
(NOT-CLOSED-CB1)
(not (CLOSED-CB1))
)
)
(:action CLOSE_SD1-condeff1-no-0
:parameters ()
:precondition
(and
(do-CLOSE_SD1-condeffs)
(NOT-CLOSED-SD5)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD1-condeff1-no-1
:parameters ()
:precondition
(and
(do-CLOSE_SD1-condeffs)
(NOT-CLOSED-SD10)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD1-condeff1-no-2
:parameters ()
:precondition
(and
(do-CLOSE_SD1-condeffs)
(NOT-CLOSED-SD6)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD1-condeff1-no-3
:parameters ()
:precondition
(and
(do-CLOSE_SD1-condeffs)
(NOT-CLOSED-CB1)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD1-endof-condeffs
:parameters ()
:precondition
(and
(do-CLOSE_SD1-condeffs)
(done-0)
(done-1)
)
:effect
(and
(do-normal)
(not (do-CLOSE_SD1-condeffs))
(not (done-0))
(not (done-1))
)
)
(:action WAIT_CB2
:parameters ()
:precondition
(and
(do-normal)
(NOT-UPDATED-CB2)
)
:effect
(and
(not (do-normal))
(do-WAIT_CB2-condeffs)
(UPDATED-CB2)
(not (NOT-UPDATED-CB2))
)
)
(:action WAIT_CB2-condeff0-yes
:parameters ()
:precondition
(and
(do-WAIT_CB2-condeffs)
(CLOSED-SD4)
(CLOSED-SD3)
(CLOSED-SD2)
(CLOSED-SD6)
(CLOSED-SD9)
(CLOSED-SD8)
(CLOSED-SD7)
)
:effect
(and
(done-0)
(NOT-CLOSED-CB2)
(not (CLOSED-CB2))
)
)
(:action WAIT_CB2-condeff0-no-0
:parameters ()
:precondition
(and
(do-WAIT_CB2-condeffs)
(NOT-CLOSED-SD4)
)
:effect
(and
(done-0)
)
)
(:action WAIT_CB2-condeff0-no-1
:parameters ()
:precondition
(and
(do-WAIT_CB2-condeffs)
(NOT-CLOSED-SD3)
)
:effect
(and
(done-0)
)
)
(:action WAIT_CB2-condeff0-no-2
:parameters ()
:precondition
(and
(do-WAIT_CB2-condeffs)
(NOT-CLOSED-SD2)
)
:effect
(and
(done-0)
)
)
(:action WAIT_CB2-condeff0-no-3
:parameters ()
:precondition
(and
(do-WAIT_CB2-condeffs)
(NOT-CLOSED-SD6)
)
:effect
(and
(done-0)
)
)
(:action WAIT_CB2-condeff0-no-4
:parameters ()
:precondition
(and
(do-WAIT_CB2-condeffs)
(NOT-CLOSED-SD9)
)
:effect
(and
(done-0)
)
)
(:action WAIT_CB2-condeff0-no-5
:parameters ()
:precondition
(and
(do-WAIT_CB2-condeffs)
(NOT-CLOSED-SD8)
)
:effect
(and
(done-0)
)
)
(:action WAIT_CB2-condeff0-no-6
:parameters ()
:precondition
(and
(do-WAIT_CB2-condeffs)
(NOT-CLOSED-SD7)
)
:effect
(and
(done-0)
)
)
(:action WAIT_CB2-condeff1-yes
:parameters ()
:precondition
(and
(do-WAIT_CB2-condeffs)
(CLOSED-SD5)
(CLOSED-SD10)
(CLOSED-SD9)
(CLOSED-SD8)
(CLOSED-SD7)
)
:effect
(and
(done-1)
(NOT-CLOSED-CB2)
(not (CLOSED-CB2))
)
)
(:action WAIT_CB2-condeff1-no-0
:parameters ()
:precondition
(and
(do-WAIT_CB2-condeffs)
(NOT-CLOSED-SD5)
)
:effect
(and
(done-1)
)
)
(:action WAIT_CB2-condeff1-no-1
:parameters ()
:precondition
(and
(do-WAIT_CB2-condeffs)
(NOT-CLOSED-SD10)
)
:effect
(and
(done-1)
)
)
(:action WAIT_CB2-condeff1-no-2
:parameters ()
:precondition
(and
(do-WAIT_CB2-condeffs)
(NOT-CLOSED-SD9)
)
:effect
(and
(done-1)
)
)
(:action WAIT_CB2-condeff1-no-3
:parameters ()
:precondition
(and
(do-WAIT_CB2-condeffs)
(NOT-CLOSED-SD8)
)
:effect
(and
(done-1)
)
)
(:action WAIT_CB2-condeff1-no-4
:parameters ()
:precondition
(and
(do-WAIT_CB2-condeffs)
(NOT-CLOSED-SD7)
)
:effect
(and
(done-1)
)
)
(:action WAIT_CB2-endof-condeffs
:parameters ()
:precondition
(and
(do-WAIT_CB2-condeffs)
(done-0)
(done-1)
)
:effect
(and
(do-normal)
(not (do-WAIT_CB2-condeffs))
(not (done-0))
(not (done-1))
)
)
(:action CLOSE_CB2
:parameters ()
:precondition
(and
(do-normal)
(NOT-CLOSED-CB2)
(UPDATED-CB1)
(UPDATED-CB2)
)
:effect
(and
(CLOSED-CB2)
(NOT-UPDATED-CB2)
(not (NOT-CLOSED-CB2))
(not (UPDATED-CB2))
)
)
(:action CLOSE_CB1
:parameters ()
:precondition
(and
(do-normal)
(NOT-CLOSED-CB1)
(UPDATED-CB1)
(UPDATED-CB2)
)
:effect
(and
(CLOSED-CB1)
(NOT-UPDATED-CB1)
(not (NOT-CLOSED-CB1))
(not (UPDATED-CB1))
)
)
(:action OPEN-SD10
:parameters ()
:precondition
(and
(do-normal)
(CLOSED-SD10)
(UPDATED-CB1)
(UPDATED-CB2)
)
:effect
(and
(NOT-CLOSED-SD10)
(not (CLOSED-SD10))
)
)
(:action OPEN-SD9
:parameters ()
:precondition
(and
(do-normal)
(CLOSED-SD9)
(UPDATED-CB1)
(UPDATED-CB2)
)
:effect
(and
(NOT-CLOSED-SD9)
(not (CLOSED-SD9))
)
)
(:action OPEN-SD8
:parameters ()
:precondition
(and
(do-normal)
(CLOSED-SD8)
(UPDATED-CB1)
(UPDATED-CB2)
)
:effect
(and
(NOT-CLOSED-SD8)
(not (CLOSED-SD8))
)
)
(:action OPEN-SD7
:parameters ()
:precondition
(and
(do-normal)
(CLOSED-SD7)
(UPDATED-CB1)
(UPDATED-CB2)
)
:effect
(and
(NOT-CLOSED-SD7)
(not (CLOSED-SD7))
)
)
(:action OPEN-SD6
:parameters ()
:precondition
(and
(do-normal)
(CLOSED-SD6)
(UPDATED-CB1)
(UPDATED-CB2)
)
:effect
(and
(NOT-CLOSED-SD6)
(not (CLOSED-SD6))
)
)
(:action OPEN-SD5
:parameters ()
:precondition
(and
(do-normal)
(CLOSED-SD5)
(UPDATED-CB1)
(UPDATED-CB2)
)
:effect
(and
(NOT-CLOSED-SD5)
(not (CLOSED-SD5))
)
)
(:action OPEN-SD4
:parameters ()
:precondition
(and
(do-normal)
(CLOSED-SD4)
(UPDATED-CB1)
(UPDATED-CB2)
)
:effect
(and
(NOT-CLOSED-SD4)
(not (CLOSED-SD4))
)
)
(:action OPEN-SD3
:parameters ()
:precondition
(and
(do-normal)
(CLOSED-SD3)
(UPDATED-CB1)
(UPDATED-CB2)
)
:effect
(and
(NOT-CLOSED-SD3)
(not (CLOSED-SD3))
)
)
(:action OPEN-SD2
:parameters ()
:precondition
(and
(do-normal)
(CLOSED-SD2)
(UPDATED-CB1)
(UPDATED-CB2)
)
:effect
(and
(NOT-CLOSED-SD2)
(not (CLOSED-SD2))
)
)
(:action OPEN-SD1
:parameters ()
:precondition
(and
(do-normal)
(CLOSED-SD1)
(UPDATED-CB1)
(UPDATED-CB2)
)
:effect
(and
(NOT-CLOSED-SD1)
(not (CLOSED-SD1))
)
)
(:action OPEN-CB2
:parameters ()
:precondition
(and
(do-normal)
(CLOSED-CB2)
(UPDATED-CB1)
(UPDATED-CB2)
)
:effect
(and
(NOT-CLOSED-CB2)
(not (CLOSED-CB2))
)
)
(:action OPEN-CB1
:parameters ()
:precondition
(and
(do-normal)
(CLOSED-CB1)
(UPDATED-CB1)
(UPDATED-CB2)
)
:effect
(and
(NOT-CLOSED-CB1)
(not (CLOSED-CB1))
)
)
(:action CLOSE_SD6
:parameters ()
:precondition
(and
(do-normal)
(NOT-CLOSED-SD6)
(UPDATED-CB1)
(UPDATED-CB2)
)
:effect
(and
(not (do-normal))
(do-CLOSE_SD6-condeffs)
(CLOSED-SD6)
(not (NOT-CLOSED-SD6))
)
)
(:action CLOSE_SD6-condeff0-yes
:parameters ()
:precondition
(and
(do-CLOSE_SD6-condeffs)
(CLOSED-SD5)
(CLOSED-SD10)
(CLOSED-SD1)
(CLOSED-CB1)
)
:effect
(and
(done-0)
(NOT-CLOSED-CB1)
(not (CLOSED-CB1))
)
)
(:action CLOSE_SD6-condeff0-no-0
:parameters ()
:precondition
(and
(do-CLOSE_SD6-condeffs)
(NOT-CLOSED-SD5)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD6-condeff0-no-1
:parameters ()
:precondition
(and
(do-CLOSE_SD6-condeffs)
(NOT-CLOSED-SD10)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD6-condeff0-no-2
:parameters ()
:precondition
(and
(do-CLOSE_SD6-condeffs)
(NOT-CLOSED-SD1)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD6-condeff0-no-3
:parameters ()
:precondition
(and
(do-CLOSE_SD6-condeffs)
(NOT-CLOSED-CB1)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD6-condeff1-yes
:parameters ()
:precondition
(and
(do-CLOSE_SD6-condeffs)
(CLOSED-SD4)
(CLOSED-SD3)
(CLOSED-SD2)
(CLOSED-SD9)
(CLOSED-SD8)
(CLOSED-SD7)
(CLOSED-CB2)
)
:effect
(and
(done-1)
(NOT-CLOSED-CB2)
(not (CLOSED-CB2))
)
)
(:action CLOSE_SD6-condeff1-no-0
:parameters ()
:precondition
(and
(do-CLOSE_SD6-condeffs)
(NOT-CLOSED-SD4)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD6-condeff1-no-1
:parameters ()
:precondition
(and
(do-CLOSE_SD6-condeffs)
(NOT-CLOSED-SD3)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD6-condeff1-no-2
:parameters ()
:precondition
(and
(do-CLOSE_SD6-condeffs)
(NOT-CLOSED-SD2)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD6-condeff1-no-3
:parameters ()
:precondition
(and
(do-CLOSE_SD6-condeffs)
(NOT-CLOSED-SD9)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD6-condeff1-no-4
:parameters ()
:precondition
(and
(do-CLOSE_SD6-condeffs)
(NOT-CLOSED-SD8)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD6-condeff1-no-5
:parameters ()
:precondition
(and
(do-CLOSE_SD6-condeffs)
(NOT-CLOSED-SD7)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD6-condeff1-no-6
:parameters ()
:precondition
(and
(do-CLOSE_SD6-condeffs)
(NOT-CLOSED-CB2)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD6-endof-condeffs
:parameters ()
:precondition
(and
(do-CLOSE_SD6-condeffs)
(done-0)
(done-1)
)
:effect
(and
(do-normal)
(not (do-CLOSE_SD6-condeffs))
(not (done-0))
(not (done-1))
)
)
(:action CLOSE_SD5
:parameters ()
:precondition
(and
(do-normal)
(NOT-CLOSED-SD5)
(UPDATED-CB1)
(UPDATED-CB2)
)
:effect
(and
(not (do-normal))
(do-CLOSE_SD5-condeffs)
(CLOSED-SD5)
(not (NOT-CLOSED-SD5))
)
)
(:action CLOSE_SD5-condeff0-yes
:parameters ()
:precondition
(and
(do-CLOSE_SD5-condeffs)
(CLOSED-SD10)
(CLOSED-SD6)
(CLOSED-SD1)
(CLOSED-CB1)
)
:effect
(and
(done-0)
(NOT-CLOSED-CB1)
(not (CLOSED-CB1))
)
)
(:action CLOSE_SD5-condeff0-no-0
:parameters ()
:precondition
(and
(do-CLOSE_SD5-condeffs)
(NOT-CLOSED-SD10)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD5-condeff0-no-1
:parameters ()
:precondition
(and
(do-CLOSE_SD5-condeffs)
(NOT-CLOSED-SD6)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD5-condeff0-no-2
:parameters ()
:precondition
(and
(do-CLOSE_SD5-condeffs)
(NOT-CLOSED-SD1)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD5-condeff0-no-3
:parameters ()
:precondition
(and
(do-CLOSE_SD5-condeffs)
(NOT-CLOSED-CB1)
)
:effect
(and
(done-0)
)
)
(:action CLOSE_SD5-condeff1-yes
:parameters ()
:precondition
(and
(do-CLOSE_SD5-condeffs)
(CLOSED-SD10)
(CLOSED-SD9)
(CLOSED-SD8)
(CLOSED-SD7)
(CLOSED-CB2)
)
:effect
(and
(done-1)
(NOT-CLOSED-CB2)
(not (CLOSED-CB2))
)
)
(:action CLOSE_SD5-condeff1-no-0
:parameters ()
:precondition
(and
(do-CLOSE_SD5-condeffs)
(NOT-CLOSED-SD10)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD5-condeff1-no-1
:parameters ()
:precondition
(and
(do-CLOSE_SD5-condeffs)
(NOT-CLOSED-SD9)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD5-condeff1-no-2
:parameters ()
:precondition
(and
(do-CLOSE_SD5-condeffs)
(NOT-CLOSED-SD8)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD5-condeff1-no-3
:parameters ()
:precondition
(and
(do-CLOSE_SD5-condeffs)
(NOT-CLOSED-SD7)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD5-condeff1-no-4
:parameters ()
:precondition
(and
(do-CLOSE_SD5-condeffs)
(NOT-CLOSED-CB2)
)
:effect
(and
(done-1)
)
)
(:action CLOSE_SD5-endof-condeffs
:parameters ()
:precondition
(and
(do-CLOSE_SD5-condeffs)
(done-0)
(done-1)
)
:effect
(and
(do-normal)
(not (do-CLOSE_SD5-condeffs))
(not (done-0))
(not (done-1))
)
)
(:action WAIT_CB1
:parameters ()
:precondition
(and
(do-normal)
(NOT-UPDATED-CB1)
)
:effect
(and
(not (do-normal))
(do-WAIT_CB1-condeffs)
(UPDATED-CB1)
(not (NOT-UPDATED-CB1))
)
)
(:action WAIT_CB1-condeff0-yes
:parameters ()
:precondition
(and
(do-WAIT_CB1-condeffs)
(CLOSED-SD4)
(CLOSED-SD3)
(CLOSED-SD2)
(CLOSED-SD1)
)
:effect
(and
(done-0)
(NOT-CLOSED-CB1)
(not (CLOSED-CB1))
)
)
(:action WAIT_CB1-condeff0-no-0
:parameters ()
:precondition
(and
(do-WAIT_CB1-condeffs)
(NOT-CLOSED-SD4)
)
:effect
(and
(done-0)
)
)
(:action WAIT_CB1-condeff0-no-1
:parameters ()
:precondition
(and
(do-WAIT_CB1-condeffs)
(NOT-CLOSED-SD3)
)
:effect
(and
(done-0)
)
)
(:action WAIT_CB1-condeff0-no-2
:parameters ()
:precondition
(and
(do-WAIT_CB1-condeffs)
(NOT-CLOSED-SD2)
)
:effect
(and
(done-0)
)
)
(:action WAIT_CB1-condeff0-no-3
:parameters ()
:precondition
(and
(do-WAIT_CB1-condeffs)
(NOT-CLOSED-SD1)
)
:effect
(and
(done-0)
)
)
(:action WAIT_CB1-condeff1-yes
:parameters ()
:precondition
(and
(do-WAIT_CB1-condeffs)
(CLOSED-SD5)
(CLOSED-SD10)
(CLOSED-SD6)
(CLOSED-SD1)
)
:effect
(and
(done-1)
(NOT-CLOSED-CB1)
(not (CLOSED-CB1))
)
)
(:action WAIT_CB1-condeff1-no-0
:parameters ()
:precondition
(and
(do-WAIT_CB1-condeffs)
(NOT-CLOSED-SD5)
)
:effect
(and
(done-1)
)
)
(:action WAIT_CB1-condeff1-no-1
:parameters ()
:precondition
(and
(do-WAIT_CB1-condeffs)
(NOT-CLOSED-SD10)
)
:effect
(and
(done-1)
)
)
(:action WAIT_CB1-condeff1-no-2
:parameters ()
:precondition
(and
(do-WAIT_CB1-condeffs)
(NOT-CLOSED-SD6)
)
:effect
(and
(done-1)
)
)
(:action WAIT_CB1-condeff1-no-3
:parameters ()
:precondition
(and
(do-WAIT_CB1-condeffs)
(NOT-CLOSED-SD1)
)
:effect
(and
(done-1)
)
)
(:action WAIT_CB1-endof-condeffs
:parameters ()
:precondition
(and
(do-WAIT_CB1-condeffs)
(done-0)
(done-1)
)
:effect
(and
(do-normal)
(not (do-WAIT_CB1-condeffs))
(not (done-0))
(not (done-1))
)
)
)
