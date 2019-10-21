(define (problem random-7x7-77)
(:domain nurikabe)
(:objects
    pos-0-0 pos-0-1 pos-0-2 pos-0-3 pos-0-4 pos-0-5 pos-0-6 pos-1-0 pos-1-1 pos-1-2 pos-1-3 pos-1-4 pos-1-5 pos-1-6 pos-2-0 pos-2-1 pos-2-2 pos-2-3 pos-2-4 pos-2-5 pos-2-6 pos-3-0 pos-3-1 pos-3-2 pos-3-3 pos-3-4 pos-3-5 pos-3-6 pos-4-0 pos-4-1 pos-4-2 pos-4-3 pos-4-4 pos-4-5 pos-4-6 pos-5-0 pos-5-1 pos-5-2 pos-5-3 pos-5-4 pos-5-5 pos-5-6 pos-6-0 pos-6-1 pos-6-2 pos-6-3 pos-6-4 pos-6-5 pos-6-6 - cell
    n1 n2 n3 n4 n5 n6 - num
    g0 g1 g2 g3 g4 g5 - group
)
(:init
    (NEXT n0 n1)
    (NEXT n1 n2)
    (NEXT n2 n3)
    (NEXT n3 n4)
    (NEXT n4 n5)
    (NEXT n5 n6)
    (CONNECTED pos-0-0 pos-1-0)
    (CONNECTED pos-0-0 pos-0-1)
    (CONNECTED pos-0-1 pos-1-1)
    (CONNECTED pos-0-1 pos-0-2)
    (CONNECTED pos-0-1 pos-0-0)
    (CONNECTED pos-0-2 pos-1-2)
    (CONNECTED pos-0-2 pos-0-3)
    (CONNECTED pos-0-2 pos-0-1)
    (CONNECTED pos-0-3 pos-1-3)
    (CONNECTED pos-0-3 pos-0-4)
    (CONNECTED pos-0-3 pos-0-2)
    (CONNECTED pos-0-4 pos-1-4)
    (CONNECTED pos-0-4 pos-0-5)
    (CONNECTED pos-0-4 pos-0-3)
    (CONNECTED pos-0-5 pos-1-5)
    (CONNECTED pos-0-5 pos-0-6)
    (CONNECTED pos-0-5 pos-0-4)
    (CONNECTED pos-0-6 pos-1-6)
    (CONNECTED pos-0-6 pos-0-5)
    (CONNECTED pos-1-0 pos-2-0)
    (CONNECTED pos-1-0 pos-1-1)
    (CONNECTED pos-1-0 pos-0-0)
    (CONNECTED pos-1-1 pos-2-1)
    (CONNECTED pos-1-1 pos-1-2)
    (CONNECTED pos-1-1 pos-0-1)
    (CONNECTED pos-1-1 pos-1-0)
    (CONNECTED pos-1-2 pos-2-2)
    (CONNECTED pos-1-2 pos-1-3)
    (CONNECTED pos-1-2 pos-0-2)
    (CONNECTED pos-1-2 pos-1-1)
    (CONNECTED pos-1-3 pos-2-3)
    (CONNECTED pos-1-3 pos-1-4)
    (CONNECTED pos-1-3 pos-0-3)
    (CONNECTED pos-1-3 pos-1-2)
    (CONNECTED pos-1-4 pos-2-4)
    (CONNECTED pos-1-4 pos-1-5)
    (CONNECTED pos-1-4 pos-0-4)
    (CONNECTED pos-1-4 pos-1-3)
    (CONNECTED pos-1-5 pos-2-5)
    (CONNECTED pos-1-5 pos-1-6)
    (CONNECTED pos-1-5 pos-0-5)
    (CONNECTED pos-1-5 pos-1-4)
    (CONNECTED pos-1-6 pos-2-6)
    (CONNECTED pos-1-6 pos-0-6)
    (CONNECTED pos-1-6 pos-1-5)
    (CONNECTED pos-2-0 pos-3-0)
    (CONNECTED pos-2-0 pos-2-1)
    (CONNECTED pos-2-0 pos-1-0)
    (CONNECTED pos-2-1 pos-3-1)
    (CONNECTED pos-2-1 pos-2-2)
    (CONNECTED pos-2-1 pos-1-1)
    (CONNECTED pos-2-1 pos-2-0)
    (CONNECTED pos-2-2 pos-3-2)
    (CONNECTED pos-2-2 pos-2-3)
    (CONNECTED pos-2-2 pos-1-2)
    (CONNECTED pos-2-2 pos-2-1)
    (CONNECTED pos-2-3 pos-3-3)
    (CONNECTED pos-2-3 pos-2-4)
    (CONNECTED pos-2-3 pos-1-3)
    (CONNECTED pos-2-3 pos-2-2)
    (CONNECTED pos-2-4 pos-3-4)
    (CONNECTED pos-2-4 pos-2-5)
    (CONNECTED pos-2-4 pos-1-4)
    (CONNECTED pos-2-4 pos-2-3)
    (CONNECTED pos-2-5 pos-3-5)
    (CONNECTED pos-2-5 pos-2-6)
    (CONNECTED pos-2-5 pos-1-5)
    (CONNECTED pos-2-5 pos-2-4)
    (CONNECTED pos-2-6 pos-3-6)
    (CONNECTED pos-2-6 pos-1-6)
    (CONNECTED pos-2-6 pos-2-5)
    (CONNECTED pos-3-0 pos-4-0)
    (CONNECTED pos-3-0 pos-3-1)
    (CONNECTED pos-3-0 pos-2-0)
    (CONNECTED pos-3-1 pos-4-1)
    (CONNECTED pos-3-1 pos-3-2)
    (CONNECTED pos-3-1 pos-2-1)
    (CONNECTED pos-3-1 pos-3-0)
    (CONNECTED pos-3-2 pos-4-2)
    (CONNECTED pos-3-2 pos-3-3)
    (CONNECTED pos-3-2 pos-2-2)
    (CONNECTED pos-3-2 pos-3-1)
    (CONNECTED pos-3-3 pos-4-3)
    (CONNECTED pos-3-3 pos-3-4)
    (CONNECTED pos-3-3 pos-2-3)
    (CONNECTED pos-3-3 pos-3-2)
    (CONNECTED pos-3-4 pos-4-4)
    (CONNECTED pos-3-4 pos-3-5)
    (CONNECTED pos-3-4 pos-2-4)
    (CONNECTED pos-3-4 pos-3-3)
    (CONNECTED pos-3-5 pos-4-5)
    (CONNECTED pos-3-5 pos-3-6)
    (CONNECTED pos-3-5 pos-2-5)
    (CONNECTED pos-3-5 pos-3-4)
    (CONNECTED pos-3-6 pos-4-6)
    (CONNECTED pos-3-6 pos-2-6)
    (CONNECTED pos-3-6 pos-3-5)
    (CONNECTED pos-4-0 pos-5-0)
    (CONNECTED pos-4-0 pos-4-1)
    (CONNECTED pos-4-0 pos-3-0)
    (CONNECTED pos-4-1 pos-5-1)
    (CONNECTED pos-4-1 pos-4-2)
    (CONNECTED pos-4-1 pos-3-1)
    (CONNECTED pos-4-1 pos-4-0)
    (CONNECTED pos-4-2 pos-5-2)
    (CONNECTED pos-4-2 pos-4-3)
    (CONNECTED pos-4-2 pos-3-2)
    (CONNECTED pos-4-2 pos-4-1)
    (CONNECTED pos-4-3 pos-5-3)
    (CONNECTED pos-4-3 pos-4-4)
    (CONNECTED pos-4-3 pos-3-3)
    (CONNECTED pos-4-3 pos-4-2)
    (CONNECTED pos-4-4 pos-5-4)
    (CONNECTED pos-4-4 pos-4-5)
    (CONNECTED pos-4-4 pos-3-4)
    (CONNECTED pos-4-4 pos-4-3)
    (CONNECTED pos-4-5 pos-5-5)
    (CONNECTED pos-4-5 pos-4-6)
    (CONNECTED pos-4-5 pos-3-5)
    (CONNECTED pos-4-5 pos-4-4)
    (CONNECTED pos-4-6 pos-5-6)
    (CONNECTED pos-4-6 pos-3-6)
    (CONNECTED pos-4-6 pos-4-5)
    (CONNECTED pos-5-0 pos-6-0)
    (CONNECTED pos-5-0 pos-5-1)
    (CONNECTED pos-5-0 pos-4-0)
    (CONNECTED pos-5-1 pos-6-1)
    (CONNECTED pos-5-1 pos-5-2)
    (CONNECTED pos-5-1 pos-4-1)
    (CONNECTED pos-5-1 pos-5-0)
    (CONNECTED pos-5-2 pos-6-2)
    (CONNECTED pos-5-2 pos-5-3)
    (CONNECTED pos-5-2 pos-4-2)
    (CONNECTED pos-5-2 pos-5-1)
    (CONNECTED pos-5-3 pos-6-3)
    (CONNECTED pos-5-3 pos-5-4)
    (CONNECTED pos-5-3 pos-4-3)
    (CONNECTED pos-5-3 pos-5-2)
    (CONNECTED pos-5-4 pos-6-4)
    (CONNECTED pos-5-4 pos-5-5)
    (CONNECTED pos-5-4 pos-4-4)
    (CONNECTED pos-5-4 pos-5-3)
    (CONNECTED pos-5-5 pos-6-5)
    (CONNECTED pos-5-5 pos-5-6)
    (CONNECTED pos-5-5 pos-4-5)
    (CONNECTED pos-5-5 pos-5-4)
    (CONNECTED pos-5-6 pos-6-6)
    (CONNECTED pos-5-6 pos-4-6)
    (CONNECTED pos-5-6 pos-5-5)
    (CONNECTED pos-6-0 pos-6-1)
    (CONNECTED pos-6-0 pos-5-0)
    (CONNECTED pos-6-1 pos-6-2)
    (CONNECTED pos-6-1 pos-5-1)
    (CONNECTED pos-6-1 pos-6-0)
    (CONNECTED pos-6-2 pos-6-3)
    (CONNECTED pos-6-2 pos-5-2)
    (CONNECTED pos-6-2 pos-6-1)
    (CONNECTED pos-6-3 pos-6-4)
    (CONNECTED pos-6-3 pos-5-3)
    (CONNECTED pos-6-3 pos-6-2)
    (CONNECTED pos-6-4 pos-6-5)
    (CONNECTED pos-6-4 pos-5-4)
    (CONNECTED pos-6-4 pos-6-3)
    (CONNECTED pos-6-5 pos-6-6)
    (CONNECTED pos-6-5 pos-5-5)
    (CONNECTED pos-6-5 pos-6-4)
    (CONNECTED pos-6-6 pos-5-6)
    (CONNECTED pos-6-6 pos-6-5)
    (robot-pos pos-0-0)
    (moving)
    (SOURCE pos-1-1 g0)
    (SOURCE pos-3-1 g1)
    (SOURCE pos-5-1 g2)
    (SOURCE pos-0-4 g3)
    (SOURCE pos-5-4 g4)
    (SOURCE pos-4-6 g5)
    (available pos-0-0)
    (available pos-0-2)
    (available pos-0-6)
    (available pos-1-3)
    (available pos-1-5)
    (available pos-1-6)
    (available pos-2-0)
    (available pos-2-2)
    (available pos-2-3)
    (available pos-2-4)
    (available pos-2-5)
    (available pos-2-6)
    (available pos-3-3)
    (available pos-3-4)
    (available pos-3-5)
    (available pos-4-0)
    (available pos-4-2)
    (available pos-4-3)
    (available pos-6-0)
    (available pos-6-2)
    (available pos-6-3)
    (available pos-6-5)
    (available pos-6-6)
    (blocked pos-2-1)
    (blocked pos-4-1)
    (part-of pos-1-2 g0)
    (part-of pos-0-1 g0)
    (part-of pos-1-0 g0)
    (part-of pos-3-2 g1)
    (part-of pos-3-0 g1)
    (part-of pos-6-1 g2)
    (part-of pos-5-2 g2)
    (part-of pos-5-0 g2)
    (part-of pos-1-4 g3)
    (part-of pos-0-5 g3)
    (part-of pos-0-3 g3)
    (part-of pos-6-4 g4)
    (part-of pos-5-5 g4)
    (part-of pos-4-4 g4)
    (part-of pos-5-3 g4)
    (part-of pos-5-6 g5)
    (part-of pos-3-6 g5)
    (part-of pos-4-5 g5)
    (remaining-cells g0 n6)
    (remaining-cells g1 n1)
    (remaining-cells g2 n4)
    (remaining-cells g3 n5)
    (remaining-cells g4 n2)
    (remaining-cells g5 n1)
)
(:goal
(and
    (group-painted g0)
    (group-painted g1)
    (group-painted g2)
    (group-painted g3)
    (group-painted g4)
    (group-painted g5)
)
)
)