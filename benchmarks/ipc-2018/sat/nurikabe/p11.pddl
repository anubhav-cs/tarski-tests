(define (problem random-11x11-420)
(:domain nurikabe)
(:objects
    pos-0-0 pos-0-1 pos-0-2 pos-0-3 pos-0-4 pos-0-5 pos-0-6 pos-0-7 pos-0-8 pos-0-9 pos-0-10 pos-1-0 pos-1-1 pos-1-2 pos-1-3 pos-1-4 pos-1-5 pos-1-6 pos-1-7 pos-1-8 pos-1-9 pos-1-10 pos-2-0 pos-2-1 pos-2-2 pos-2-3 pos-2-4 pos-2-5 pos-2-6 pos-2-7 pos-2-8 pos-2-9 pos-2-10 pos-3-0 pos-3-1 pos-3-2 pos-3-3 pos-3-4 pos-3-5 pos-3-6 pos-3-7 pos-3-8 pos-3-9 pos-3-10 pos-4-0 pos-4-1 pos-4-2 pos-4-3 pos-4-4 pos-4-5 pos-4-6 pos-4-7 pos-4-8 pos-4-9 pos-4-10 pos-5-0 pos-5-1 pos-5-2 pos-5-3 pos-5-4 pos-5-5 pos-5-6 pos-5-7 pos-5-8 pos-5-9 pos-5-10 pos-6-0 pos-6-1 pos-6-2 pos-6-3 pos-6-4 pos-6-5 pos-6-6 pos-6-7 pos-6-8 pos-6-9 pos-6-10 pos-7-0 pos-7-1 pos-7-2 pos-7-3 pos-7-4 pos-7-5 pos-7-6 pos-7-7 pos-7-8 pos-7-9 pos-7-10 pos-8-0 pos-8-1 pos-8-2 pos-8-3 pos-8-4 pos-8-5 pos-8-6 pos-8-7 pos-8-8 pos-8-9 pos-8-10 pos-9-0 pos-9-1 pos-9-2 pos-9-3 pos-9-4 pos-9-5 pos-9-6 pos-9-7 pos-9-8 pos-9-9 pos-9-10 pos-10-0 pos-10-1 pos-10-2 pos-10-3 pos-10-4 pos-10-5 pos-10-6 pos-10-7 pos-10-8 pos-10-9 pos-10-10 - cell
    n1 n2 n3 n4 n5 n6 n7 n8 n9 - num
    g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 - group
)
(:init
    (NEXT n0 n1)
    (NEXT n1 n2)
    (NEXT n2 n3)
    (NEXT n3 n4)
    (NEXT n4 n5)
    (NEXT n5 n6)
    (NEXT n6 n7)
    (NEXT n7 n8)
    (NEXT n8 n9)
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
    (CONNECTED pos-0-6 pos-0-7)
    (CONNECTED pos-0-6 pos-0-5)
    (CONNECTED pos-0-7 pos-1-7)
    (CONNECTED pos-0-7 pos-0-8)
    (CONNECTED pos-0-7 pos-0-6)
    (CONNECTED pos-0-8 pos-1-8)
    (CONNECTED pos-0-8 pos-0-9)
    (CONNECTED pos-0-8 pos-0-7)
    (CONNECTED pos-0-9 pos-1-9)
    (CONNECTED pos-0-9 pos-0-10)
    (CONNECTED pos-0-9 pos-0-8)
    (CONNECTED pos-0-10 pos-1-10)
    (CONNECTED pos-0-10 pos-0-9)
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
    (CONNECTED pos-1-6 pos-1-7)
    (CONNECTED pos-1-6 pos-0-6)
    (CONNECTED pos-1-6 pos-1-5)
    (CONNECTED pos-1-7 pos-2-7)
    (CONNECTED pos-1-7 pos-1-8)
    (CONNECTED pos-1-7 pos-0-7)
    (CONNECTED pos-1-7 pos-1-6)
    (CONNECTED pos-1-8 pos-2-8)
    (CONNECTED pos-1-8 pos-1-9)
    (CONNECTED pos-1-8 pos-0-8)
    (CONNECTED pos-1-8 pos-1-7)
    (CONNECTED pos-1-9 pos-2-9)
    (CONNECTED pos-1-9 pos-1-10)
    (CONNECTED pos-1-9 pos-0-9)
    (CONNECTED pos-1-9 pos-1-8)
    (CONNECTED pos-1-10 pos-2-10)
    (CONNECTED pos-1-10 pos-0-10)
    (CONNECTED pos-1-10 pos-1-9)
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
    (CONNECTED pos-2-6 pos-2-7)
    (CONNECTED pos-2-6 pos-1-6)
    (CONNECTED pos-2-6 pos-2-5)
    (CONNECTED pos-2-7 pos-3-7)
    (CONNECTED pos-2-7 pos-2-8)
    (CONNECTED pos-2-7 pos-1-7)
    (CONNECTED pos-2-7 pos-2-6)
    (CONNECTED pos-2-8 pos-3-8)
    (CONNECTED pos-2-8 pos-2-9)
    (CONNECTED pos-2-8 pos-1-8)
    (CONNECTED pos-2-8 pos-2-7)
    (CONNECTED pos-2-9 pos-3-9)
    (CONNECTED pos-2-9 pos-2-10)
    (CONNECTED pos-2-9 pos-1-9)
    (CONNECTED pos-2-9 pos-2-8)
    (CONNECTED pos-2-10 pos-3-10)
    (CONNECTED pos-2-10 pos-1-10)
    (CONNECTED pos-2-10 pos-2-9)
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
    (CONNECTED pos-3-6 pos-3-7)
    (CONNECTED pos-3-6 pos-2-6)
    (CONNECTED pos-3-6 pos-3-5)
    (CONNECTED pos-3-7 pos-4-7)
    (CONNECTED pos-3-7 pos-3-8)
    (CONNECTED pos-3-7 pos-2-7)
    (CONNECTED pos-3-7 pos-3-6)
    (CONNECTED pos-3-8 pos-4-8)
    (CONNECTED pos-3-8 pos-3-9)
    (CONNECTED pos-3-8 pos-2-8)
    (CONNECTED pos-3-8 pos-3-7)
    (CONNECTED pos-3-9 pos-4-9)
    (CONNECTED pos-3-9 pos-3-10)
    (CONNECTED pos-3-9 pos-2-9)
    (CONNECTED pos-3-9 pos-3-8)
    (CONNECTED pos-3-10 pos-4-10)
    (CONNECTED pos-3-10 pos-2-10)
    (CONNECTED pos-3-10 pos-3-9)
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
    (CONNECTED pos-4-6 pos-4-7)
    (CONNECTED pos-4-6 pos-3-6)
    (CONNECTED pos-4-6 pos-4-5)
    (CONNECTED pos-4-7 pos-5-7)
    (CONNECTED pos-4-7 pos-4-8)
    (CONNECTED pos-4-7 pos-3-7)
    (CONNECTED pos-4-7 pos-4-6)
    (CONNECTED pos-4-8 pos-5-8)
    (CONNECTED pos-4-8 pos-4-9)
    (CONNECTED pos-4-8 pos-3-8)
    (CONNECTED pos-4-8 pos-4-7)
    (CONNECTED pos-4-9 pos-5-9)
    (CONNECTED pos-4-9 pos-4-10)
    (CONNECTED pos-4-9 pos-3-9)
    (CONNECTED pos-4-9 pos-4-8)
    (CONNECTED pos-4-10 pos-5-10)
    (CONNECTED pos-4-10 pos-3-10)
    (CONNECTED pos-4-10 pos-4-9)
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
    (CONNECTED pos-5-6 pos-5-7)
    (CONNECTED pos-5-6 pos-4-6)
    (CONNECTED pos-5-6 pos-5-5)
    (CONNECTED pos-5-7 pos-6-7)
    (CONNECTED pos-5-7 pos-5-8)
    (CONNECTED pos-5-7 pos-4-7)
    (CONNECTED pos-5-7 pos-5-6)
    (CONNECTED pos-5-8 pos-6-8)
    (CONNECTED pos-5-8 pos-5-9)
    (CONNECTED pos-5-8 pos-4-8)
    (CONNECTED pos-5-8 pos-5-7)
    (CONNECTED pos-5-9 pos-6-9)
    (CONNECTED pos-5-9 pos-5-10)
    (CONNECTED pos-5-9 pos-4-9)
    (CONNECTED pos-5-9 pos-5-8)
    (CONNECTED pos-5-10 pos-6-10)
    (CONNECTED pos-5-10 pos-4-10)
    (CONNECTED pos-5-10 pos-5-9)
    (CONNECTED pos-6-0 pos-7-0)
    (CONNECTED pos-6-0 pos-6-1)
    (CONNECTED pos-6-0 pos-5-0)
    (CONNECTED pos-6-1 pos-7-1)
    (CONNECTED pos-6-1 pos-6-2)
    (CONNECTED pos-6-1 pos-5-1)
    (CONNECTED pos-6-1 pos-6-0)
    (CONNECTED pos-6-2 pos-7-2)
    (CONNECTED pos-6-2 pos-6-3)
    (CONNECTED pos-6-2 pos-5-2)
    (CONNECTED pos-6-2 pos-6-1)
    (CONNECTED pos-6-3 pos-7-3)
    (CONNECTED pos-6-3 pos-6-4)
    (CONNECTED pos-6-3 pos-5-3)
    (CONNECTED pos-6-3 pos-6-2)
    (CONNECTED pos-6-4 pos-7-4)
    (CONNECTED pos-6-4 pos-6-5)
    (CONNECTED pos-6-4 pos-5-4)
    (CONNECTED pos-6-4 pos-6-3)
    (CONNECTED pos-6-5 pos-7-5)
    (CONNECTED pos-6-5 pos-6-6)
    (CONNECTED pos-6-5 pos-5-5)
    (CONNECTED pos-6-5 pos-6-4)
    (CONNECTED pos-6-6 pos-7-6)
    (CONNECTED pos-6-6 pos-6-7)
    (CONNECTED pos-6-6 pos-5-6)
    (CONNECTED pos-6-6 pos-6-5)
    (CONNECTED pos-6-7 pos-7-7)
    (CONNECTED pos-6-7 pos-6-8)
    (CONNECTED pos-6-7 pos-5-7)
    (CONNECTED pos-6-7 pos-6-6)
    (CONNECTED pos-6-8 pos-7-8)
    (CONNECTED pos-6-8 pos-6-9)
    (CONNECTED pos-6-8 pos-5-8)
    (CONNECTED pos-6-8 pos-6-7)
    (CONNECTED pos-6-9 pos-7-9)
    (CONNECTED pos-6-9 pos-6-10)
    (CONNECTED pos-6-9 pos-5-9)
    (CONNECTED pos-6-9 pos-6-8)
    (CONNECTED pos-6-10 pos-7-10)
    (CONNECTED pos-6-10 pos-5-10)
    (CONNECTED pos-6-10 pos-6-9)
    (CONNECTED pos-7-0 pos-8-0)
    (CONNECTED pos-7-0 pos-7-1)
    (CONNECTED pos-7-0 pos-6-0)
    (CONNECTED pos-7-1 pos-8-1)
    (CONNECTED pos-7-1 pos-7-2)
    (CONNECTED pos-7-1 pos-6-1)
    (CONNECTED pos-7-1 pos-7-0)
    (CONNECTED pos-7-2 pos-8-2)
    (CONNECTED pos-7-2 pos-7-3)
    (CONNECTED pos-7-2 pos-6-2)
    (CONNECTED pos-7-2 pos-7-1)
    (CONNECTED pos-7-3 pos-8-3)
    (CONNECTED pos-7-3 pos-7-4)
    (CONNECTED pos-7-3 pos-6-3)
    (CONNECTED pos-7-3 pos-7-2)
    (CONNECTED pos-7-4 pos-8-4)
    (CONNECTED pos-7-4 pos-7-5)
    (CONNECTED pos-7-4 pos-6-4)
    (CONNECTED pos-7-4 pos-7-3)
    (CONNECTED pos-7-5 pos-8-5)
    (CONNECTED pos-7-5 pos-7-6)
    (CONNECTED pos-7-5 pos-6-5)
    (CONNECTED pos-7-5 pos-7-4)
    (CONNECTED pos-7-6 pos-8-6)
    (CONNECTED pos-7-6 pos-7-7)
    (CONNECTED pos-7-6 pos-6-6)
    (CONNECTED pos-7-6 pos-7-5)
    (CONNECTED pos-7-7 pos-8-7)
    (CONNECTED pos-7-7 pos-7-8)
    (CONNECTED pos-7-7 pos-6-7)
    (CONNECTED pos-7-7 pos-7-6)
    (CONNECTED pos-7-8 pos-8-8)
    (CONNECTED pos-7-8 pos-7-9)
    (CONNECTED pos-7-8 pos-6-8)
    (CONNECTED pos-7-8 pos-7-7)
    (CONNECTED pos-7-9 pos-8-9)
    (CONNECTED pos-7-9 pos-7-10)
    (CONNECTED pos-7-9 pos-6-9)
    (CONNECTED pos-7-9 pos-7-8)
    (CONNECTED pos-7-10 pos-8-10)
    (CONNECTED pos-7-10 pos-6-10)
    (CONNECTED pos-7-10 pos-7-9)
    (CONNECTED pos-8-0 pos-9-0)
    (CONNECTED pos-8-0 pos-8-1)
    (CONNECTED pos-8-0 pos-7-0)
    (CONNECTED pos-8-1 pos-9-1)
    (CONNECTED pos-8-1 pos-8-2)
    (CONNECTED pos-8-1 pos-7-1)
    (CONNECTED pos-8-1 pos-8-0)
    (CONNECTED pos-8-2 pos-9-2)
    (CONNECTED pos-8-2 pos-8-3)
    (CONNECTED pos-8-2 pos-7-2)
    (CONNECTED pos-8-2 pos-8-1)
    (CONNECTED pos-8-3 pos-9-3)
    (CONNECTED pos-8-3 pos-8-4)
    (CONNECTED pos-8-3 pos-7-3)
    (CONNECTED pos-8-3 pos-8-2)
    (CONNECTED pos-8-4 pos-9-4)
    (CONNECTED pos-8-4 pos-8-5)
    (CONNECTED pos-8-4 pos-7-4)
    (CONNECTED pos-8-4 pos-8-3)
    (CONNECTED pos-8-5 pos-9-5)
    (CONNECTED pos-8-5 pos-8-6)
    (CONNECTED pos-8-5 pos-7-5)
    (CONNECTED pos-8-5 pos-8-4)
    (CONNECTED pos-8-6 pos-9-6)
    (CONNECTED pos-8-6 pos-8-7)
    (CONNECTED pos-8-6 pos-7-6)
    (CONNECTED pos-8-6 pos-8-5)
    (CONNECTED pos-8-7 pos-9-7)
    (CONNECTED pos-8-7 pos-8-8)
    (CONNECTED pos-8-7 pos-7-7)
    (CONNECTED pos-8-7 pos-8-6)
    (CONNECTED pos-8-8 pos-9-8)
    (CONNECTED pos-8-8 pos-8-9)
    (CONNECTED pos-8-8 pos-7-8)
    (CONNECTED pos-8-8 pos-8-7)
    (CONNECTED pos-8-9 pos-9-9)
    (CONNECTED pos-8-9 pos-8-10)
    (CONNECTED pos-8-9 pos-7-9)
    (CONNECTED pos-8-9 pos-8-8)
    (CONNECTED pos-8-10 pos-9-10)
    (CONNECTED pos-8-10 pos-7-10)
    (CONNECTED pos-8-10 pos-8-9)
    (CONNECTED pos-9-0 pos-10-0)
    (CONNECTED pos-9-0 pos-9-1)
    (CONNECTED pos-9-0 pos-8-0)
    (CONNECTED pos-9-1 pos-10-1)
    (CONNECTED pos-9-1 pos-9-2)
    (CONNECTED pos-9-1 pos-8-1)
    (CONNECTED pos-9-1 pos-9-0)
    (CONNECTED pos-9-2 pos-10-2)
    (CONNECTED pos-9-2 pos-9-3)
    (CONNECTED pos-9-2 pos-8-2)
    (CONNECTED pos-9-2 pos-9-1)
    (CONNECTED pos-9-3 pos-10-3)
    (CONNECTED pos-9-3 pos-9-4)
    (CONNECTED pos-9-3 pos-8-3)
    (CONNECTED pos-9-3 pos-9-2)
    (CONNECTED pos-9-4 pos-10-4)
    (CONNECTED pos-9-4 pos-9-5)
    (CONNECTED pos-9-4 pos-8-4)
    (CONNECTED pos-9-4 pos-9-3)
    (CONNECTED pos-9-5 pos-10-5)
    (CONNECTED pos-9-5 pos-9-6)
    (CONNECTED pos-9-5 pos-8-5)
    (CONNECTED pos-9-5 pos-9-4)
    (CONNECTED pos-9-6 pos-10-6)
    (CONNECTED pos-9-6 pos-9-7)
    (CONNECTED pos-9-6 pos-8-6)
    (CONNECTED pos-9-6 pos-9-5)
    (CONNECTED pos-9-7 pos-10-7)
    (CONNECTED pos-9-7 pos-9-8)
    (CONNECTED pos-9-7 pos-8-7)
    (CONNECTED pos-9-7 pos-9-6)
    (CONNECTED pos-9-8 pos-10-8)
    (CONNECTED pos-9-8 pos-9-9)
    (CONNECTED pos-9-8 pos-8-8)
    (CONNECTED pos-9-8 pos-9-7)
    (CONNECTED pos-9-9 pos-10-9)
    (CONNECTED pos-9-9 pos-9-10)
    (CONNECTED pos-9-9 pos-8-9)
    (CONNECTED pos-9-9 pos-9-8)
    (CONNECTED pos-9-10 pos-10-10)
    (CONNECTED pos-9-10 pos-8-10)
    (CONNECTED pos-9-10 pos-9-9)
    (CONNECTED pos-10-0 pos-10-1)
    (CONNECTED pos-10-0 pos-9-0)
    (CONNECTED pos-10-1 pos-10-2)
    (CONNECTED pos-10-1 pos-9-1)
    (CONNECTED pos-10-1 pos-10-0)
    (CONNECTED pos-10-2 pos-10-3)
    (CONNECTED pos-10-2 pos-9-2)
    (CONNECTED pos-10-2 pos-10-1)
    (CONNECTED pos-10-3 pos-10-4)
    (CONNECTED pos-10-3 pos-9-3)
    (CONNECTED pos-10-3 pos-10-2)
    (CONNECTED pos-10-4 pos-10-5)
    (CONNECTED pos-10-4 pos-9-4)
    (CONNECTED pos-10-4 pos-10-3)
    (CONNECTED pos-10-5 pos-10-6)
    (CONNECTED pos-10-5 pos-9-5)
    (CONNECTED pos-10-5 pos-10-4)
    (CONNECTED pos-10-6 pos-10-7)
    (CONNECTED pos-10-6 pos-9-6)
    (CONNECTED pos-10-6 pos-10-5)
    (CONNECTED pos-10-7 pos-10-8)
    (CONNECTED pos-10-7 pos-9-7)
    (CONNECTED pos-10-7 pos-10-6)
    (CONNECTED pos-10-8 pos-10-9)
    (CONNECTED pos-10-8 pos-9-8)
    (CONNECTED pos-10-8 pos-10-7)
    (CONNECTED pos-10-9 pos-10-10)
    (CONNECTED pos-10-9 pos-9-9)
    (CONNECTED pos-10-9 pos-10-8)
    (CONNECTED pos-10-10 pos-9-10)
    (CONNECTED pos-10-10 pos-10-9)
    (robot-pos pos-0-0)
    (moving)
    (SOURCE pos-2-0 g0)
    (SOURCE pos-7-0 g1)
    (SOURCE pos-1-1 g2)
    (SOURCE pos-9-1 g3)
    (SOURCE pos-3-2 g4)
    (SOURCE pos-8-2 g5)
    (SOURCE pos-10-3 g6)
    (SOURCE pos-2-4 g7)
    (SOURCE pos-0-5 g8)
    (SOURCE pos-7-6 g9)
    (SOURCE pos-2-7 g10)
    (SOURCE pos-8-7 g11)
    (SOURCE pos-1-8 g12)
    (SOURCE pos-3-9 g13)
    (SOURCE pos-8-9 g14)
    (SOURCE pos-1-10 g15)
    (available pos-0-0)
    (available pos-0-2)
    (available pos-0-3)
    (available pos-0-7)
    (available pos-0-9)
    (available pos-1-3)
    (available pos-1-6)
    (available pos-3-5)
    (available pos-3-6)
    (available pos-4-0)
    (available pos-4-1)
    (available pos-4-3)
    (available pos-4-4)
    (available pos-4-5)
    (available pos-4-6)
    (available pos-4-7)
    (available pos-4-8)
    (available pos-4-10)
    (available pos-5-0)
    (available pos-5-1)
    (available pos-5-2)
    (available pos-5-3)
    (available pos-5-4)
    (available pos-5-5)
    (available pos-5-6)
    (available pos-5-7)
    (available pos-5-8)
    (available pos-5-9)
    (available pos-5-10)
    (available pos-6-1)
    (available pos-6-2)
    (available pos-6-3)
    (available pos-6-4)
    (available pos-6-5)
    (available pos-6-7)
    (available pos-6-8)
    (available pos-6-9)
    (available pos-6-10)
    (available pos-7-3)
    (available pos-7-4)
    (available pos-7-8)
    (available pos-7-10)
    (available pos-8-4)
    (available pos-8-5)
    (available pos-9-4)
    (available pos-9-5)
    (available pos-9-6)
    (available pos-9-8)
    (available pos-9-10)
    (available pos-10-0)
    (available pos-10-5)
    (available pos-10-6)
    (available pos-10-7)
    (available pos-10-8)
    (available pos-10-9)
    (available pos-10-10)
    (blocked pos-2-1)
    (blocked pos-1-0)
    (blocked pos-9-2)
    (blocked pos-8-1)
    (blocked pos-7-7)
    (blocked pos-8-6)
    (blocked pos-2-8)
    (blocked pos-1-7)
    (blocked pos-8-8)
    (blocked pos-1-9)
    (part-of pos-3-0 g0)
    (part-of pos-8-0 g1)
    (part-of pos-7-1 g1)
    (part-of pos-6-0 g1)
    (part-of pos-1-2 g2)
    (part-of pos-0-1 g2)
    (part-of pos-10-1 g3)
    (part-of pos-9-0 g3)
    (part-of pos-4-2 g4)
    (part-of pos-3-3 g4)
    (part-of pos-2-2 g4)
    (part-of pos-3-1 g4)
    (part-of pos-8-3 g5)
    (part-of pos-7-2 g5)
    (part-of pos-10-4 g6)
    (part-of pos-9-3 g6)
    (part-of pos-10-2 g6)
    (part-of pos-3-4 g7)
    (part-of pos-2-5 g7)
    (part-of pos-1-4 g7)
    (part-of pos-2-3 g7)
    (part-of pos-1-5 g8)
    (part-of pos-0-6 g8)
    (part-of pos-0-4 g8)
    (part-of pos-6-6 g9)
    (part-of pos-7-5 g9)
    (part-of pos-3-7 g10)
    (part-of pos-2-6 g10)
    (part-of pos-9-7 g11)
    (part-of pos-0-8 g12)
    (part-of pos-4-9 g13)
    (part-of pos-3-10 g13)
    (part-of pos-2-9 g13)
    (part-of pos-3-8 g13)
    (part-of pos-9-9 g14)
    (part-of pos-8-10 g14)
    (part-of pos-7-9 g14)
    (part-of pos-2-10 g15)
    (part-of pos-0-10 g15)
    (remaining-cells g0 n2)
    (remaining-cells g1 n4)
    (remaining-cells g2 n3)
    (remaining-cells g3 n1)
    (remaining-cells g4 n9)
    (remaining-cells g5 n1)
    (remaining-cells g6 n6)
    (remaining-cells g7 n2)
    (remaining-cells g8 n3)
    (remaining-cells g9 n1)
    (remaining-cells g10 n6)
    (remaining-cells g11 n2)
    (remaining-cells g12 n1)
    (remaining-cells g13 n2)
    (remaining-cells g14 n8)
    (remaining-cells g15 n1)
)
(:goal
(and
    (group-painted g0)
    (group-painted g1)
    (group-painted g2)
    (group-painted g3)
    (group-painted g4)
    (group-painted g5)
    (group-painted g6)
    (group-painted g7)
    (group-painted g8)
    (group-painted g9)
    (group-painted g10)
    (group-painted g11)
    (group-painted g12)
    (group-painted g13)
    (group-painted g14)
    (group-painted g15)
)
)
)