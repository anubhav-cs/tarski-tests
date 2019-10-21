
(define (problem os-sequencedstrips-sp4-1)
        (:domain openstacks-sequencedstrips)
        (:objects n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17
         n18 n19 n20 n21 n22 n23 n24 n25 - count o1 o2 o3 o4 o5 o6 o7 o8 o9 o10
         o11 o12 o13 o14 o15 o16 o17 o18 o19 o20 o21 o22 o23 o24 o25 - order p1
         p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20
         p21 p22 p23 p24 p25 - product)
        (:init (machine-available) (next-count n0 n1) (next-count n1 n2)
         (next-count n2 n3) (next-count n3 n4) (next-count n4 n5)
         (next-count n5 n6) (next-count n6 n7) (next-count n7 n8)
         (next-count n8 n9) (next-count n9 n10) (next-count n10 n11)
         (next-count n11 n12) (next-count n12 n13) (next-count n13 n14)
         (next-count n14 n15) (next-count n15 n16) (next-count n16 n17)
         (next-count n17 n18) (next-count n18 n19) (next-count n19 n20)
         (next-count n20 n21) (next-count n21 n22) (next-count n22 n23)
         (next-count n23 n24) (next-count n24 n25) (stacks-avail n0)
         (waiting o1) (includes o1 p3) (includes o1 p11) (includes o1 p12)
         (includes o1 p22) (includes o1 p24) (waiting o2) (includes o2 p7)
         (includes o2 p12) (waiting o3) (includes o3 p25) (waiting o4)
         (includes o4 p8) (includes o4 p12) (includes o4 p15) (includes o4 p16)
         (includes o4 p21) (includes o4 p22) (includes o4 p25) (waiting o5)
         (includes o5 p11) (includes o5 p23) (waiting o6) (includes o6 p13)
         (waiting o7) (includes o7 p7) (includes o7 p14) (includes o7 p17)
         (includes o7 p20) (includes o7 p22) (waiting o8) (includes o8 p5)
         (includes o8 p12) (waiting o9) (includes o9 p2) (includes o9 p21)
         (includes o9 p22) (waiting o10) (includes o10 p20) (includes o10 p22)
         (waiting o11) (includes o11 p7) (includes o11 p18) (waiting o12)
         (includes o12 p9) (includes o12 p21) (waiting o13) (includes o13 p1)
         (includes o13 p19) (includes o13 p24) (waiting o14) (includes o14 p21)
         (includes o14 p23) (waiting o15) (includes o15 p4) (includes o15 p25)
         (waiting o16) (includes o16 p12) (waiting o17) (includes o17 p5)
         (includes o17 p18) (includes o17 p19) (includes o17 p23) (waiting o18)
         (includes o18 p20) (waiting o19) (includes o19 p5) (includes o19 p9)
         (includes o19 p22) (waiting o20) (includes o20 p6) (includes o20 p9)
         (waiting o21) (includes o21 p2) (waiting o22) (includes o22 p9)
         (includes o22 p19) (includes o22 p20) (includes o22 p22) (waiting o23)
         (includes o23 p22) (includes o23 p23) (waiting o24) (includes o24 p10)
         (includes o24 p17) (includes o24 p18) (waiting o25) (includes o25 p10)
         (includes o25 p13) (includes o25 p17))
        (:goal
         (and (shipped o1)
              (shipped o2)
              (shipped o3)
              (shipped o4)
              (shipped o5)
              (shipped o6)
              (shipped o7)
              (shipped o8)
              (shipped o9)
              (shipped o10)
              (shipped o11)
              (shipped o12)
              (shipped o13)
              (shipped o14)
              (shipped o15)
              (shipped o16)
              (shipped o17)
              (shipped o18)
              (shipped o19)
              (shipped o20)
              (shipped o21)
              (shipped o22)
              (shipped o23)
              (shipped o24)
              (shipped o25))))
