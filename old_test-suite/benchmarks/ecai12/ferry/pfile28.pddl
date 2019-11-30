


(define (problem ferry-l4-c3)
(:domain ferry)
(:objects l0 l1 l2 l3 
          c0 c1 c2 
)
(:init
(location l0)
(location l1)
(location l2)
(location l3)
(car c0)
(car c1)
(car c2)
(not-eq l0 l1)
(not-eq l1 l0)
(not-eq l0 l2)
(not-eq l2 l0)
(not-eq l0 l3)
(not-eq l3 l0)
(not-eq l1 l2)
(not-eq l2 l1)
(not-eq l1 l3)
(not-eq l3 l1)
(not-eq l2 l3)
(not-eq l3 l2)
(empty-ferry)
(at c0 l3)
(at c1 l2)
(at c2 l0)
(at-ferry l2)
)
(:goal
(and
(at c0 l1)
(at c1 l2)
(at c2 l0)
)
)
)

