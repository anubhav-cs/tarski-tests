;; Generator input: seed=160882, locations=5, edges=5, seas=1, probabilities=[2, 3, 3, 4], goals=8, optimization=[5, 10], C=1.500000, V=1.500000
(define (problem psat-small-08-medium)
(:domain settlers)
(:objects
    p0 p1 p2 p3 p4 - place
    v0 v1 v2 v3 - vehicle
    sl11 sl12 sl13 sl14 sl15 - stone_level
    hl11 hl12 hl13 hl14 hl15 - housing_level
    cl11 cl12 cl13 cl14 cl15 cl16 cl17 cl18 cl19 cl20 cl21 cl22 cl23 cl24 cl25 cl26 cl27 cl28 cl29 cl30 cl31 cl32 cl33 cl34 cl35 - coal_level
    wl11 wl12 wl13 wl14 wl15 wl16 wl17 wl18 wl19 wl20 wl21 wl22 wl23 wl24 wl25 wl26 wl27 wl28 wl29 wl30 wl31 wl32 wl33 wl34 wl35 - wood_level
    tl11 tl12 tl13 tl14 tl15 tl16 tl17 tl18 tl19 tl20 tl21 tl22 tl23 tl24 tl25 tl26 tl27 tl28 tl29 tl30 tl31 tl32 tl33 tl34 tl35 - timber_level
)
(:init
    (CONNECTED-BY-LAND p0 p1)
    (CONNECTED-BY-LAND p0 p4)
    (CONNECTED-BY-LAND p1 p0)
    (CONNECTED-BY-LAND p1 p4)
    (CONNECTED-BY-LAND p2 p4)
    (CONNECTED-BY-LAND p3 p4)
    (CONNECTED-BY-LAND p4 p0)
    (CONNECTED-BY-LAND p4 p1)
    (CONNECTED-BY-LAND p4 p2)
    (CONNECTED-BY-LAND p4 p3)
    (CONNECTED-BY-SEA p1 p2)
    (CONNECTED-BY-SEA p2 p1)
    (BY-COAST p1)
    (BY-COAST p2)
    (housing p0 hl0)
    (housing p1 hl0)
    (housing p2 hl0)
    (housing p3 hl0)
    (housing p4 hl0)
    (available-stone p0 sl15)
    (available-atleast-stone p0 sl1)
    (available-atleast-stone p0 sl2)
    (available-atleast-stone p0 sl4)
    (available-timber p0 tl35)
    (available-atleast-timber p0 tl1)
    (available-atleast-timber p0 tl2)
    (available-atleast-timber p0 tl4)
    (available-ore p0 ol0)
    (available-wood p0 wl0)
    (available-coal p0 cl0)
    (available-iron p0 il0)
    (available-stone p1 sl0)
    (available-timber p1 tl0)
    (available-ore p1 ol9)
    (available-atleast-ore p1 ol1)
    (available-atleast-ore p1 ol2)
    (available-atleast-ore p1 ol4)
    (available-wood p1 wl0)
    (available-coal p1 cl0)
    (available-iron p1 il0)
    (available-stone p2 sl0)
    (available-timber p2 tl0)
    (available-ore p2 ol0)
    (available-wood p2 wl0)
    (available-coal p2 cl0)
    (available-iron p2 il0)
    (available-stone p3 sl0)
    (available-timber p3 tl0)
    (available-ore p3 ol0)
    (available-wood p3 wl0)
    (available-coal p3 cl0)
    (available-iron p3 il0)
    (available-stone p4 sl0)
    (available-timber p4 tl0)
    (available-ore p4 ol0)
    (available-wood p4 wl0)
    (available-coal p4 cl0)
    (available-iron p4 il0)
    (potential v0)
    (available-stone v0 sl0)
    (available-timber v0 tl0)
    (available-ore v0 ol0)
    (available-wood v0 wl0)
    (available-coal v0 cl0)
    (available-iron v0 il0)
    (potential v1)
    (available-stone v1 sl0)
    (available-timber v1 tl0)
    (available-ore v1 ol0)
    (available-wood v1 wl0)
    (available-coal v1 cl0)
    (available-iron v1 il0)
    (potential v2)
    (available-stone v2 sl0)
    (available-timber v2 tl0)
    (available-ore v2 ol0)
    (available-wood v2 wl0)
    (available-coal v2 cl0)
    (available-iron v2 il0)
    (potential v3)
    (available-stone v3 sl0)
    (available-timber v3 tl0)
    (available-ore v3 ol0)
    (available-wood v3 wl0)
    (available-coal v3 cl0)
    (available-iron v3 il0)
    (DIFF-SPACE spl1 spl1 spl0)
    (DIFF-SPACE spl2 spl1 spl1)
    (DIFF-SPACE spl3 spl1 spl2)
    (DIFF-SPACE spl4 spl1 spl3)
    (DIFF-SPACE spl5 spl1 spl4)
    (DIFF-SPACE spl6 spl1 spl5)
    (DIFF-SPACE spl7 spl1 spl6)
    (DIFF-SPACE spl8 spl1 spl7)
    (DIFF-SPACE spl9 spl1 spl8)
    (DIFF-SPACE spl10 spl1 spl9)
    (DIFF-SPACE spl2 spl2 spl0)
    (DIFF-SPACE spl3 spl2 spl1)
    (DIFF-SPACE spl4 spl2 spl2)
    (DIFF-SPACE spl5 spl2 spl3)
    (DIFF-SPACE spl6 spl2 spl4)
    (DIFF-SPACE spl7 spl2 spl5)
    (DIFF-SPACE spl8 spl2 spl6)
    (DIFF-SPACE spl9 spl2 spl7)
    (DIFF-SPACE spl10 spl2 spl8)
    (DIFF-HOUSING hl1 hl1 hl0)
    (DIFF-HOUSING hl2 hl1 hl1)
    (DIFF-HOUSING hl3 hl1 hl2)
    (DIFF-HOUSING hl4 hl1 hl3)
    (DIFF-HOUSING hl5 hl1 hl4)
    (DIFF-HOUSING hl6 hl1 hl5)
    (DIFF-HOUSING hl7 hl1 hl6)
    (DIFF-HOUSING hl8 hl1 hl7)
    (DIFF-HOUSING hl9 hl1 hl8)
    (DIFF-HOUSING hl10 hl1 hl9)
    (DIFF-HOUSING hl11 hl1 hl10)
    (DIFF-HOUSING hl12 hl1 hl11)
    (DIFF-HOUSING hl13 hl1 hl12)
    (DIFF-HOUSING hl14 hl1 hl13)
    (DIFF-HOUSING hl15 hl1 hl14)
    (DIFF-STONE sl1 sl1 sl0)
    (DIFF-STONE sl2 sl1 sl1)
    (DIFF-STONE sl3 sl1 sl2)
    (DIFF-STONE sl4 sl1 sl3)
    (DIFF-STONE sl5 sl1 sl4)
    (DIFF-STONE sl6 sl1 sl5)
    (DIFF-STONE sl7 sl1 sl6)
    (DIFF-STONE sl8 sl1 sl7)
    (DIFF-STONE sl9 sl1 sl8)
    (DIFF-STONE sl10 sl1 sl9)
    (DIFF-STONE sl11 sl1 sl10)
    (DIFF-STONE sl12 sl1 sl11)
    (DIFF-STONE sl13 sl1 sl12)
    (DIFF-STONE sl14 sl1 sl13)
    (DIFF-STONE sl15 sl1 sl14)
    (DIFF-STONE sl2 sl2 sl0)
    (DIFF-STONE sl3 sl2 sl1)
    (DIFF-STONE sl4 sl2 sl2)
    (DIFF-STONE sl5 sl2 sl3)
    (DIFF-STONE sl6 sl2 sl4)
    (DIFF-STONE sl7 sl2 sl5)
    (DIFF-STONE sl8 sl2 sl6)
    (DIFF-STONE sl9 sl2 sl7)
    (DIFF-STONE sl10 sl2 sl8)
    (DIFF-STONE sl11 sl2 sl9)
    (DIFF-STONE sl12 sl2 sl10)
    (DIFF-STONE sl13 sl2 sl11)
    (DIFF-STONE sl14 sl2 sl12)
    (DIFF-STONE sl15 sl2 sl13)
    (DIFF-STONE sl4 sl4 sl0)
    (DIFF-STONE sl5 sl4 sl1)
    (DIFF-STONE sl6 sl4 sl2)
    (DIFF-STONE sl7 sl4 sl3)
    (DIFF-STONE sl8 sl4 sl4)
    (DIFF-STONE sl9 sl4 sl5)
    (DIFF-STONE sl10 sl4 sl6)
    (DIFF-STONE sl11 sl4 sl7)
    (DIFF-STONE sl12 sl4 sl8)
    (DIFF-STONE sl13 sl4 sl9)
    (DIFF-STONE sl14 sl4 sl10)
    (DIFF-STONE sl15 sl4 sl11)
    (DIFF-TIMBER tl1 tl1 tl0)
    (DIFF-TIMBER tl2 tl1 tl1)
    (DIFF-TIMBER tl3 tl1 tl2)
    (DIFF-TIMBER tl4 tl1 tl3)
    (DIFF-TIMBER tl5 tl1 tl4)
    (DIFF-TIMBER tl6 tl1 tl5)
    (DIFF-TIMBER tl7 tl1 tl6)
    (DIFF-TIMBER tl8 tl1 tl7)
    (DIFF-TIMBER tl9 tl1 tl8)
    (DIFF-TIMBER tl10 tl1 tl9)
    (DIFF-TIMBER tl11 tl1 tl10)
    (DIFF-TIMBER tl12 tl1 tl11)
    (DIFF-TIMBER tl13 tl1 tl12)
    (DIFF-TIMBER tl14 tl1 tl13)
    (DIFF-TIMBER tl15 tl1 tl14)
    (DIFF-TIMBER tl16 tl1 tl15)
    (DIFF-TIMBER tl17 tl1 tl16)
    (DIFF-TIMBER tl18 tl1 tl17)
    (DIFF-TIMBER tl19 tl1 tl18)
    (DIFF-TIMBER tl20 tl1 tl19)
    (DIFF-TIMBER tl21 tl1 tl20)
    (DIFF-TIMBER tl22 tl1 tl21)
    (DIFF-TIMBER tl23 tl1 tl22)
    (DIFF-TIMBER tl24 tl1 tl23)
    (DIFF-TIMBER tl25 tl1 tl24)
    (DIFF-TIMBER tl26 tl1 tl25)
    (DIFF-TIMBER tl27 tl1 tl26)
    (DIFF-TIMBER tl28 tl1 tl27)
    (DIFF-TIMBER tl29 tl1 tl28)
    (DIFF-TIMBER tl30 tl1 tl29)
    (DIFF-TIMBER tl31 tl1 tl30)
    (DIFF-TIMBER tl32 tl1 tl31)
    (DIFF-TIMBER tl33 tl1 tl32)
    (DIFF-TIMBER tl34 tl1 tl33)
    (DIFF-TIMBER tl35 tl1 tl34)
    (DIFF-TIMBER tl2 tl2 tl0)
    (DIFF-TIMBER tl3 tl2 tl1)
    (DIFF-TIMBER tl4 tl2 tl2)
    (DIFF-TIMBER tl5 tl2 tl3)
    (DIFF-TIMBER tl6 tl2 tl4)
    (DIFF-TIMBER tl7 tl2 tl5)
    (DIFF-TIMBER tl8 tl2 tl6)
    (DIFF-TIMBER tl9 tl2 tl7)
    (DIFF-TIMBER tl10 tl2 tl8)
    (DIFF-TIMBER tl11 tl2 tl9)
    (DIFF-TIMBER tl12 tl2 tl10)
    (DIFF-TIMBER tl13 tl2 tl11)
    (DIFF-TIMBER tl14 tl2 tl12)
    (DIFF-TIMBER tl15 tl2 tl13)
    (DIFF-TIMBER tl16 tl2 tl14)
    (DIFF-TIMBER tl17 tl2 tl15)
    (DIFF-TIMBER tl18 tl2 tl16)
    (DIFF-TIMBER tl19 tl2 tl17)
    (DIFF-TIMBER tl20 tl2 tl18)
    (DIFF-TIMBER tl21 tl2 tl19)
    (DIFF-TIMBER tl22 tl2 tl20)
    (DIFF-TIMBER tl23 tl2 tl21)
    (DIFF-TIMBER tl24 tl2 tl22)
    (DIFF-TIMBER tl25 tl2 tl23)
    (DIFF-TIMBER tl26 tl2 tl24)
    (DIFF-TIMBER tl27 tl2 tl25)
    (DIFF-TIMBER tl28 tl2 tl26)
    (DIFF-TIMBER tl29 tl2 tl27)
    (DIFF-TIMBER tl30 tl2 tl28)
    (DIFF-TIMBER tl31 tl2 tl29)
    (DIFF-TIMBER tl32 tl2 tl30)
    (DIFF-TIMBER tl33 tl2 tl31)
    (DIFF-TIMBER tl34 tl2 tl32)
    (DIFF-TIMBER tl35 tl2 tl33)
    (DIFF-TIMBER tl4 tl4 tl0)
    (DIFF-TIMBER tl5 tl4 tl1)
    (DIFF-TIMBER tl6 tl4 tl2)
    (DIFF-TIMBER tl7 tl4 tl3)
    (DIFF-TIMBER tl8 tl4 tl4)
    (DIFF-TIMBER tl9 tl4 tl5)
    (DIFF-TIMBER tl10 tl4 tl6)
    (DIFF-TIMBER tl11 tl4 tl7)
    (DIFF-TIMBER tl12 tl4 tl8)
    (DIFF-TIMBER tl13 tl4 tl9)
    (DIFF-TIMBER tl14 tl4 tl10)
    (DIFF-TIMBER tl15 tl4 tl11)
    (DIFF-TIMBER tl16 tl4 tl12)
    (DIFF-TIMBER tl17 tl4 tl13)
    (DIFF-TIMBER tl18 tl4 tl14)
    (DIFF-TIMBER tl19 tl4 tl15)
    (DIFF-TIMBER tl20 tl4 tl16)
    (DIFF-TIMBER tl21 tl4 tl17)
    (DIFF-TIMBER tl22 tl4 tl18)
    (DIFF-TIMBER tl23 tl4 tl19)
    (DIFF-TIMBER tl24 tl4 tl20)
    (DIFF-TIMBER tl25 tl4 tl21)
    (DIFF-TIMBER tl26 tl4 tl22)
    (DIFF-TIMBER tl27 tl4 tl23)
    (DIFF-TIMBER tl28 tl4 tl24)
    (DIFF-TIMBER tl29 tl4 tl25)
    (DIFF-TIMBER tl30 tl4 tl26)
    (DIFF-TIMBER tl31 tl4 tl27)
    (DIFF-TIMBER tl32 tl4 tl28)
    (DIFF-TIMBER tl33 tl4 tl29)
    (DIFF-TIMBER tl34 tl4 tl30)
    (DIFF-TIMBER tl35 tl4 tl31)
    (DIFF-ORE ol1 ol1 ol0)
    (DIFF-ORE ol2 ol1 ol1)
    (DIFF-ORE ol3 ol1 ol2)
    (DIFF-ORE ol4 ol1 ol3)
    (DIFF-ORE ol5 ol1 ol4)
    (DIFF-ORE ol6 ol1 ol5)
    (DIFF-ORE ol7 ol1 ol6)
    (DIFF-ORE ol8 ol1 ol7)
    (DIFF-ORE ol9 ol1 ol8)
    (DIFF-ORE ol2 ol2 ol0)
    (DIFF-ORE ol3 ol2 ol1)
    (DIFF-ORE ol4 ol2 ol2)
    (DIFF-ORE ol5 ol2 ol3)
    (DIFF-ORE ol6 ol2 ol4)
    (DIFF-ORE ol7 ol2 ol5)
    (DIFF-ORE ol8 ol2 ol6)
    (DIFF-ORE ol9 ol2 ol7)
    (DIFF-ORE ol4 ol4 ol0)
    (DIFF-ORE ol5 ol4 ol1)
    (DIFF-ORE ol6 ol4 ol2)
    (DIFF-ORE ol7 ol4 ol3)
    (DIFF-ORE ol8 ol4 ol4)
    (DIFF-ORE ol9 ol4 ol5)
    (DIFF-WOOD wl1 wl1 wl0)
    (DIFF-WOOD wl2 wl1 wl1)
    (DIFF-WOOD wl3 wl1 wl2)
    (DIFF-WOOD wl4 wl1 wl3)
    (DIFF-WOOD wl5 wl1 wl4)
    (DIFF-WOOD wl6 wl1 wl5)
    (DIFF-WOOD wl7 wl1 wl6)
    (DIFF-WOOD wl8 wl1 wl7)
    (DIFF-WOOD wl9 wl1 wl8)
    (DIFF-WOOD wl10 wl1 wl9)
    (DIFF-WOOD wl11 wl1 wl10)
    (DIFF-WOOD wl12 wl1 wl11)
    (DIFF-WOOD wl13 wl1 wl12)
    (DIFF-WOOD wl14 wl1 wl13)
    (DIFF-WOOD wl15 wl1 wl14)
    (DIFF-WOOD wl16 wl1 wl15)
    (DIFF-WOOD wl17 wl1 wl16)
    (DIFF-WOOD wl18 wl1 wl17)
    (DIFF-WOOD wl19 wl1 wl18)
    (DIFF-WOOD wl20 wl1 wl19)
    (DIFF-WOOD wl21 wl1 wl20)
    (DIFF-WOOD wl22 wl1 wl21)
    (DIFF-WOOD wl23 wl1 wl22)
    (DIFF-WOOD wl24 wl1 wl23)
    (DIFF-WOOD wl25 wl1 wl24)
    (DIFF-WOOD wl26 wl1 wl25)
    (DIFF-WOOD wl27 wl1 wl26)
    (DIFF-WOOD wl28 wl1 wl27)
    (DIFF-WOOD wl29 wl1 wl28)
    (DIFF-WOOD wl30 wl1 wl29)
    (DIFF-WOOD wl31 wl1 wl30)
    (DIFF-WOOD wl32 wl1 wl31)
    (DIFF-WOOD wl33 wl1 wl32)
    (DIFF-WOOD wl34 wl1 wl33)
    (DIFF-WOOD wl35 wl1 wl34)
    (DIFF-WOOD wl2 wl2 wl0)
    (DIFF-WOOD wl3 wl2 wl1)
    (DIFF-WOOD wl4 wl2 wl2)
    (DIFF-WOOD wl5 wl2 wl3)
    (DIFF-WOOD wl6 wl2 wl4)
    (DIFF-WOOD wl7 wl2 wl5)
    (DIFF-WOOD wl8 wl2 wl6)
    (DIFF-WOOD wl9 wl2 wl7)
    (DIFF-WOOD wl10 wl2 wl8)
    (DIFF-WOOD wl11 wl2 wl9)
    (DIFF-WOOD wl12 wl2 wl10)
    (DIFF-WOOD wl13 wl2 wl11)
    (DIFF-WOOD wl14 wl2 wl12)
    (DIFF-WOOD wl15 wl2 wl13)
    (DIFF-WOOD wl16 wl2 wl14)
    (DIFF-WOOD wl17 wl2 wl15)
    (DIFF-WOOD wl18 wl2 wl16)
    (DIFF-WOOD wl19 wl2 wl17)
    (DIFF-WOOD wl20 wl2 wl18)
    (DIFF-WOOD wl21 wl2 wl19)
    (DIFF-WOOD wl22 wl2 wl20)
    (DIFF-WOOD wl23 wl2 wl21)
    (DIFF-WOOD wl24 wl2 wl22)
    (DIFF-WOOD wl25 wl2 wl23)
    (DIFF-WOOD wl26 wl2 wl24)
    (DIFF-WOOD wl27 wl2 wl25)
    (DIFF-WOOD wl28 wl2 wl26)
    (DIFF-WOOD wl29 wl2 wl27)
    (DIFF-WOOD wl30 wl2 wl28)
    (DIFF-WOOD wl31 wl2 wl29)
    (DIFF-WOOD wl32 wl2 wl30)
    (DIFF-WOOD wl33 wl2 wl31)
    (DIFF-WOOD wl34 wl2 wl32)
    (DIFF-WOOD wl35 wl2 wl33)
    (DIFF-WOOD wl4 wl4 wl0)
    (DIFF-WOOD wl5 wl4 wl1)
    (DIFF-WOOD wl6 wl4 wl2)
    (DIFF-WOOD wl7 wl4 wl3)
    (DIFF-WOOD wl8 wl4 wl4)
    (DIFF-WOOD wl9 wl4 wl5)
    (DIFF-WOOD wl10 wl4 wl6)
    (DIFF-WOOD wl11 wl4 wl7)
    (DIFF-WOOD wl12 wl4 wl8)
    (DIFF-WOOD wl13 wl4 wl9)
    (DIFF-WOOD wl14 wl4 wl10)
    (DIFF-WOOD wl15 wl4 wl11)
    (DIFF-WOOD wl16 wl4 wl12)
    (DIFF-WOOD wl17 wl4 wl13)
    (DIFF-WOOD wl18 wl4 wl14)
    (DIFF-WOOD wl19 wl4 wl15)
    (DIFF-WOOD wl20 wl4 wl16)
    (DIFF-WOOD wl21 wl4 wl17)
    (DIFF-WOOD wl22 wl4 wl18)
    (DIFF-WOOD wl23 wl4 wl19)
    (DIFF-WOOD wl24 wl4 wl20)
    (DIFF-WOOD wl25 wl4 wl21)
    (DIFF-WOOD wl26 wl4 wl22)
    (DIFF-WOOD wl27 wl4 wl23)
    (DIFF-WOOD wl28 wl4 wl24)
    (DIFF-WOOD wl29 wl4 wl25)
    (DIFF-WOOD wl30 wl4 wl26)
    (DIFF-WOOD wl31 wl4 wl27)
    (DIFF-WOOD wl32 wl4 wl28)
    (DIFF-WOOD wl33 wl4 wl29)
    (DIFF-WOOD wl34 wl4 wl30)
    (DIFF-WOOD wl35 wl4 wl31)
    (DIFF-COAL cl1 cl1 cl0)
    (DIFF-COAL cl2 cl1 cl1)
    (DIFF-COAL cl3 cl1 cl2)
    (DIFF-COAL cl4 cl1 cl3)
    (DIFF-COAL cl5 cl1 cl4)
    (DIFF-COAL cl6 cl1 cl5)
    (DIFF-COAL cl7 cl1 cl6)
    (DIFF-COAL cl8 cl1 cl7)
    (DIFF-COAL cl9 cl1 cl8)
    (DIFF-COAL cl10 cl1 cl9)
    (DIFF-COAL cl11 cl1 cl10)
    (DIFF-COAL cl12 cl1 cl11)
    (DIFF-COAL cl13 cl1 cl12)
    (DIFF-COAL cl14 cl1 cl13)
    (DIFF-COAL cl15 cl1 cl14)
    (DIFF-COAL cl16 cl1 cl15)
    (DIFF-COAL cl17 cl1 cl16)
    (DIFF-COAL cl18 cl1 cl17)
    (DIFF-COAL cl19 cl1 cl18)
    (DIFF-COAL cl20 cl1 cl19)
    (DIFF-COAL cl21 cl1 cl20)
    (DIFF-COAL cl22 cl1 cl21)
    (DIFF-COAL cl23 cl1 cl22)
    (DIFF-COAL cl24 cl1 cl23)
    (DIFF-COAL cl25 cl1 cl24)
    (DIFF-COAL cl26 cl1 cl25)
    (DIFF-COAL cl27 cl1 cl26)
    (DIFF-COAL cl28 cl1 cl27)
    (DIFF-COAL cl29 cl1 cl28)
    (DIFF-COAL cl30 cl1 cl29)
    (DIFF-COAL cl31 cl1 cl30)
    (DIFF-COAL cl32 cl1 cl31)
    (DIFF-COAL cl33 cl1 cl32)
    (DIFF-COAL cl34 cl1 cl33)
    (DIFF-COAL cl35 cl1 cl34)
    (DIFF-COAL cl2 cl2 cl0)
    (DIFF-COAL cl3 cl2 cl1)
    (DIFF-COAL cl4 cl2 cl2)
    (DIFF-COAL cl5 cl2 cl3)
    (DIFF-COAL cl6 cl2 cl4)
    (DIFF-COAL cl7 cl2 cl5)
    (DIFF-COAL cl8 cl2 cl6)
    (DIFF-COAL cl9 cl2 cl7)
    (DIFF-COAL cl10 cl2 cl8)
    (DIFF-COAL cl11 cl2 cl9)
    (DIFF-COAL cl12 cl2 cl10)
    (DIFF-COAL cl13 cl2 cl11)
    (DIFF-COAL cl14 cl2 cl12)
    (DIFF-COAL cl15 cl2 cl13)
    (DIFF-COAL cl16 cl2 cl14)
    (DIFF-COAL cl17 cl2 cl15)
    (DIFF-COAL cl18 cl2 cl16)
    (DIFF-COAL cl19 cl2 cl17)
    (DIFF-COAL cl20 cl2 cl18)
    (DIFF-COAL cl21 cl2 cl19)
    (DIFF-COAL cl22 cl2 cl20)
    (DIFF-COAL cl23 cl2 cl21)
    (DIFF-COAL cl24 cl2 cl22)
    (DIFF-COAL cl25 cl2 cl23)
    (DIFF-COAL cl26 cl2 cl24)
    (DIFF-COAL cl27 cl2 cl25)
    (DIFF-COAL cl28 cl2 cl26)
    (DIFF-COAL cl29 cl2 cl27)
    (DIFF-COAL cl30 cl2 cl28)
    (DIFF-COAL cl31 cl2 cl29)
    (DIFF-COAL cl32 cl2 cl30)
    (DIFF-COAL cl33 cl2 cl31)
    (DIFF-COAL cl34 cl2 cl32)
    (DIFF-COAL cl35 cl2 cl33)
    (DIFF-COAL cl4 cl4 cl0)
    (DIFF-COAL cl5 cl4 cl1)
    (DIFF-COAL cl6 cl4 cl2)
    (DIFF-COAL cl7 cl4 cl3)
    (DIFF-COAL cl8 cl4 cl4)
    (DIFF-COAL cl9 cl4 cl5)
    (DIFF-COAL cl10 cl4 cl6)
    (DIFF-COAL cl11 cl4 cl7)
    (DIFF-COAL cl12 cl4 cl8)
    (DIFF-COAL cl13 cl4 cl9)
    (DIFF-COAL cl14 cl4 cl10)
    (DIFF-COAL cl15 cl4 cl11)
    (DIFF-COAL cl16 cl4 cl12)
    (DIFF-COAL cl17 cl4 cl13)
    (DIFF-COAL cl18 cl4 cl14)
    (DIFF-COAL cl19 cl4 cl15)
    (DIFF-COAL cl20 cl4 cl16)
    (DIFF-COAL cl21 cl4 cl17)
    (DIFF-COAL cl22 cl4 cl18)
    (DIFF-COAL cl23 cl4 cl19)
    (DIFF-COAL cl24 cl4 cl20)
    (DIFF-COAL cl25 cl4 cl21)
    (DIFF-COAL cl26 cl4 cl22)
    (DIFF-COAL cl27 cl4 cl23)
    (DIFF-COAL cl28 cl4 cl24)
    (DIFF-COAL cl29 cl4 cl25)
    (DIFF-COAL cl30 cl4 cl26)
    (DIFF-COAL cl31 cl4 cl27)
    (DIFF-COAL cl32 cl4 cl28)
    (DIFF-COAL cl33 cl4 cl29)
    (DIFF-COAL cl34 cl4 cl30)
    (DIFF-COAL cl35 cl4 cl31)
    (DIFF-IRON il1 il1 il0)
    (DIFF-IRON il2 il1 il1)
    (DIFF-IRON il3 il1 il2)
    (DIFF-IRON il4 il1 il3)
    (DIFF-IRON il5 il1 il4)
    (DIFF-IRON il6 il1 il5)
    (DIFF-IRON il7 il1 il6)
    (DIFF-IRON il8 il1 il7)
    (DIFF-IRON il9 il1 il8)
    (DIFF-IRON il2 il2 il0)
    (DIFF-IRON il3 il2 il1)
    (DIFF-IRON il4 il2 il2)
    (DIFF-IRON il5 il2 il3)
    (DIFF-IRON il6 il2 il4)
    (DIFF-IRON il7 il2 il5)
    (DIFF-IRON il8 il2 il6)
    (DIFF-IRON il9 il2 il7)
    (DIFF-IRON il4 il4 il0)
    (DIFF-IRON il5 il4 il1)
    (DIFF-IRON il6 il4 il2)
    (DIFF-IRON il7 il4 il3)
    (DIFF-IRON il8 il4 il4)
    (DIFF-IRON il9 il4 il5)
    (ADD-ATLEAST-STONE sl0 sl1 sl1)
    (DEL-ATLEAST-STONE sl1 sl1 sl1)
    (ADD-ATLEAST-STONE sl0 sl2 sl1)
    (DEL-ATLEAST-STONE sl1 sl2 sl1)
    (DEL-ATLEAST-STONE sl2 sl2 sl1)
    (ADD-ATLEAST-STONE sl0 sl4 sl1)
    (DEL-ATLEAST-STONE sl1 sl4 sl1)
    (DEL-ATLEAST-STONE sl2 sl4 sl1)
    (DEL-ATLEAST-STONE sl3 sl4 sl1)
    (DEL-ATLEAST-STONE sl4 sl4 sl1)
    (ADD-ATLEAST-STONE sl1 sl1 sl2)
    (DEL-ATLEAST-STONE sl2 sl1 sl2)
    (ADD-ATLEAST-STONE sl0 sl2 sl2)
    (ADD-ATLEAST-STONE sl1 sl2 sl2)
    (DEL-ATLEAST-STONE sl2 sl2 sl2)
    (DEL-ATLEAST-STONE sl3 sl2 sl2)
    (ADD-ATLEAST-STONE sl0 sl4 sl2)
    (ADD-ATLEAST-STONE sl1 sl4 sl2)
    (DEL-ATLEAST-STONE sl2 sl4 sl2)
    (DEL-ATLEAST-STONE sl3 sl4 sl2)
    (DEL-ATLEAST-STONE sl4 sl4 sl2)
    (DEL-ATLEAST-STONE sl5 sl4 sl2)
    (ADD-ATLEAST-STONE sl3 sl1 sl4)
    (DEL-ATLEAST-STONE sl4 sl1 sl4)
    (ADD-ATLEAST-STONE sl2 sl2 sl4)
    (ADD-ATLEAST-STONE sl3 sl2 sl4)
    (DEL-ATLEAST-STONE sl4 sl2 sl4)
    (DEL-ATLEAST-STONE sl5 sl2 sl4)
    (ADD-ATLEAST-STONE sl0 sl4 sl4)
    (ADD-ATLEAST-STONE sl1 sl4 sl4)
    (ADD-ATLEAST-STONE sl2 sl4 sl4)
    (ADD-ATLEAST-STONE sl3 sl4 sl4)
    (DEL-ATLEAST-STONE sl4 sl4 sl4)
    (DEL-ATLEAST-STONE sl5 sl4 sl4)
    (DEL-ATLEAST-STONE sl6 sl4 sl4)
    (DEL-ATLEAST-STONE sl7 sl4 sl4)
    (ADD-ATLEAST-TIMBER tl0 tl1 tl1)
    (DEL-ATLEAST-TIMBER tl1 tl1 tl1)
    (ADD-ATLEAST-TIMBER tl0 tl2 tl1)
    (DEL-ATLEAST-TIMBER tl1 tl2 tl1)
    (DEL-ATLEAST-TIMBER tl2 tl2 tl1)
    (ADD-ATLEAST-TIMBER tl0 tl4 tl1)
    (DEL-ATLEAST-TIMBER tl1 tl4 tl1)
    (DEL-ATLEAST-TIMBER tl2 tl4 tl1)
    (DEL-ATLEAST-TIMBER tl3 tl4 tl1)
    (DEL-ATLEAST-TIMBER tl4 tl4 tl1)
    (ADD-ATLEAST-TIMBER tl1 tl1 tl2)
    (DEL-ATLEAST-TIMBER tl2 tl1 tl2)
    (ADD-ATLEAST-TIMBER tl0 tl2 tl2)
    (ADD-ATLEAST-TIMBER tl1 tl2 tl2)
    (DEL-ATLEAST-TIMBER tl2 tl2 tl2)
    (DEL-ATLEAST-TIMBER tl3 tl2 tl2)
    (ADD-ATLEAST-TIMBER tl0 tl4 tl2)
    (ADD-ATLEAST-TIMBER tl1 tl4 tl2)
    (DEL-ATLEAST-TIMBER tl2 tl4 tl2)
    (DEL-ATLEAST-TIMBER tl3 tl4 tl2)
    (DEL-ATLEAST-TIMBER tl4 tl4 tl2)
    (DEL-ATLEAST-TIMBER tl5 tl4 tl2)
    (ADD-ATLEAST-TIMBER tl3 tl1 tl4)
    (DEL-ATLEAST-TIMBER tl4 tl1 tl4)
    (ADD-ATLEAST-TIMBER tl2 tl2 tl4)
    (ADD-ATLEAST-TIMBER tl3 tl2 tl4)
    (DEL-ATLEAST-TIMBER tl4 tl2 tl4)
    (DEL-ATLEAST-TIMBER tl5 tl2 tl4)
    (ADD-ATLEAST-TIMBER tl0 tl4 tl4)
    (ADD-ATLEAST-TIMBER tl1 tl4 tl4)
    (ADD-ATLEAST-TIMBER tl2 tl4 tl4)
    (ADD-ATLEAST-TIMBER tl3 tl4 tl4)
    (DEL-ATLEAST-TIMBER tl4 tl4 tl4)
    (DEL-ATLEAST-TIMBER tl5 tl4 tl4)
    (DEL-ATLEAST-TIMBER tl6 tl4 tl4)
    (DEL-ATLEAST-TIMBER tl7 tl4 tl4)
    (ADD-ATLEAST-ORE ol0 ol1 ol1)
    (DEL-ATLEAST-ORE ol1 ol1 ol1)
    (ADD-ATLEAST-ORE ol0 ol2 ol1)
    (DEL-ATLEAST-ORE ol1 ol2 ol1)
    (DEL-ATLEAST-ORE ol2 ol2 ol1)
    (ADD-ATLEAST-ORE ol0 ol4 ol1)
    (DEL-ATLEAST-ORE ol1 ol4 ol1)
    (DEL-ATLEAST-ORE ol2 ol4 ol1)
    (DEL-ATLEAST-ORE ol3 ol4 ol1)
    (DEL-ATLEAST-ORE ol4 ol4 ol1)
    (ADD-ATLEAST-ORE ol1 ol1 ol2)
    (DEL-ATLEAST-ORE ol2 ol1 ol2)
    (ADD-ATLEAST-ORE ol0 ol2 ol2)
    (ADD-ATLEAST-ORE ol1 ol2 ol2)
    (DEL-ATLEAST-ORE ol2 ol2 ol2)
    (DEL-ATLEAST-ORE ol3 ol2 ol2)
    (ADD-ATLEAST-ORE ol0 ol4 ol2)
    (ADD-ATLEAST-ORE ol1 ol4 ol2)
    (DEL-ATLEAST-ORE ol2 ol4 ol2)
    (DEL-ATLEAST-ORE ol3 ol4 ol2)
    (DEL-ATLEAST-ORE ol4 ol4 ol2)
    (DEL-ATLEAST-ORE ol5 ol4 ol2)
    (ADD-ATLEAST-ORE ol3 ol1 ol4)
    (DEL-ATLEAST-ORE ol4 ol1 ol4)
    (ADD-ATLEAST-ORE ol2 ol2 ol4)
    (ADD-ATLEAST-ORE ol3 ol2 ol4)
    (DEL-ATLEAST-ORE ol4 ol2 ol4)
    (DEL-ATLEAST-ORE ol5 ol2 ol4)
    (ADD-ATLEAST-ORE ol0 ol4 ol4)
    (ADD-ATLEAST-ORE ol1 ol4 ol4)
    (ADD-ATLEAST-ORE ol2 ol4 ol4)
    (ADD-ATLEAST-ORE ol3 ol4 ol4)
    (DEL-ATLEAST-ORE ol4 ol4 ol4)
    (DEL-ATLEAST-ORE ol5 ol4 ol4)
    (DEL-ATLEAST-ORE ol6 ol4 ol4)
    (DEL-ATLEAST-ORE ol7 ol4 ol4)
    (ADD-ATLEAST-WOOD wl0 wl1 wl1)
    (DEL-ATLEAST-WOOD wl1 wl1 wl1)
    (ADD-ATLEAST-WOOD wl0 wl2 wl1)
    (DEL-ATLEAST-WOOD wl1 wl2 wl1)
    (DEL-ATLEAST-WOOD wl2 wl2 wl1)
    (ADD-ATLEAST-WOOD wl0 wl4 wl1)
    (DEL-ATLEAST-WOOD wl1 wl4 wl1)
    (DEL-ATLEAST-WOOD wl2 wl4 wl1)
    (DEL-ATLEAST-WOOD wl3 wl4 wl1)
    (DEL-ATLEAST-WOOD wl4 wl4 wl1)
    (ADD-ATLEAST-WOOD wl1 wl1 wl2)
    (DEL-ATLEAST-WOOD wl2 wl1 wl2)
    (ADD-ATLEAST-WOOD wl0 wl2 wl2)
    (ADD-ATLEAST-WOOD wl1 wl2 wl2)
    (DEL-ATLEAST-WOOD wl2 wl2 wl2)
    (DEL-ATLEAST-WOOD wl3 wl2 wl2)
    (ADD-ATLEAST-WOOD wl0 wl4 wl2)
    (ADD-ATLEAST-WOOD wl1 wl4 wl2)
    (DEL-ATLEAST-WOOD wl2 wl4 wl2)
    (DEL-ATLEAST-WOOD wl3 wl4 wl2)
    (DEL-ATLEAST-WOOD wl4 wl4 wl2)
    (DEL-ATLEAST-WOOD wl5 wl4 wl2)
    (ADD-ATLEAST-WOOD wl3 wl1 wl4)
    (DEL-ATLEAST-WOOD wl4 wl1 wl4)
    (ADD-ATLEAST-WOOD wl2 wl2 wl4)
    (ADD-ATLEAST-WOOD wl3 wl2 wl4)
    (DEL-ATLEAST-WOOD wl4 wl2 wl4)
    (DEL-ATLEAST-WOOD wl5 wl2 wl4)
    (ADD-ATLEAST-WOOD wl0 wl4 wl4)
    (ADD-ATLEAST-WOOD wl1 wl4 wl4)
    (ADD-ATLEAST-WOOD wl2 wl4 wl4)
    (ADD-ATLEAST-WOOD wl3 wl4 wl4)
    (DEL-ATLEAST-WOOD wl4 wl4 wl4)
    (DEL-ATLEAST-WOOD wl5 wl4 wl4)
    (DEL-ATLEAST-WOOD wl6 wl4 wl4)
    (DEL-ATLEAST-WOOD wl7 wl4 wl4)
    (ADD-ATLEAST-COAL cl0 cl1 cl1)
    (DEL-ATLEAST-COAL cl1 cl1 cl1)
    (ADD-ATLEAST-COAL cl0 cl2 cl1)
    (DEL-ATLEAST-COAL cl1 cl2 cl1)
    (DEL-ATLEAST-COAL cl2 cl2 cl1)
    (ADD-ATLEAST-COAL cl0 cl4 cl1)
    (DEL-ATLEAST-COAL cl1 cl4 cl1)
    (DEL-ATLEAST-COAL cl2 cl4 cl1)
    (DEL-ATLEAST-COAL cl3 cl4 cl1)
    (DEL-ATLEAST-COAL cl4 cl4 cl1)
    (ADD-ATLEAST-COAL cl1 cl1 cl2)
    (DEL-ATLEAST-COAL cl2 cl1 cl2)
    (ADD-ATLEAST-COAL cl0 cl2 cl2)
    (ADD-ATLEAST-COAL cl1 cl2 cl2)
    (DEL-ATLEAST-COAL cl2 cl2 cl2)
    (DEL-ATLEAST-COAL cl3 cl2 cl2)
    (ADD-ATLEAST-COAL cl0 cl4 cl2)
    (ADD-ATLEAST-COAL cl1 cl4 cl2)
    (DEL-ATLEAST-COAL cl2 cl4 cl2)
    (DEL-ATLEAST-COAL cl3 cl4 cl2)
    (DEL-ATLEAST-COAL cl4 cl4 cl2)
    (DEL-ATLEAST-COAL cl5 cl4 cl2)
    (ADD-ATLEAST-COAL cl3 cl1 cl4)
    (DEL-ATLEAST-COAL cl4 cl1 cl4)
    (ADD-ATLEAST-COAL cl2 cl2 cl4)
    (ADD-ATLEAST-COAL cl3 cl2 cl4)
    (DEL-ATLEAST-COAL cl4 cl2 cl4)
    (DEL-ATLEAST-COAL cl5 cl2 cl4)
    (ADD-ATLEAST-COAL cl0 cl4 cl4)
    (ADD-ATLEAST-COAL cl1 cl4 cl4)
    (ADD-ATLEAST-COAL cl2 cl4 cl4)
    (ADD-ATLEAST-COAL cl3 cl4 cl4)
    (DEL-ATLEAST-COAL cl4 cl4 cl4)
    (DEL-ATLEAST-COAL cl5 cl4 cl4)
    (DEL-ATLEAST-COAL cl6 cl4 cl4)
    (DEL-ATLEAST-COAL cl7 cl4 cl4)
    (ADD-ATLEAST-IRON il0 il1 il1)
    (DEL-ATLEAST-IRON il1 il1 il1)
    (ADD-ATLEAST-IRON il0 il2 il1)
    (DEL-ATLEAST-IRON il1 il2 il1)
    (DEL-ATLEAST-IRON il2 il2 il1)
    (ADD-ATLEAST-IRON il0 il4 il1)
    (DEL-ATLEAST-IRON il1 il4 il1)
    (DEL-ATLEAST-IRON il2 il4 il1)
    (DEL-ATLEAST-IRON il3 il4 il1)
    (DEL-ATLEAST-IRON il4 il4 il1)
    (ADD-ATLEAST-IRON il1 il1 il2)
    (DEL-ATLEAST-IRON il2 il1 il2)
    (ADD-ATLEAST-IRON il0 il2 il2)
    (ADD-ATLEAST-IRON il1 il2 il2)
    (DEL-ATLEAST-IRON il2 il2 il2)
    (DEL-ATLEAST-IRON il3 il2 il2)
    (ADD-ATLEAST-IRON il0 il4 il2)
    (ADD-ATLEAST-IRON il1 il4 il2)
    (DEL-ATLEAST-IRON il2 il4 il2)
    (DEL-ATLEAST-IRON il3 il4 il2)
    (DEL-ATLEAST-IRON il4 il4 il2)
    (DEL-ATLEAST-IRON il5 il4 il2)
    (ADD-ATLEAST-IRON il3 il1 il4)
    (DEL-ATLEAST-IRON il4 il1 il4)
    (ADD-ATLEAST-IRON il2 il2 il4)
    (ADD-ATLEAST-IRON il3 il2 il4)
    (DEL-ATLEAST-IRON il4 il2 il4)
    (DEL-ATLEAST-IRON il5 il2 il4)
    (ADD-ATLEAST-IRON il0 il4 il4)
    (ADD-ATLEAST-IRON il1 il4 il4)
    (ADD-ATLEAST-IRON il2 il4 il4)
    (ADD-ATLEAST-IRON il3 il4 il4)
    (DEL-ATLEAST-IRON il4 il4 il4)
    (DEL-ATLEAST-IRON il5 il4 il4)
    (DEL-ATLEAST-IRON il6 il4 il4)
    (DEL-ATLEAST-IRON il7 il4 il4)
)
(:goal
(and
    (has-ironworks p2)
    (has-ironworks p0)
    (connected-by-rail p2 p4)
    (connected-by-rail p1 p0)
    (connected-by-rail p1 p4)
    (has-ironworks p1)
    (has-sawmill p2)
    (housing p4 hl1)
)
)
(:metric minimize (total-cost))
)