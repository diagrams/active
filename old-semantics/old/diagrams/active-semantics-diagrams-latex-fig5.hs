import ActiveDiagrams
dia = (cat' unitY with [a1X,a2X]) <> tl

a2X = mconcat
  [ a2
  , text' "?" # scale 0.7 # translateX (-3.5)
  , activeRect (-6) (-1) (blend 0.7 blue white)
  ]

a1X = mconcat
  [ a1
  , text' "?" # scale 0.7 # translateX 4
  , activeRect 3 5 (blend 0.5 red white)
  ]
