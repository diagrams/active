import ActiveDiagrams
as :: Diagram Cairo R2
as = cat' unitY with {sep = 0.5}
   [ draw (active' (-6) 3 (activeRect (-6) 3 red <> activeRect (-6) 3 blue))
   , activeD (-6) 3 blue
   , activeD (-6) 3 red
   ]

dia = as <> tl
