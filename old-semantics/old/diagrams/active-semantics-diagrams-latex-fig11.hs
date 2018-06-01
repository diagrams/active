import ActiveDiagrams

dia = vcat' with {sep = 1}
  [ a1                <> tl
  , text' "~"
  , a1 # translateX 4 <> tl
  ]
