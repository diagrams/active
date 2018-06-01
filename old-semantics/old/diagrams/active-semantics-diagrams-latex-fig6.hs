import ActiveDiagrams

dia = vcat' with {sep = 1}
      [ hcat' with {sep = 2}
        [ activeD (-3) 1 red
        , seqR
        , activeD (-4) 3 blue
        ] # centerX
      , text' "="
      , result # centerX <> phantom tl
      ]

result = (draw $ active' (-3) 8 (activeRect (-3) 1 red ||| activeRect 1 8 blue))
