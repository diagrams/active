import ActiveDiagrams

dia = vcat' with {sep = 1}
      [ activeDR (-3) 1 red  <> tl
      , seqR
      , activeDR (-4) 3 blue <> tl
      , text' "="
      , vcat
        [ mconcat
          [ ( ((-4) & 0)  ~~  (0.5 & 0) ) # dashing [0.2,0.2] 0
          , triangle 0.5 # rotateBy (-1/4) # alignR # translateX 1 # lw 0
          ]
          # lw 0.2 # lc blue # fc blue # opacity 0.5
        , result
        ]
      ]

result = (draw $ Active (C (-3), r, O 8)) <> tl  -- $
  where
    r = hcat [ activeRect (-3) 1 red, activeRect 1 8 blue ]
