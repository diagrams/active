import ActiveDiagrams

dia = infO <> tl

infO = draw $ Active (I, r, O 2)  -- $
  where
    r = cat' unit_X with
      [ activeRect (-2) 2 red
      , fade 7 0 0.5 50
      ]
