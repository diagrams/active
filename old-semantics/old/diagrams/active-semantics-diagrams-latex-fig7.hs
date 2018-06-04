import ActiveDiagrams

dia = result # centerX <> phantom tl

result = atop (text' "?" # scale 0.7 # translateX 1). draw . active' (-3) 8 $ hcat
  [ activeRect (-3) 1 red
  , vrule 3 # lw 0.1 # dashing [0.1,0.1] 0 # lc grey
  , activeRect 1 8 blue
  ]
