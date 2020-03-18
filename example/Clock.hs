{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeFamilies              #-}

import Diagrams.Backend.Rasterific.CmdLine
import Diagrams.Prelude

clock :: Animation B V2 Double
clock = cut 24 $ stack
  [ flip rotateBy littleHand <$> -dur'
  , flip rotateBy bigHand    <$> -dur' / 12
  , pure (circle 1  # fc black # lwG 0)
  , pure (circle 11 # lwG 1.5 # lc slategray # fc lightsteelblue)
  , pure (square 25 # fc white)
  ]
  where
    bigHand    = (0 ^& (-1.5)) ~~ (0 ^& 7.5) # lwG 0.5
    littleHand = (0 ^& (-2))   ~~ (0 ^& 9.5) # lwG 0.2

main = animMain clock
