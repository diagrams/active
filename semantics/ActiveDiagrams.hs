{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances  #-}

module ActiveDiagrams where

import           Diagrams.Backend.Cairo
import           Diagrams.Coordinates
import           Diagrams.Prelude

timeline t1 t2 =
       circle 0.2 # fc black
    <> (t1 & 0) ~~ (t2 & 0) # dashing [0.1,0.1] 0
    <> arrowhead            # moveTo (t2 & 0)
    <> arrowhead # reflectX # moveTo (t1 & 0)
  where
    arrowhead = fromOffsets [(1&(-1)), ((-1)&(-1))]
              # scale 0.3
              # scaleY 0.5
              # lineCap LineCapRound
              # centerY
              # alignR

newtype XActive = XActive (Maybe Double, Diagram Cairo R2, Maybe Double)

class Drawable d where
  draw :: d -> Diagram Cairo R2

instance Drawable XActive where
  draw (XActive (s, d, e)) = drawLine s <> drawLine e <> d
    where
      drawLine Nothing  = mempty
      drawLine (Just x) = vrule 3 # lw 0.1 # translateX x

xactive s e c = XActive
  ( Just s
  , rect (e - s) 2 # lw 0 # fcA (c `withOpacity` 0.5) # alignL # translateX s
  , Just e
  )

-- main = defaultMain (timeline (-10) 10)
