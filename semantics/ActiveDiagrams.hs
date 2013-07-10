{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances  #-}

module ActiveDiagrams where

import           Diagrams.Backend.Cairo
import           Diagrams.Coordinates
import           Diagrams.Prelude
import           Graphics.SVGFonts.ReadFont

timeline :: Double -> Double -> Diagram Cairo R2
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

data End = I
         | C Double
         | O Double

newtype XActive = XActive (End, Diagram Cairo R2, End)

class Drawable d where
  draw :: d -> Diagram Cairo R2

instance Drawable XActive where
  draw (XActive (s, d, e)) = drawLine s <> drawLine e <> d
    where
      drawLine I     = mempty
      drawLine (C x) = vrule 3 # lw 0.1 # translateX x
      drawLine (O x) = vrule 3 # lw 0.1 # dashing [0.2,0.2] 0 # lc grey # translateX x  -- XXX fix me

xactive' :: Double -> Double -> Diagram Cairo R2 -> XActive
xactive' s e d = XActive
  ( C s
  , d
  , C e
  )

xactive :: Double -> Double -> Colour Double -> XActive
xactive s e c = xactive' s e (xactiveRect s e c)

xactiveRect :: Double -> Double -> Colour Double -> Diagram Cairo R2
xactiveRect s e c
  = rect (e - s) 2 # lw 0 # fcA (c `withOpacity` 0.5) # alignL # translateX s

xactiveD :: Double -> Double -> Colour Double -> Diagram Cairo R2
xactiveD s e c = draw (xactive s e c)

a1, a2, a12 :: Diagram Cairo R2
a1 = xactiveD (-6) 3 red
a2 = xactiveD (-1) 5 blue
a12 = draw (xactive' (-1) 3 (xactiveRect (-1) 3 red <> xactiveRect (-1) 3 blue))

a1R :: Diagram Cairo R2
a1R = draw $ XActive (C (-6), a1RRect, I)
  where
    a1RRect = xactiveRect (-6) 3 red
          ||| fade 7 0.5 0 50

-- Hack since diagrams doesn't yet support gradients.  This doesn't even look right.
fade len o1 o2 n =
  hcat (map (\o -> let c = red `withOpacity` o in rect (len / n) 2 # lw 0 # fcA c)
            [o1, o1 + (o2 - o1) / (n - 1) .. o2]
       )

tl :: Diagram Cairo R2
tl = timeline (-10) 10

text' :: Renderable (Path R2) b => String -> Diagram b R2
text' s = (stroke $ textSVG' (TextOpts s lin2 INSIDE_H KERN False 4 4)) # fc black # lw 0
