{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE UndecidableInstances      #-}

module ActiveDiagrams where

import           Diagrams.Backend.Cairo
import           Diagrams.Coordinates
import           Diagrams.Prelude           hiding (Active)
import           Graphics.SVGFonts.ReadFont

timeline :: Double -> Double -> Diagram Cairo R2
timeline t1 t2 =
       circle 0.2 # fc black
    <> arrowAt origin ((t2 - t1) *^ unitX) # centerX

wiggleTrail :: Trail R2
wiggleTrail = cubicSpline False (zipWith (curry p2) [0..] [1,3,4,2,-3,0,6,2,-1,-0.5,-1,0])

wiggle :: Double -> Double -> Diagram Cairo R2
wiggle e1 e2 = arrowBetween' with { arrowShaft = wiggleTrail }
                 (p2 (e1,0)) (p2 (e2,0))

------------------------------------------------------------
-- Old stuff


data End = EI
         | EC Double
         | EO Double

newtype Active = Active (End, Diagram Cairo R2, End)

class Drawable d where
  draw :: d -> Diagram Cairo R2

instance Drawable Active where
  draw (Active (s, d, e)) = drawLine s <> drawLine e <> d
    where
      drawLine EI     = mempty
      drawLine (EC x) = vrule 3 # lw 0.1 # translateX x
      drawLine (EO x) = vrule 3 # lw 0.1 # dashing [0.2,0.2] 0 # lc grey # translateX x  -- XXX fix me

active' :: Double -> Double -> Diagram Cairo R2 -> Active
active' s e d = Active
  ( EC s
  , d
  , EC e
  )

active :: Double -> Double -> Colour Double -> Active
active s e c = active' s e (activeRect s e c)

activeRect :: Double -> Double -> Colour Double -> Diagram Cairo R2
activeRect s e c
  = rect (e - s) 2 # lw 0 # fcA (c `withOpacity` 0.5) # alignL # translateX s

activeD :: Double -> Double -> Colour Double -> Diagram Cairo R2
activeD s e c = draw (active s e c)

activeD' :: (Double -> End) -> (Double -> End) -> Double -> Double -> [Colour Double] -> Diagram Cairo R2
activeD' l r s e cs = draw $ Active (l s, mconcat . map (activeRect s e) $ cs, r e)

activeDR :: Double -> Double -> Colour Double -> Diagram Cairo R2
activeDR s e c = activeD' EC EO s e [c]

a1, a2, a12 :: Diagram Cairo R2
a1 = activeD (-6) 3 red
a2 = activeD (-1) 5 blue
a12 = draw (active' (-1) 3 (activeRect (-1) 3 red <> activeRect (-1) 3 blue))

a1R :: Diagram Cairo R2
a1R = draw $ Active (EC (-6), a1RRect, EI)
  where
    a1RRect = activeRect (-6) 3 red
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

seqR = triangle 1 # rotateBy (-1/4) # lw 0.15
