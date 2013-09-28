{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

import           Data.Active.Era
import           Diagrams.Backend.Cairo.CmdLine
import           Diagrams.Prelude

pts = map (\x -> p2 (x, sin x)) [-5..5]

spline :: Located (Trail R2)
spline = cubicSpline False pts

along :: ( IsEraType f, EraConstraints f C C
         , Parametric p, Codomain p ~ Point (V a), Fractional (Scalar (V p))
         , HasOrigin a
         )
      => p -> a -> Active f C C Time a
along t x = (moveTo . (t `atParam`)) <$> durValued (dur 1) <*~> x

canvas = square 14 # fc white

main = animMain
  (     atop
   <$>  ((circle 1 :: Diagram Cairo R2) # along spline) *>> 5
   <*~> canvas
  )
