{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

import           Diagrams.Backend.Cairo.CmdLine
import           Diagrams.Prelude

theTri :: Diagram Cairo R2
theTri
  = [ 2 *^ unit_Y
    , 5 *^ unitX
    ]
    # fromOffsets
    # closeTrail
    # (onLine . onLineSegments) (\[a,b,c] -> [b,c,a])
    # strokeTrail
    # lw 0.05
    # lineJoin LineJoinRound
    # named "theTri"

movingTri :: Animation Cairo R2
movingTri = translateY <$> durValued (dur 9) <*~> theTri

canvas :: Diagram Cairo R2
canvas = square 15 # fc white # alignBL

triColumn :: Animation Cairo R2
triColumn
  = movingTri
 <#> (atop <*> maybe mempty copies . lookupName "theTri")
  #  translate (r2 (1,1))
  where
    copies s = cat' unitY with {sep=1}
             $ replicate (floor (snd (unp2 (location s)) / 3) + 1) theTri

scene1 :: Animation Cairo R2
scene1
  = movie
    [ dur 1                  $> (theTri # translate (r2 (1,1)))
    , triColumn *>> (1/2)
    , dur 1                  $> atRm triColumn
    ]

main :: IO ()
main = animMain ((<>) <$> scene1 <*~> canvas)
