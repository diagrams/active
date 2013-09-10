{-# LANGUAGE NoMonomorphismRestriction #-}

import           Diagrams.Backend.Cairo.CmdLine
import           Diagrams.Prelude

theTri
  = [ 2 *^ unit_Y
    , 5 *^ unitX
    ]
    # fromOffsets
    # closeTrail
    # (onLine . onLineSegments) (\[a,b,c] -> [b,c,a])
    # strokeTrail
    # fc blue

movingTri = translateY <$> (fromTime <$> timeValued (0 ... 3)) `appA` pureA theTri

canvas = pureA (square 18 # fc white)

($>) = flip (<$)

a = movingTri `parA` ( (0 ... 3) $> theTri )

main = animMain (ufree a)
