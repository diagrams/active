{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

import           Control.Applicative
import           Data.Maybe
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
    # fc blue
    # named "theTri"

movingTri :: Active Fixed C C Time (Diagram Cairo R2)
movingTri = translateY <$> (fromTime <$> timeValued (0 ... 9)) `appA` pureA theTri

canvas :: Diagram Cairo R2
canvas = square 15 # fc white # alignBL

triColumn :: Active Fixed C C Time (Diagram Cairo R2)
triColumn = ( (\d -> d <> case lookupName "theTri" d of
                            Just s  -> cat' unitY with {sep=1}
                                      $ replicate (floor (snd (unp2 (location s)) / 3) + 1) theTri
                            Nothing -> mempty
              )
              <$> movingTri
            )
            # translate (r2 (1,1))

($>) :: Functor f => f b -> a -> f a
($>) = flip (<$)

scene1
  = movie
    [ dur 1 $> (theTri # translate (r2 (1,1)))
    , ufree triColumn
    , ufree $ snd <$> ((0...1) `pairA` fromJust (snapshot 9 triColumn))
    ]

main :: IO ()
main = animMain ((<>canvas) <$> scene1)
