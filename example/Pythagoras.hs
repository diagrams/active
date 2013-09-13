{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

import           Control.Applicative
import           Control.Lens                   ((^.))
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
    # lw 0.05
    # lineJoin LineJoinRound
    # named "theTri"

(<#>) :: Functor f => f a -> (a -> b) -> f b
(<#>) = flip fmap

infixl 4 <*~>

(<*~>) :: Functor f => f (a -> b) -> a -> f b
f <*~> a = fmap ($a) f

movingTri :: Animation Cairo R2
movingTri = (translateY . fromDuration) <$> durValued (dur 9) <*~> theTri

canvas :: Diagram Cairo R2
canvas = square 15 # fc white # alignBL

triColumn :: Animation Cairo R2
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

scene1 :: Animation Cairo R2
scene1
  = movie
    [ dur 1 $> (theTri # translate (r2 (1,1)))
    , triColumn *>> (1/2)
    , dur 1 $> atRm triColumn
    ]

main :: IO ()
main = animMain ((<>canvas) <$> scene1)
