{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

import           Control.Newtype
import           Data.Active.Time
import qualified Data.Map                       as M
import           Data.Maybe                     (fromJust)
import           Diagrams.Backend.Cairo.CmdLine
import           Diagrams.Coordinates
import           Diagrams.Prelude

keyframe :: ( OrderedField (Scalar v), HasLinearMap v, InnerSpace v
              , Semigroup m )
           => QDiagram b v m -> QDiagram b v m -> QAnimation b v m
keyframe d1 d2 = f <$> durValued (dur 1)
  where
    pairs = concat . map strength . M.assocs
          $ M.intersectionWith zip (unpack $ subMap d1) (unpack $ subMap d2)
    strength (a,fb) = fmap ((,) a) fb
    f t = mconcat
        . map (\(_,(x1,x2)) ->
                getSub x1
                # translate
                  ( lerp zeroV (location x2 .-. location x1)
                    (fromJust $ sigma `atTime` t)
                  )
              )
        $ pairs

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

accumulate :: (Deadline C O t a, Ord t, Monoid' a) => [Active Free O C t a] -> Active Free O C t a
accumulate = go mempty
  where
    go _ []     = emptyActive
    go m (a:as) = fmap (m <>) a <<>> go (m <> atRm a) as

swoopY :: Active Free C C Time T2
swoopY = translationY <$> ((sigma *>> 2) # scale 3)

ts :: Active Free C C Time T2
ts = closeL mempty $ accumulate (replicate 3 (uopenL swoopY))

movingTri :: Animation Cairo R2
movingTri = transform <$> ts <*~> theTri

fadeIn :: Duration -> Diagram Cairo R2 -> Animation Cairo R2
fadeIn d dia = opacity <$> sigma *>> fromDuration d <*~> dia

canvas :: Diagram Cairo R2
canvas = square 15 # fc white # alignBL

triColumn :: Animation Cairo R2
triColumn
  = movingTri
 <#> (atop <*> maybe mempty copies . lookupName "theTri")
  #  translate (r2 (1,1))
  where
    copies s
      = theTri
      # fc green
      # replicate (floor (snd (unp2 (location s)) / 3) + 1)
      # zipWith named [0::Int ..]
      # cat' unitY with {sep=1}

square1
  = theTri
  # iterateN 4 (rotateAbout (3.5 & 3.5) (1/4 :: Turn))
  # zipWith named [0::Int ..]
  # mconcat

scene1 :: Animation Cairo R2
scene1
  = movie
    [ dur 1                  $> theTri # translate (1 & 1)
    , triColumn *>> (1/2)
    , dur 1                  $> atRm triColumn
    ]

move1 = keyframe (atRm triColumn) square1 *>> 4

main :: IO ()
-- main = defaultMain square1
main = animMain ((<>) <$> move1 <*~> canvas)
