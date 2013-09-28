{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE DeriveDataTypeable        #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE ViewPatterns              #-}

import           Control.Newtype
import           Data.Active.Time
import qualified Data.Map                       as M
import           Data.Maybe                     (fromJust)
import           Data.Monoid.Coproduct          (untangle)
import           Data.Monoid.Split              (unsplit)
import           Data.Typeable
import           Diagrams.Backend.Cairo.CmdLine
import           Diagrams.Coordinates
import           Diagrams.Prelude
import           Diagrams.TwoD.Vector
import           Graphics.SVGFonts

type Anim = Animation Cairo R2
type Dia = Diagram Cairo R2

data TriLabel = TA | TB | TC
  deriving (Eq, Ord, Show, Typeable)

instance IsName TriLabel

theTri :: Dia
theTri
  = [ 2 *^ unit_Y
    , 5 *^ unitX
    ]
    # fromOffsets
    # closeTrail
    # (onLine . onLineSegments) (\[a,b,c] -> [b,c,a])
    # strokeTrail' with {vertexNames = [[TC, TA, TB]]}
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

movingTri :: Anim
movingTri = transform <$> ts <*~> theTri

fade :: (Functor f, HasStyle b) => f Double -> b -> f b
fade f dia = opacity <$> f <*~> dia

fadeIn :: Duration -> Dia -> Anim
fadeIn d = fade (sigma *>> fromDuration d)

fadeOut :: Duration -> Dia -> Anim
fadeOut d = fade (backwards sigma *>> fromDuration d)

inout
  = fade
    ( movie
      [ sigma *>> 0.5
      , dur 1 $> 1
      , backwards sigma *>> 0.5
      ]
    )

canvas :: Dia
canvas = square 15 # fc white # alignBL

triColumn :: Anim
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

parAL a1 a2 = ufree (anchorL 0 a1 `parA` anchorL 0 a2)

bigT = theTri # scale 2 # centerOn canvas

showTri
  = movie
    [ dur 1 $> bigT
    , inout
        ( mconcat
          [ edgeLabel TC TA "b" bigT
          , edgeLabel TA TB "c" bigT
          , edgeLabel TB TC "a" bigT
          ]
        )
      `parAL` (dur 10 $> bigT)
    , dur 1 $> bigT
    ]

edgeLabel :: TriLabel -> TriLabel -> String -> Dia -> Dia
edgeLabel v1 v2 label
  = withNames [v1,v2] $ \subs ->
      let [p1,p2] = map location subs
          pmid    = alerp p1 p2 0.5
          off     = perp (p2 .-. p1) # negateV # normalized
          labelPt = pmid .+^ off
      in
          const (text' 2 label # moveTo labelPt)

triToPosition :: Anim
triToPosition = keyframe (const True) bigT (triColumn # atLm) *>> 2

makeCopies :: Anim
makeCopies
  = movie
    [ dur 1                  $> theTri # translate (1 & 1)
    , triColumn *>> (1/2)
    , dur 1                  $> atRm triColumn
    ]

square1
  = replicate 4 theTri
  # zipWith named [0::Int ..]
  # zipWith transform (iterateN 4 (rotateAbout (3.5 & 3.5) (1/4 :: Turn)) mempty)
  # mconcat
  # centerOn canvas

copiesToSquare
  = keyframe (`elem` (map toName [0::Int .. 3])) (atRm triColumn) square1 *>> 4

showC
  = (dur 100 $> atRm copiesToSquare)
    `parAL`
    inout (text' 2 "c²" # centerOn canvas)

config2
  = (bl ||| juxtapose unitY bl tr) # fc green # centerOn canvas
  where bl = theTri # fc green # named (1::Int) # rotateBy (1/4) # alignL
          <> theTri # named (3::Int) # rotateBy (-1/4) # alignB
        tr = theTri # named (0::Int) # alignT
          <> theTri # named (2::Int) # rotateBy (1/2) # alignL

squareToConfig2
  = keyframe (`elem` (map toName [0::Int .. 3]))
      square1 config2 # fc green *>> 3

showAB
  = (dur 100 $> atRm squareToConfig2)
    `parAL`
    inout
      ( mconcat
        [ text' 2 "a²" # centerOn canvas # translate ((-2.5) & 2.5)
        , text' 2 "b²" # centerOn canvas # translate (1 & (-1))
        ]
      )

pythagoras :: Anim
pythagoras
  = movie
    [ showTri
    , triToPosition
    , makeCopies
    , copiesToSquare
    , dur 1 $> atRm copiesToSquare
    , showC
    , dur 1 $> atRm copiesToSquare
    , squareToConfig2
    , dur 1 $> atRm squareToConfig2
    , showAB
    , dur 1 $> atRm squareToConfig2
    ]

main :: IO ()
-- main = defaultMain config2
main = animMain ((<>) <$> pythagoras <*~> canvas)

------------------------------------------------------------

-- TODO: add this to std lib
instance VectorSpace Turn where
  type Scalar Turn = Double
  d *^ (Turn t)    = Turn (d*t)

interpolateT2 :: T2 -> T2 -> Double -> T2
interpolateT2 t1 t2 s =
  mconcat
  [ translation (lerp p p' s)
  , rotation (s *^ theta)
  , scalingY (lerp 1 (magnitude uy') s)
  , scalingX (lerp 1 (magnitude ux') s)
  , translation (negateV p)
  ]
  where
    tr :: (Transformable t, V t ~ R2) => t -> t
    tr  = transform (t2 <> inv t1)
    ux' = tr unitX
    uy' = tr unitY
    p   = transl t1
    p'  = transl t2
    theta :: Turn
    theta = smallest (angleBetween unitX ux')
    smallest (Turn phi)
      | phi >= 1/2 = Turn $ phi - 1
      | otherwise = Turn phi

keyframe :: (Semigroup m)
         => (Name -> Bool) -> QDiagram b R2 m -> QDiagram b R2 m -> QAnimation b R2 m
keyframe namePred d1 d2 = f <$> durValued (dur 1)
  where
    pairs = concat . map strength . filter (namePred . fst) . M.assocs
          $ M.intersectionWith zip (unpack $ subMap d1) (unpack $ subMap d2)
    strength (a,fb) = fmap ((,) a) fb
    f t = mconcat
        . map (\(n
                , ( x1@(Subdiagram _ (option mempty untangle -> (unsplit -> t1, _), _))
                  ,    (Subdiagram _ (option mempty untangle -> (unsplit -> t2, _), _))
                  )
                )
                ->

                getSub x1
                # transform (interpolateT2 t1 t2 (fromJust $ sigma `atTime` t))
--                # named n  How to keep the names around?
              )
        $ pairs

centerOn
  :: (Alignable b, HasOrigin b, Enveloped a, V a ~ R2, V b ~ R2) =>
     a -> b -> b
centerOn c d = d # centerXY # moveTo (center2D c)

text' :: Renderable (Path R2) b => Double -> String -> Diagram b R2
text' d s = (stroke $ textSVG' (TextOpts s lin2 INSIDE_H KERN False d d)) # fc black # lw 0
