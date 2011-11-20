{-# LANGUAGE DeriveFunctor
           , GeneralizedNewtypeDeriving
  #-}
module Data.Active where

import Data.Semigroup
import Data.Functor.Apply
import Control.Applicative

type Time = Rational

type UI = Double

newtype Duration = Duration (Min Time, Max Time)
  deriving (Semigroup)

mkDuration :: Time -> Time -> Duration
mkDuration begin end = Duration (Min begin, Max end)

getStart :: Duration -> Time
getStart (Duration (Min t, _)) = t

getEnd :: Duration -> Time
getEnd (Duration (_, Max t)) = t

elapsed :: Duration -> Time
elapsed = (-) <$> getEnd <*> getStart

data Dynamic a = Dynamic { getDuration :: Duration
                         , runDynamic  :: Time -> a
                         }
  deriving (Functor)

instance Apply Dynamic where
  (Dynamic d1 f1) <.> (Dynamic d2 f2) = Dynamic (d1 <> d2) (f1 <.> f2)

newtype Active a = Active (MaybeApply Dynamic a)
  deriving (Functor, Apply, Applicative)

mkActive :: Time -> Time -> (Time -> a) -> Active a
mkActive begin end f
  = Active (MaybeApply (Left (Dynamic (mkDuration begin end) f)))

ui :: Active UI
ui = mkActive 0 1 fromRational

onActive :: (a -> b) -> (Dynamic a -> b) -> Active a -> b
onActive f _ (Active (MaybeApply (Right a))) = f a
onActive _ f (Active (MaybeApply (Left d)))  = f d

simulate :: Rational -> Active a -> [a]
simulate rate act =
  onActive (:[])
           (\d -> map (runDynamic d)
                      (let s = getStart (getDuration d)
                           e = getEnd   (getDuration d)
                       in  [s, s + 1/rate .. e]
                      )
           )
           act
