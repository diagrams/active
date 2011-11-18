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

data Dynamic a = Dynamic Duration (Time -> a)
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