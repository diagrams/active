{-# LANGUAGE DeriveFunctor
           , GeneralizedNewtypeDeriving
           , TypeSynonymInstances
           , MultiParamTypeClasses
           , TypeFamilies
           , FlexibleInstances
  #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- XXX make test suite!

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Active
-- Copyright   :  (c) 2011 Brent Yorgey
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  byorgey@cis.upenn.edu
--
-- Inspired by the work of Kevin Matlage and Andy Gill (/Every/
-- /Animation Should Have a Beginning, a Middle, and an End/, Trends
-- in Functional Programming,
-- 2010. <http://ittc.ku.edu/csdl/fpg/node/46>), this module defines a
-- simple abstraction for working with time-varying values.  A value
-- of type @Active a@ is either a constant value of type @a@, or a
-- time-varying value of type @a@ (/i.e./ a function from time to
-- @a@) with specific start and end times.  Since active values
-- have start and end times, they can be aligned, sequenced,
-- stretched, or reversed.
--
-- In a sense, this is sort of like a stripped-down version of
-- functional reactive programming (FRP), without the reactivity.
--
-- The original motivating use for this library is to support making
-- animations with the diagrams framework
-- (<http://projects.haskell.org/diagrams>), but the hope is that it
-- may find more general utility.
-----------------------------------------------------------------------------

module Data.Active
       ( -- * Representing time

         -- ** Time and duration

         Time, toTime
       , Duration

         -- ** Eras

       , Era, mkEra
       , start, end, duration

         -- * Active values

       , Dynamic(..)
       , Active, mkActive, onActive, runActive

       , activeEra

         -- * Combinators

         -- ** Special active values

       , ui, interval

         -- ** Transforming active values

       , stretch, shift, backwards
       , clamp

         -- ** Composing active values

       , andThen, (->>)

         -- * Simulation

       , discrete
       , simulate

       ) where

import Control.Applicative
import Control.Newtype

import Data.Array

import Data.Functor.Apply
import Data.Semigroup

import Data.VectorSpace hiding ((<.>))
import Data.AffineSpace

------------------------------------------------------------
-- Time
------------------------------------------------------------

-- | An abstract type for representing /points in time/.  Note that
--   @Time@ values can be converted to/from other numeric types using
--   the 'Num', 'Fractional', 'Real', and 'RealFrac' instances.
--   'toTime' is also provided for convenience in converting from
--   other types (notably @Float@ and @Double@) to @Time@.
newtype Time = Time { unTime :: Rational }
  deriving ( Eq, Ord, Show, Read, Enum, Num, Fractional, Real, RealFrac
           , AdditiveGroup, InnerSpace
           )

instance Newtype Time Rational where
  pack   = Time
  unpack = unTime

instance VectorSpace Time where
  type Scalar Time = Rational
  s *^ (Time t) = Time (s * t)

-- | Convert any value of a 'Real' type (including @Int@, @Integer@,
--   @Rational@, @Float@, and @Double@) to a 'Time'.
toTime :: Real a => a -> Time
toTime = fromRational . toRational

-- | An abstract type representing /elapsed time/ between two points
--   in time.  Note that durations can be negative. @Duration@ values
--   can be converted to/from other numeric types using the 'Num',
--   'Fractional', 'Real', and 'RealFrac' instances.
newtype Duration = Duration { unDuration :: Rational }
  deriving ( Eq, Ord, Show, Read, Enum, Num, Fractional, Real, RealFrac
           , AdditiveGroup)

instance Newtype Duration Rational where
  pack   = Duration
  unpack = unDuration

instance VectorSpace Duration where
  type Scalar Duration = Rational
  s *^ (Duration d) = Duration (s * d)

instance AffineSpace Time where
  type Diff Time = Duration
  (Time t1) .-. (Time t2) = Duration (t1 - t2)
  (Time t) .+^ (Duration d) = Time (t + d)

-- | An @Era@ is a concrete span of time, that is, a pair of times
--   representing the start and end of the era. @Era@s form a
--   semigroup: the combination of two @Era@s is the smallest @Era@
--   which contains both.  They do not form a 'Monoid', since there is
--   no @Era@ which acts as the identity with respect to this
--   combining operation.
--
--   @Era@ is abstract. To construct @Era@ values, use 'mkEra'; to
--   deconstruct, use 'start' and 'end'.
newtype Era = Era (Min Time, Max Time)
  deriving (Semigroup)

-- | Create an 'Era' by specifying start and end 'Time's.
mkEra :: Time -> Time -> Era
mkEra s e = Era (Min s, Max e)

-- | Get the start 'Time' of an 'Era'.
start :: Era -> Time
start (Era (Min t, _)) = t

-- | Get the end 'Time' of an 'Era'.
end :: Era -> Time
end (Era (_, Max t)) = t

-- | Compute the 'Duration' of an 'Era'.
duration :: Era -> Duration
duration = (.-.) <$> end <*> start

------------------------------------------------------------
-- Dynamic
------------------------------------------------------------

-- | A @Dynamic a@ can be thought of as an @a@ value that changes over
--   the course of a particular 'Era'.
data Dynamic a = Dynamic { era        :: Era
                         , runDynamic :: Time -> a
                         }
  deriving (Functor)

-- | 'Dynamic' is an instance of 'Apply': a time-varying function is
--   applied to a time-varying value pointwise; the era of the result
--   is the combination of the function and value eras.  Note,
--   however, that 'Dynamic' is /not/ an instance of 'Applicative'
--   since there is no way to implement 'pure': the era would have to
--   be empty, but there is no such thing as an empty era.
instance Apply Dynamic where
  (Dynamic d1 f1) <.> (Dynamic d2 f2) = Dynamic (d1 <> d2) (f1 <.> f2)

-- | 'Dynamic a' is a 'Semigroup' whenever @a@ is: the eras are
--   combined according to their semigroup structure, and the values
--   of type @a@ are combined pointwise.  Note that 'Dynamic a' cannot
--   be an instance of 'Monoid', for the same reason that 'Dynamic' is
--   not an instance of 'Applicative'.
instance Semigroup a => Semigroup (Dynamic a) where
  Dynamic d1 f1 <> Dynamic d2 f2 = Dynamic (d1 <> d2) (f1 <> f2)

------------------------------------------------------------
--  Active
------------------------------------------------------------

-- | @Active@ is like 'Dynamic', with the addition of special
--   \"constant\" values, which do not vary over time.  These constant
--   values enable implementations of 'pure' and 'mempty'.
newtype Active a = Active (MaybeApply Dynamic a)
  deriving (Functor, Apply, Applicative)

instance Newtype (Active a) (MaybeApply Dynamic a) where
  pack              = Active
  unpack (Active m) = m

instance Newtype (MaybeApply f a) (Either (f a) a) where
  pack   = MaybeApply
  unpack = runMaybeApply

over2 :: (Newtype n o, Newtype n' o', Newtype n'' o'')
      => (o -> n) -> (o -> o' -> o'') -> (n -> n' -> n'')
over2 _ f n1 n2 = pack (f (unpack n1) (unpack n2))

instance Semigroup a => Semigroup (Active a) where
  (<>) = (over2 Active . over2 MaybeApply) combine
   where
    combine (Right m1) (Right m2)
      = Right (m1 <> m2)

    combine (Left (Dynamic dur f)) (Right m)
      = Left (Dynamic dur (f <> const m))

    combine (Right m) (Left (Dynamic dur f))
      = Left (Dynamic dur (const m <> f))

    combine (Left d1) (Left d2)
      = Left (d1 <> d2)

instance (Monoid a, Semigroup a) => Monoid (Active a) where
  mempty  = Active (MaybeApply (Right mempty))
  mappend = (<>)

-- | Create an 'Active' from a start time, an end time, and a
--   time-varying value.
mkActive :: Time -> Time -> (Time -> a) -> Active a
mkActive s e f
  = Active (MaybeApply (Left (Dynamic (mkEra s e) f)))

-- | Fold for 'Active's.  Process an 'Active a', given a function to
--   apply if it is a pure (constant) value, and a function to apply if
--   it is a 'Dynamic'.
onActive :: (a -> b) -> (Dynamic a -> b) -> Active a -> b
onActive f _ (Active (MaybeApply (Right a))) = f a
onActive _ f (Active (MaybeApply (Left d)))  = f d

-- | Interpret an 'Active' value as a function from time.
runActive :: Active a -> (Time -> a)
runActive = onActive const runDynamic

-- | Get the 'Era' of an 'Active' value (or 'Nothing' if it is
--   a constant/pure value).
activeEra :: Active a -> Maybe Era
activeEra = onActive (const Nothing) (Just . era)

------------------------------------------------------------
--  Combinators
------------------------------------------------------------

-- | @ui@ represents the /unit interval/, which takes on the value @t@
--   at time @t@, and has as its era @[0,1]@. It is equivalent to
--   @interval 0 1@.
--
--   To alter the /values/ that @ui@ takes on without altering its
--   era, use its 'Functor' and 'Applicative' instances.  For example,
--   @(*2) \<$\> ui@ varies from @0@ to @2@ over the era @[0,1]@.  To
--   alter the era, you can use 'stretch' or 'shift'.
ui :: Fractional a => Active a
ui = interval 0 1

-- | @interval a b@ is an active value starting at time @a@, ending at
--   time @b@, and taking the value @t@ at time @t@.
interval :: Fractional a => Time -> Time -> Active a
interval a b = mkActive a b (fromRational . unTime)

-- | @stretch s act@ \"stretches\" the active @act@ so that it takes
--   @s@ times as long (retaining the same start time).
stretch :: Rational -> Active a -> Active a
stretch s =
  onActive pure $ \d ->
    let er = era d
    in  mkActive
          (start er)
          (start er .+^ (s *^ duration er))
          (\t -> runDynamic d (start er .+^ ((t .-. start er) ^/ s)))

-- | @shift d act@ shifts the start time of @act@ by duration @d@.
shift :: Duration -> Active a -> Active a
shift sh =
  onActive pure $ \d ->
    let er = era d
    in  mkActive
          (start er .+^ sh)
          (end er   .+^ sh)
          (\t -> runDynamic d (t .-^ sh))

-- | Reverse an active value so the start of its era gets mapped to
--   the end and vice versa.
backwards :: Active a -> Active a
backwards =
  onActive pure $ \d ->
    let er = era d
        s  = start er
        e  = end er
    in  mkActive s e
          (\t -> runDynamic d (e - t + s))

-- | \"Clamp\" an active value so that it is constant outside its era.
--   Before the era, @clamp a@ takes on the value of @a@ at the start
--   of the era.  Likewise, after the era, @clamp a@ takes on the
--   value of @a@ at the end of the era.
--
--   For example XXX.
clamp :: Active a -> Active a
clamp =
  onActive pure $ \d ->
    let er = era d
        s  = start er
        e  = end er
    in  mkActive s e
          (\t -> case () of _ | t < s     -> runDynamic d s
                              | t > e     -> runDynamic d e
                              | otherwise -> runDynamic d t)

-- setEra :: Era -> Active a -> Active a

-- | XXX
andThen :: Active a -> Active a -> Active a
andThen a1 a2 = undefined  -- XXX

-- | Convenient infix operator synonym of 'andThen'.
(->>) :: Active a -> Active a -> Active a
(->>) = andThen

------------------------------------------------------------
--  Simulation
------------------------------------------------------------

-- | Create an @Active@ which takes on each value in the given list in
--   turn during the time @[0,1]@, with each value getting an equal
--   amount of time.  In other words, @discrete@ creates a "slide
--   show" that starts at time 0 and ends at time 1.  The first
--   element is used prior to time 0, and the last element is used
--   after time 1.
--
--   It is an error to call 'discrete' on the empty list.
discrete :: [a] -> Active a
discrete [] = error "Data.Active.discrete must be called with a non-empty list."
discrete xs = f <$> (ui :: Active Rational)
  where f t | t <= 0    = arr ! 0
            | t >= 1    = arr ! (n-1)
            | otherwise = arr ! floor (t * fromIntegral n)
        n   = length xs
        arr = listArray (0, n-1) xs

-- | @simulate r act@ simulates the 'Active' value @act@, returning a
--   list of \"snapshots\" taken at regular intervals from the start
--   time to the end time.  The interval used is determined by the
--   rate @r@, which denotes the \"frame rate\", that is, the number
--   of snapshots per unit time.
--
--   If the 'Active' value is constant (and thus has no start or end
--   times), a list of length 1 is returned, containing the constant
--   value.
simulate :: Rational -> Active a -> [a]
simulate rate act =
  onActive (:[])
           (\d -> map (runDynamic d)
                      (let s = start (era d)
                           e = end   (era d)
                       in  [s, s + 1^/rate .. e]
                      )
           )
           act