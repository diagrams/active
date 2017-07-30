{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE TypeOperators      #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Active.Duration
-- Copyright   :  (c) 2017 Brent Yorgey
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  byorgey@gmail.com
--
-- Finite and infinite durations.
-----------------------------------------------------------------------------

module Active.Duration
  ( -- * Finitude

    Finitude(..)
  , type (⊔)
  , type (⊓)

    -- * Duration

  , Duration(..)

    -- * Conversion

  , toDuration, fromDuration, fromDurationF

    -- * Operations

  , addDuration, subDuration, maxDuration, minDuration, compareDuration

  ) where

import           Linear.Vector

------------------------------------------------------------
-- Finitude
------------------------------------------------------------

-- | A 'Finitude' value denotes whether something is finite ('F') or
--   infinite ('I').  It exists mostly to be used as a lifted type
--   index.
data Finitude =
    F    -- ^ Finite
  | I    -- ^ Infinite

-- | Union on finitudes. The union of an infinite thing with anything
--   is infinite; the union of two finite things is finite.
--
--   Finitudes form a monoid under this operation with 'F' as the
--   identity element.
type family (f1 :: Finitude) ⊔ (f2 :: Finitude) :: Finitude where
  f ⊔ f = f
  F ⊔ f = f
  I ⊔ f = I

-- | Intersection on type-level finitudes.  This is not quite as
--   straightforward as union: the intersection of a finite set with
--   anything is finite, but we can't say anything in particular about
--   the size of the intersection of two infinite sets.  However, we
--   think of the finitudes as representing not arbitrary sets but
--   potentially right-infinite intervals on the positive real line.
--   In that case the intersection of two right-infinite intervals
--   must be infinite.
--
--   This operation is associative; 'Finitude' forms a monoid with 'I'
--   as the identity element.
type family (f1 :: Finitude) ⊓ (f2 :: Finitude) :: Finitude where
  f ⊓ f = f
  F ⊓ f = F
  I ⊓ g = g

------------------------------------------------------------
-- Durations
------------------------------------------------------------

-- | The type of (potentially infinite) /durations/ over a given
--   numeric type @n@.  The type index @f@ indicates whether the
--   duration is finite or infinite.  The infinite duration is longer
--   than any finite duration.
data Duration :: Finitude -> * -> * where

  -- | A finite duration of a given nonnegative length.  The length
  --   could be zero.
  Duration :: n -> Duration F n

  -- | An infinite duration.
  Forever  ::      Duration I n

deriving instance Show n => Show (Duration f n)
deriving instance Functor (Duration f)

instance Applicative (Duration F) where
  pure = Duration
  Duration f <*> Duration x = Duration (f x)

instance Eq n => Eq (Duration f n) where
  Duration n1 == Duration n2 = n1 == n2
  Forever     == Forever     = True

-- | Note that the 'Ord' instance for 'Duration' is not quite as
--   useful as one might like: it forces the type indices to be the
--   same, so it can only be used to compare two finite or two
--   infinite durations.  To compare durations in general, use
--   'compareDuration'.
instance Ord n => Ord (Duration f n) where
  compare (Duration n1) (Duration n2) = compare n1 n2
  compare Forever Forever             = EQ

-- | Compare two durations.
compareDuration :: Ord n => Duration f1 n -> Duration f2 n -> Ordering
compareDuration Forever       Forever       = EQ
compareDuration (Duration _)  Forever       = LT
compareDuration Forever       (Duration _)  = GT
compareDuration (Duration n1) (Duration n2) = compare n1 n2

-- | /Finite/ durations inherit the additive structure of the
--   underlying numeric type.  (Note that it does not make sense to
--   multiply durations, but you can scale them by a constant using
--   the ('*^') operator from the 'Additive' instance.) To add
--   durations in general (finite or infinite), see 'addDuration'.
--
--   This instance also gives us the convenience of 'fromInteger', so
--   numeric literals can be used as finite durations.
instance Num n => Num (Duration F n) where
  fromInteger               = toDuration . fromInteger
  negate (Duration d)       = Duration (negate d)
  Duration d1 + Duration d2 = Duration (d1 + d2)
  (*)    = error "multiplying durations makes no sense"
  abs (Duration n)          = Duration (abs n)
  signum = error "signum on durations makes no sense"

instance Additive (Duration F) where
  zero = Duration 0

-- | A wrapper function to convert a numeric value into a finite duration.
toDuration :: n -> Duration F n
toDuration = Duration

-- | An unwrapper function to turn a duration into a numeric value.
--   Finite durations become @Just@; the infinite duration becomes
--   @Nothing@.
fromDuration :: Duration f n -> Maybe n
fromDuration Forever      = Nothing
fromDuration (Duration n) = Just n

-- | Like 'fromDuration' when you know you have a finite duration.
fromDurationF :: Duration F n -> n
fromDurationF (Duration n) = n

-- | Add two durations.  If either one is infinite, so is the result;
--   finite durations add normally.
addDuration :: Num n => Duration f1 n -> Duration f2 n -> Duration (f1 ⊔ f2) n
addDuration Forever      _            = Forever
addDuration (Duration _) Forever      = Forever
addDuration (Duration a) (Duration b) = Duration (a + b)

-- | Subtract a finite duration from another duration.  If the first
--   duration is infinite, the result is also infinite.  If the second
--   duration is longer than the first, the result is zero.
subDuration :: (Num n, Ord n) => Duration f1 n -> Duration F n -> Duration f1 n
subDuration Forever      _            = Forever
subDuration (Duration a) (Duration b)
  | b <= a    = Duration (a - b)
  | otherwise = Duration 0

-- | The maximum of two durations.
maxDuration :: Ord n => Duration f1 n -> Duration f2 n -> Duration (f1 ⊔ f2) n
maxDuration Forever      _            = Forever
maxDuration (Duration _) Forever      = Forever
maxDuration (Duration a) (Duration b) = Duration (max a b)

-- | The minimum of two durations.
minDuration :: (Num n, Ord n) => Duration f1 n -> Duration f2 n -> Duration (f1 ⊓ f2) n
minDuration Forever Forever           = Forever
minDuration Forever (Duration b)      = Duration b
minDuration (Duration a) Forever      = Duration a
minDuration (Duration a) (Duration b) = Duration (min a b)

-- could make ISemigroup, IMonoid classes...

