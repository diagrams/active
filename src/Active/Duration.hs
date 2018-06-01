{-# LANGUAGE DeriveFunctor  #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}

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
  ( -- * Duration

    Duration(..)

    -- * Conversion

  , toDuration, fromDuration

    -- * Operations

  , subDuration

  ) where

import           Linear.Vector

------------------------------------------------------------
-- Durations
------------------------------------------------------------

-- | The type of (potentially infinite) /durations/ over a given
--   numeric type @n@. The infinite duration is longer than any finite
--   duration.
data Duration :: * -> * where

  -- | A finite duration of a given nonnegative length.  The length
  --   can be zero.
  Duration :: n -> Duration n

  -- | An infinite duration.
  Forever  ::      Duration n

  deriving (Show, Eq, Ord, Functor)

instance Applicative Duration where
  pure = Duration
  Forever <*> _ = Forever
  _ <*> Forever = Forever
  Duration f <*> Duration x = Duration (f x)

-- | Durations inherit the additive structure of the underlying
--   numeric type; the sum of the infinite duration with anything is
--   infinite. Note that it does not make sense to multiply durations,
--   but you can scale them by a constant using the ('*^') operator
--   from the 'Additive' instance.
--
--   This instance also gives us the convenience of 'fromInteger', so
--   numeric literals can be used as finite durations.
instance Num n => Num (Duration n) where
  fromInteger               = toDuration . fromInteger

  Forever     + _           = Forever
  _           + Forever     = Forever
  Duration d1 + Duration d2 = Duration (d1 + d2)

  abs Forever               = Forever
  abs (Duration n)          = Duration (abs n)

  (*)                       = error "Multiplying durations makes no sense. Use (*^) to scale by a constant."
  negate                    = error "Negating durations makes no sense."
  signum                    = error "Signum on durations makes no sense."

instance Additive Duration where
  zero = Duration 0

-- | A wrapper function to convert a numeric value into a finite duration.
toDuration :: n -> Duration n
toDuration = Duration

-- | An unwrapper function to turn a duration into a numeric value.
--   Finite durations become @Just@; the infinite duration becomes
--   @Nothing@.
fromDuration :: Duration n -> Maybe n
fromDuration Forever      = Nothing
fromDuration (Duration n) = Just n

-- | Subtract a finite duration from another duration.  If the first
--   duration is infinite, the result is also infinite.  If the second
--   duration is longer than the first, the result is zero.
subDuration :: (Num n, Ord n) => Duration n -> Duration n -> Duration n
subDuration Forever      _                      = Forever
subDuration (Duration a) (Duration b) | b <= a  = Duration (a - b)
subDuration _ _                                 = Duration 0

