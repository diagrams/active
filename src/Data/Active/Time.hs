{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Active.Time
-- Copyright   :  (c) 2013 Andy Gill, Brent Yorgey
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  byorgey@cis.upenn.edu
--
-- This module defines several type classes for representations of
-- time (which can be used /e.g./ for building deep embeddings), as
-- well as a concrete default representation.
-----------------------------------------------------------------------------

module Data.Active.Time
    ( -- * Default concrete representations of time and duration

      Time, time
    , Duration, duration

      -- * Shifting things in time

    , Shifty(..)

      -- * Abstract time and duration
      -- | This section contains generic type classes which can be
      --   used as the basis of deep embeddings of @Active@.

    , Clock(..)
    , Waiting(..)
    , Deadline(..)
    , FractionalOf(..)

    )
    where

import           Control.Arrow ((***))
import           Control.Lens
import           Data.AffineSpace
import qualified Data.Map as M
import           Data.Proxy
import           Data.VectorSpace

import           Data.Active.Endpoint

------------------------------------------------------------
-- Clock
------------------------------------------------------------

-- | A class that abstracts over time, taking into account the
--   difference and interaction between /moments/ (/e.g./ 2pm) and
--   /durations/ (/e.g./ 2 hours).  If @t@ is the type of moments,
--   then @Diff t@ is the type of durations, which together form an
--   'AffineSpace'.
class (AffineSpace t, Waiting (Diff t)) => Clock t where

  -- | Convert any value of a 'Real' type (including @Int@, @Integer@,
  --   @Rational@, @Float@, and @Double@) to a time.
  toTime :: Real a => a -> t

  -- | Convert a time to a fractional type.  For the standard 'Time'
  -- type, this includes any instance of 'Fractional' (such as
  -- @Rational@, @Float@, or @Double@). Other 'Clock' instances
  -- (/e.g./ for deep embeddings) may have more specialized
  -- corresponding fractional types.
  fromTime :: (FractionalOf t a) => t -> a

  -- | Take the minimum (earlier) of two moments.
  firstTime :: t -> t -> t

  -- | Take the maximum (later) of two moments.
  lastTime  :: t -> t -> t

-- | A type class for /durations/.
class (FractionalOf w (Scalar w), VectorSpace w) => Waiting w where

  -- | Convert any value of a 'Real' type (including @Int@, @Integer@,
  --   @Rational@, @Float@, and @Double@) to a duration.
  toDuration :: Real a => a -> w

  -- | Convert a duration to a fractional type. For the standard
  --   'Duration' type, this includes any instance of 'Fractional'
  --   (such as @Rational@, @Float@, or @Double@).  Other 'Waiting'
  --   instances (/e.g./ for deep embeddings) may have more
  --   specialized corresponding fractional types.
  fromDuration :: (FractionalOf w a) => w -> a

-- | A class abstracting over fractional types corresponding to some
--   time or duration type, needed to build specialized deep
--   embeddings (for example, an embedding to JavaScript may use some
--   special type representing JavaScript floating-point values).
class Fractional a => FractionalOf v a where
  toFractionalOf :: v -> a

-- | An instance of @Deadline@ lets us choose between two values based
--   on a \"deadline\": the first value is chosen before the deadline
--   and the second value after.  The behavior at the precise moment
--   of the deadline is determined by the @l@ and @r@ type indices,
--   indicating whether the left-hand interval is closed (@l ~ C@, @r
--   ~ O@, in which case the first value is chosen at the precise
--   deadline), or the right (@l ~ O@, @r ~ C@, the second value is
--   chosen at the deadline).
class (Clock t, Compat l r)
  => Deadline (l :: EndpointType) (r :: EndpointType) t a where

  -- | Choose one of two values based on the time in relation to a
  --   given deadline.
  choose :: Proxy l -- ^ Proxy for the left endpoint type, to drive
                    --   instance selection
         -> Proxy r -- ^ Proxy for the right endpoint type
         -> t       -- ^ Deadline
         -> t       -- ^ Current time
         -> a       -- ^ Value before deadline
         -> a       -- ^ Value after deadline
         -> a

------------------------------------------------------------
-- Time + Duration
------------------------------------------------------------

-- | An abstract type for representing /points in time/, aka
-- /moments/.  Note that literal numeric values may be used as
-- @Time@s, thanks to the the 'Num' and 'Fractional' instances.
-- 'toTime' and 'fromTime' are also provided for convenience in
-- converting between @Time@ and other numeric types.
newtype Time = Time { _time :: Rational }
  deriving ( Eq, Ord, Show, Read, Enum, Num, Fractional, Real, RealFrac )

makeLensesWith (lensRules & generateSignatures .~ False) ''Time

-- | An isomorphism lens for working directly on the underlying
--   @Rational@ value of a @Time@.
time :: Iso' Time Rational

instance AffineSpace Time where
  type Diff Time = Duration
  (Time t1) .-. (Time t2) = Duration (t1 - t2)
  (Time t) .+^ (Duration d) = Time (t + d)

instance Clock Time where
  toTime    = fromRational . toRational
  fromTime  = fromRational . view time
  firstTime = min
  lastTime  = max

instance Fractional a => FractionalOf Time a where
  toFractionalOf (Time d) = fromRational d

instance Deadline C O Time a where
  choose _ _ deadline now a b = if now <= deadline then a else b

instance Deadline O C Time a where
  choose _ _ deadline now a b = if now <  deadline then a else b

-- | An abstract type representing /elapsed time/ between two moments.
--   Note that durations can be negative. Literal numeric values may
--   be used as @Duration@s thanks to the 'Num' and 'Fractional'
--   instances. 'toDuration' and 'fromDuration' are also provided for
--   convenience in converting between @Duration@s and other numeric
--   types.
newtype Duration = Duration { _duration :: Rational }
  deriving ( Eq, Ord, Show, Read, Enum, Num, Fractional, Real, RealFrac
           , AdditiveGroup)

makeLensesWith (lensRules & generateSignatures .~ False) ''Duration

-- | An isomorphim lens for working directly on the underlying
--   @Rational@ value of a @Duration@.
duration :: Iso' Duration Rational

instance VectorSpace Duration where
  type Scalar Duration = Rational
  s *^ (Duration d) = Duration (s * d)

instance Waiting Duration where
  toDuration = fromRational . toRational
  fromDuration = toFractionalOf

instance Fractional a => FractionalOf Duration a where
  toFractionalOf (Duration d) = fromRational d

--------------------------------------------------
-- Shifty
--------------------------------------------------

-- Note this is a monoid action of durations on timey things.  But we
-- can't really use the Action type class because we want it to be
-- polymorphic in both the timey things AND the durations (so we can
-- do deep embedding stuff and use e.g. JSDuration or whatever).

-- | A type class for things which can be shifted in time.
class Shifty a where

  -- | The corresponding type of moments.
  type ShiftyTime a :: *

  -- | Shift by the given duration.
  shift :: Diff (ShiftyTime a) -> a -> a

instance Shifty s => Shifty (Maybe s) where
  type ShiftyTime (Maybe s) = ShiftyTime s

  shift = fmap . shift

instance (Shifty a, Shifty b, ShiftyTime a ~ ShiftyTime b) => Shifty (a,b) where
  type ShiftyTime (a,b) = ShiftyTime a

  shift d = shift d *** shift d

-- | Functions from time to any type @a@ can be thought of as a
--   \"sequence\" (possibly continuous) of values of type @a@;
--   shifting the function has the semantics of shifting this sequence
--   of values.  Concretely, this is accomplished by /subtracting/ the
--   given duration from inputs to the function.
instance (AffineSpace t) => Shifty (t -> a) where
  type ShiftyTime (t -> a) = t

  shift d f = f . (.-^ d)

instance AffineSpace t => Shifty (M.Map k t) where
  type ShiftyTime (M.Map k t) = t

  shift d = fmap (.+^ d)

instance Shifty Time where
  type ShiftyTime Time = Time

  shift d = (.+^ d)

instance AffineSpace t => Shifty (Endpoint e t) where
  type ShiftyTime (Endpoint e t) = t

  shift d = fmap (.+^ d)

