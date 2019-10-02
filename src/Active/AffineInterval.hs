-----------------------------------------------------------------------------
-- |
-- Module      :  Active.AffineInterval
-- Copyright   :  2019 Brent Yorgey, Nick Wu
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  byorgey@gmail.com
-----------------------------------------------------------------------------

-- XXX document me, add export list
module Active.AffineInterval where

-- XXX add discussion/explanation
-- XXX add pictures to everything

import           Active.Duration
import           Data.Maybe      (fromMaybe, isJust)

-- | XXX document me
class AffineInterval i where
  duration     :: i -> Duration Rational
  stretch      :: Rational -> i -> i
  backwardsMay :: i -> Maybe i
  cut          :: Rational -> i -> i
  omit         :: Rational -> i -> i
  shift        :: Rational -> i -> i

-- Semimodule?  i.e. we only allow stretching by positive amounts, but
-- there is also "backwards"?  Notice allowing stretch by negative
-- doesn't satisfy module/vector space laws...?

-- | (Unsafely) extract the duration of an @Active@ value that you know
--   to be finite.  __Partial__: throws an error if given an infinite
--   argument.
durationF :: AffineInterval i => i -> Rational
durationF i = case duration i of
  Forever    -> error "durationF called on infinite interval"
  Duration d -> d

-- XXX
backwards :: AffineInterval i => i -> i
backwards
  = fromMaybe (error "backwards called on infinite interval")
  . backwardsMay

-- Add implementations of
-- cutTo, slice
-- in terms of the combinators in the class.
--
-- Keep the versions in the Active module so we can keep the nice
-- documentation with pictures.  Just import this module qualified.
-- No, just put the pictures in here!  Then re-export individually
-- from the Active module.

-- | Stretch a finite interval by whatever factor is required so that it
--   ends up with the given duration.
stretchTo :: AffineInterval i => Rational -> i -> i
stretchTo d
  = fromMaybe (error "stretchTo called on infinite interval")
  . stretchToMay d

-- | A safe, total variant of 'stretchTo'.  Performs 'stretchTo' on a
--   finite argument, and returns @Nothing@ for an infinite argument.
stretchToMay :: AffineInterval i => Rational -> i -> Maybe i
stretchToMay n i = case duration i of
  Duration d -> Just $ stretch (n / d) i
  _          -> Nothing

-- | Stretch the second interval so it has the same duration as the
--   first.  If both are infinite, do nothing.
--
--   __Partial__: throws an error if one of the arguments is finite
--   and the other infinite.  See also 'matchDurationMay'.

matchDuration :: AffineInterval i => i -> i -> i
matchDuration a b
  = fromMaybe (error "matchDuration called on arguments of different finitude")
  $ matchDurationMay a b

-- | A total, safe variant of 'matchDuration' which returns @Nothing@
--   when given one finite and one infinite argument.
matchDurationMay :: AffineInterval i => i -> i -> Maybe i
matchDurationMay a b = case (duration a, duration b) of
  (Forever    , Forever    ) -> Just b
  (Duration d1, Duration d2) -> Just $ stretch (d1/d2) b
  _                          -> Nothing

-- | @cutTo a1 a2@ 'cut'\s @a2@ to match the duration of @a1@, unless
--   @a2@ is already shorter than @a1@ in which case @cutTo a1 = id@.
cutTo :: AffineInterval i => i -> i -> i
cutTo a = case duration a of
  Duration d -> cut d
  _          -> id

-- | @slice s e@ "slices out" a finite portion of an interval starting
--   at time @s@ and ending at time (at most) @e@.  If the start time
--   is greater than the end time, the resulting slice is reversed in
--   time.
--
--   __Partial__: the result is only defined if \( \min(s,e) \leq d \) where
--   \( d \) is the duration of the interval.
--
--   @
-- slice s e = cut (e - s) . omit s   (if e >= s)
-- slice s e = backwards . slice e s
--   @

slice :: AffineInterval i => Rational -> Rational -> i -> i
slice s e a
  -- Could just defer the error to 'omit', but that might confuse
  -- users who would wonder why they got an error message about 'omit'
  -- even though they never used that function.
  | Duration (min s e) > duration a
    = error "slice: starting time greater than the duration of the given interval"
  | e >= s    = cut (e - s) . omit s $ a
  | otherwise = backwards . slice e s $ a
