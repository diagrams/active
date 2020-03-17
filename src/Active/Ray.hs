-- XXX todo: clean up, make module header etc.

module Active.Ray where

import           Active.Duration
import           Data.Ratio

-- | @Ray c d k p@ represents an arithmetic progression of points in
--   time (i.e. regular samples), contained in a closed interval
--   beginning at @c@ with duration @d@.  @p@ is the "phase shift", so
--   that the first sample is at @c + p@.  In general, the samples are
--   at @c + p + kt@ for natural numbers @t@.
--
--   More abstractly, a @Ray@ represents an affine transformation of
--   some initial segment of \([0,\infty)\) plus a phase shift @p@.
--
--   Invariants: \(0 \leq |p| < |k|\); k and p have the same sign.
data Ray = Ray Rational (Duration Rational) Rational Rational
  deriving Show

rayPoints :: Ray -> [Rational]
rayPoints (Ray c Forever      k p) = map (\t -> p + k*t + c) $ [0 ..]
rayPoints (Ray c (Duration d) k p) = takeWhile (\r -> abs (r - c) <= d)
                                   . map (\t -> p + k*t + c)
                                   $ [0 ..]

primRay :: Dur -> Ray
primRay d = Ray 0 d 1 0

cutRay :: Dur -> Ray -> Ray
cutRay x (Ray c d k p)  = Ray c (x `min` d) k p

rmod :: Rational -> Rational -> Rational
rmod r m = r - m * fromIntegral (floor (r/m))

-- Drop an initial segment of length x from a ray.
-- Assumption: x <= duration of the ray.
omitRay :: Rational -> Ray -> Ray
omitRay x (Ray c d k p)
  = Ray (c + offset)
          -- The new starting point is x distance from c.

        (d `subDuration` Duration x)
          -- The new duration is just the old duration - x.

        k
          -- The scaling factor is unaffected.

        ((p - offset) `rmod` k)
          -- The new phase shift is the old phase shift minus the
          -- offset, mod k.
  where
    offset = signum k * x
      -- The actual offset is in a direction determined by the sign of
      -- k.

-- XXX
offsetRay :: Rational -> Ray -> Ray
offsetRay x (Ray c d k p) = Ray (c + x) d k p

splitRay :: Rational -> Ray -> (Ray, Ray)
splitRay x r = (cutRay (Duration x) r, offsetRay (-x) (omitRay x r))

-- Assume d is Finite.
reverseRay :: Ray -> Ray
reverseRay (Ray c (Duration d) k p) = Ray (c + d * signum k) (Duration d) (-k) p'
  where
    p' = abs (d - p) `rmod` abs k

stretchRay :: Rational -> Ray -> Ray
stretchRay r (Ray c d k p) = Ray c ((/r) <$> d) (k/r) (p/r)

-- Check whether the given rational is contained in the ray
onRay :: Rational -> Ray -> Bool
onRay x (Ray c d k p) =
    -- check sign of k.
    --   - if k > 0  then  c <= x <= c + d
    --   - otherwise       c - d <= x <= c
    -- also need x == c + p + kt for some integer t.
    --   hence compute (x - c - p) / k  and check whether it is integer.
  upperBound && lowerBound && (denominator ((x - c - p) / k) == 1)
  where
    upperBound = case d of
      Duration d'
        | k > 0 -> x <= c + d'
        | k < 0 -> c - d' <= x
      Forever     -> True
    lowerBound
      | k > 0 = c <= x
      | k < 0 = x <= c
