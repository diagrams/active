{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE ScopedTypeVariables #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Active
-- Copyright   :  2011-2017 Brent Yorgey
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  byorgey@gmail.com
--
-- @active@ is a small EDSL for building continuous, time-varying values
-- of arbitrary type. It is particularly useful for building media
-- such as animations, audio clips, and the like, but it is often
-- useful to have other values that vary over time (vectors, colors,
-- filters, volume levels...) and be able to create and use them in
-- the service of constructing time-varying media.
--
-- Some of the important concepts/features of the library include:
--
-- * Every 'Active' value has a /duration/, which is either a
--   nonnegative rational number, or infinite.
-- * An @Active@ value with finite duration \(d\) can be thought of as
--   a function \([0,d] \to a\), assigning a value to each instant on
--   the closed interval \([0,d]\); an @Active@ with infinite duration
--   assigns a value to every nonnegative time.
-- * @Active@ values are /time-invariant/, that is, they do not have a
--   fixed, absolute starting time.  Put another way, time is always
--   relative: one can say that `a` should start two seconds after `b`,
--   but one cannot say that `a` should start at 2pm on Thursday.
-- * @Active@ values can be composed both in sequence and in parallel,
--   with special attention paid to how underlying values should be
--   composed when there is overlap.
-- * The 'Applicative' instance can be used to apply time-varying
--   functions to time-varying values.
-- * Time-varying numeric values can be conveniently manipulated via
--   appropriate 'Num', 'Fractional', and 'Floating' instances.
--
-- Throughout this Haddock documentation, various primitive @Active@
-- values and combinators are illustrated using graphical
-- representations of time-varying numeric values, that is, values of
-- type @Active d@ for some numeric type @d@.  They are drawn with
-- time increasing along the x-axis and numeric value on the y-axis.
-- For example, the @Active@ of duration 3 which has value \(t/2\) at
-- time \(t\) would be drawn like this:
--
-- <<diagrams/src_Active_exampleDia.svg#diagram=exampleDia&width=200>>
--
-- Some combinators are also illustrated by showing "before" and
-- "after" diagrams, to visualize their effect.  For example, the
-- 'backwards' combinator reverses a finite @Active@ in time; it could
-- be illustrated thus:
--
-- <<diagrams/src_Active_backwardsDia.svg#diagram=backwardsDia&width=450>>
--
-- Often, the meaning of combining @Active a@ values depends on a
-- 'Semigroup' instance for @a@.  Most of the illustrations use the
-- 'Sum' semigroup over the underlying numeric type.  For example, the
-- operation of combining two @Active@ values in parallel is
-- illustrated by adding their respective values:
--
-- <<diagrams/src_Active_parUDia.svg#diagram=parUDia&width=450>>
--
-- The code for producing these diagrams isn't particularly pretty,
-- but you can look at it if you like: just view the source of this
-- module and scroll all the way to the bottom.
--
-----------------------------------------------------------------------------

module Active
  ( -- * Durations
    -- | A few things from the "Active.Duration" module are
    --   re-exported for convenience.

    Duration(..), toDuration

    -- * The Active type
  , Active

    -- * Building actives
  , activeF, activeI, active
  , instant, lasting, always
  , ui, ui', interval, interval', dur, dur'
  , (<#>)
  , discreteNE, discrete

    -- * Convenient primitives

  , sin', cos'
  , ramp, cosRamp

    -- * Running/sampling actives

  , runActive, runActiveMay, runActiveOpt
  , duration, durationF, isFinite
  , start, end, endMay, samples

    -- * Sequential composition
    -- $seq

    -- ** Stitching
  , (->-), stitchNE, stitch, Sequential(..)

    -- ** Movies
  , (->>), (>>-), movieNE, movie


    -- ** Accumulating
  , (-<>-), accumulateNE, accumulate

    -- * Parallel composition
    -- $par

    -- ** Unioning parallel composition
    -- $union

  , parU, (<∪>), stackNE, stack, stackAt, stackAtDef

    -- ** Intersecting parallel composition
    -- $inter

  , parI, (<∩>)

    -- * Modifying

    -- ** Playing with time
  , backwards, backwardsMay, snapshot, delay

    -- ** Stretching

  , stretch, stretchTo, matchDuration, matchDurationMay

    -- ** Slicing and dicing
  , cut, cutTo, omit, slice

  ) where

import           Data.Coerce

import           Control.Applicative
import           Data.Bifunctor      (second)
import           Data.List.NonEmpty  (NonEmpty (..))
import           Data.Maybe          (fromJust, fromMaybe)
import           Data.Semigroup
import qualified Data.Vector         as V
import           Linear.Vector

import           Active.Duration


------------------------------------------------------------
--  Active
------------------------------------------------------------

-- | A value of type @Active a@ is a time-varying value of type
--   @a@ with a given duration.
--
--   If the duration is infinite, it can be thought of as a function
--   \( [0,+\infty) \to a \); if it has a finite duration \( d \), it
--   can be thought of as a function \( [0,d] \to a \) (note in
--   particular that the interval is /closed/ on both ends: the
--   function is defined at \(0\) as well as at the duration \(d\)).
--
--   @Active@ is an 'Applicative' 'Functor'; if @a@ is a 'Semigroup'
--   then @Active a@ is as well.  @Active a@ is an instance of 'Num',
--   'Fractional', and 'Floating' as long as there is a corresponding
--   instance for @a@.  All these instances are described in much more
--   detail in the sections on sequential and parallel composition
--   below.
--
--   This definition is intentionally abstract, since the
--   implementation may change in the future to enable additional
--   optimizations.
--
--   Semantically, an @Active@ only needs to be defined on the
--   interval \([0,d]\), although in Haskell there is no way to
--   enforce this with types.  For example,
--
-- @
-- activeF 3 (\d -> if d <= 3 then d*2 else error "o noes!")
-- @
--
--   is considered a well-defined, total 'Active' value, even though
--   the provided Haskell function is partial.  Because 'Active' is
--   abstract, it is impossible to ever observe the value of an
--   'Active' past its duration.
--
-- @
-- >> let a = activeF 3 (\d -> if d <= 5 then d*2 else error "o noes!")
-- >> runActive a 4
-- *** Exception: Active.runActive: Active value evaluated past its duration.
-- @
--
--   Even though in this example the provided Haskell function is
--   defined at the value 4 (in particular it is equal to 8), it is
--   impossible to observe this since the 'Active' has a duration of
--   only 3.

data Active :: * -> * where
  Active   :: Duration Rational -> (Rational -> a) -> Active a
  deriving Functor

--------------------------------------------------
-- Constructing

-- | Smart constructor for finite 'Active' values, given a finite
--   numeric duration \(d\) and a function from \([0,d] \to a\).
--
--   @'activeF' d f = 'cut' d 'dur'    '<#>' f
--            = 'interval' 0 d '<#>' f@
--
--   In the example below, @activeF 2 (^2)@ constructs the Active
--   value which lasts for 2 time units and takes on the value
--   \( t^2 \) at time \( t \).  Note that some alternative, perhaps more
--   idiomatic ways to construct the same value would be @('interval'
--   0 2)^2@, or @'cut' 2 ('dur'^2)@.
--
--   <<diagrams/src_Active_activeFDia.svg#diagram=activeFDia&width=200>>
--
--   > activeFEx :: Active Rational
--   > activeFEx = activeF 2 (^2)

activeF :: Rational -> (Rational -> a) -> Active a
activeF = Active . Duration

-- > activeFDia = illustrateActive' 0.1 [] activeFEx


-- | Smart constructor for infinite 'Active' values, given a total
--   function of type \(d \to a\) giving a value of type \(a\) at every
--   time.
--
--   <<diagrams/src_Active_activeIDia.svg#diagram=activeIDia&width=200>>
--
--   > activeIEx :: Active Double
--   > activeIEx = activeI (sqrt . fromRational)
--
--   Since @Active a@ is an instance of 'Floating' whenever @a@ is,
--   @activeI (sqrt . fromRational)@ can alternatively be written as
--   @sqrt 'dur''@.
activeI :: (Rational -> a) -> Active a
activeI = Active Forever

-- > activeIDia = illustrateActive' 0.1 [] activeIEx


-- | Generic smart constructor for 'Active' values, given a 'Duration'
--   and a function on the appropriate interval.
active :: Duration Rational -> (Rational -> a) -> Active a
active = Active


-- | A value of duration zero.
--
--   @'instant' a = 'lasting' 0 a@
--
--   <<diagrams/src_Active_instantDia.svg#diagram=instantDia&width=200>>
--
--   > instantEx :: Active Rational
--   > instantEx = instant 2

instant :: a -> Active a
instant = lasting 0

-- > instantDia = illustrateActive instantEx


-- | A constant value lasting for the specified duration.
--
-- @'lasting' d = 'activeF' d . const
--          = 'cut' d . always@
--
--   <<diagrams/src_Active_lastingDia.svg#diagram=lastingDia&width=200>>
--
--   > lastingEx :: Active Rational
--   > lastingEx = lasting 3 2
--
--   This reads particularly nicely when used with postfix function
--   application, a la @(#)@ from the diagrams library.  For example:
--
--   @
-- c :: Active Char
-- c = movie
--   [ \'a\' # lasting 2
--   , \'b\' # lasting 3
--   , \'c\' # lasting 1
--   ]
-- @
--

lasting :: Rational -> a -> Active a
lasting d = activeF d . const

-- > lastingDia = illustrateActive lastingEx


-- | The unit interval: the identity function on the interval \( [0,1] \).
--
--   <<diagrams/src_Active_uiDia.svg#diagram=uiDia&width=200>>
ui :: Active Rational
ui = active 1 id

-- > uiDia = illustrateActive ui

-- | The unit interval with any @Fractional@ type, provided for
--   convenience.  For an explanation of why this is not the default,
--   see the documentation for 'dur''.
--
--   @ui' = 'ui' '<#>' fromRational@
ui' :: Fractional d => Active d
ui' = ui <#> fromRational


-- | An infinite sine wave with a period of @1@, that is,
--   \( d \mapsto \sin(2\pi d) \).  This can be convenient when
--   creating repetitive behavior with a period measured in whole
--   number units.
--
--   <<diagrams/src_Active_sin'Dia.svg#diagram=sin'Dia&width=200>>
--
--   >>> let act = cut 1 (sin' + cos')
--   >>> let ht x = 8 + round (4*x)
--   >>> mapM_ putStrLn $ samples 24 (act <#> \x -> replicate (ht x) '*')
--   ************
--   *************
--   *************
--   **************
--   *************
--   *************
--   ************
--   ***********
--   *********
--   ********
--   *******
--   *****
--   ****
--   ***
--   ***
--   **
--   ***
--   ***
--   ****
--   *****
--   *******
--   ********
--   *********
--   ***********
--   ************

sin' :: Floating n => Active n
sin' = sin (2*pi*dur')

-- > sin'Dia = illustrateActive' 0.1 [] sin'


-- | An infinite cosine wave with a period of @1@, that is,
--   \( d \mapsto \cos(2\pi d) \).   This can be convenient when
--   creating repetitive behavior with a period measured in whole
--   number units.
--
--   <<diagrams/src_Active_cos'Dia.svg#diagram=cos'Dia&width=200>>

cos' :: Floating n => Active n
cos' = cos (2*pi*dur')

-- > cos'Dia = illustrateActive' 0.1 [] cos'


-- | Particularly when animating motion, it looks bad to have things
--   simply move linearly from one point to another; it looks much
--   nicer if they accelerate away from their starting point and then
--   decelerate as they reach their goal.  This can be achieved by
--   linearly interpolating between the points according to the output
--   of some ramp function.
--
--   @ramp@ has duration 1 and takes on values in the interval \([0,1]\).
--   It happens to correspond to the specific function
--
--   \(f(t) = -20t^7 + 70t^6 - 84t^5 + 35t^4\),
--
--   which is the antiderivative of \(140t^3(1-t)^3\).  I got this
--   function from <http://shonkwiler.org/ Clayton Shonkwiler>.
--
--   <<diagrams/src_Active_rampDia.svg#diagram=rampDia&width=200>>
--
--   > rampEx :: Active Rational
--   > rampEx = stretch 3 (3 * ramp)
ramp :: Active Rational
ramp = ui <#> \t -> (((-20 * t + 70) * t - 84) * t + 35) * t^(4 :: Integer)

-- > rampDia = illustrateActive' 0.1 [] rampEx


-- | An alternative ramp function based on a portion of a cosine
--   curve; produces spring-like motion.
--
--   <<diagrams/src_Active_cosRampDia.svg#diagram=cosRampDia&width=200>>
--
--   > cosRampEx :: Active Double
--   > cosRampEx = stretch 3 (3 * cosRamp)
cosRamp :: Active Double
cosRamp = ui <#> \t -> (-cos (fromRational t * pi) + 1)/2

-- > cosRampDia = illustrateActive' 0.1 [] cosRampEx


-- | @interval a b@ varies linearly from \( a \) to \( b \) over a
--   duration of \( |a - b| \).  That is, it represents the function \( d \mapsto a + d \)
--   if \( a \leq b \), and \( d \mapsto a - d \) otherwise.
--
--   <<diagrams/src_Active_intervalDia.svg#diagram=intervalDia&width=200>>
--
--   > intervalEx1 :: Active Rational
--   > intervalEx1 = interval 1 4
--
--   <<diagrams/src_Active_intervalDia2.svg#diagram=intervalDia2&width=200>>
--
--   > intervalEx2 :: Active Rational
--   > intervalEx2 = interval 4 2

interval :: Rational -> Rational -> Active Rational
interval a b
  | a <= b    = active (toDuration (b - a)) (a+)
  | otherwise = active (toDuration (a - b)) (a-)

-- > intervalDia  = illustrateActive intervalEx1
-- > intervalDia2 = illustrateActive intervalEx2

-- | The 'interval' from @a@ to @b@ with any @Fractional@ type, provided
--   for convenience.  For an explanation of why this is not the
--   default, see the documentation for 'dur''.
--
--   @interval' a b = 'interval' a b '<#>' fromRational@
interval' :: Fractional d => Rational -> Rational -> Active d
interval' a b = interval a b <#> fromRational

-- | @dur@ is the infinite active value representing the function
--   \( d \mapsto d \).  It is called @dur@ since it can be thought of as
--   representing "the current duration" at any point in time.
--
--   @dur = activeI id@
--
--   <<diagrams/src_Active_durDia.svg#diagram=durDia&width=200>>

dur :: Active Rational
dur = activeI id

-- > durDia = illustrateActive dur

-- | The duration, with any @Fractional@ type, provided for
--   convenience.
--
--   The reason this is not the default is that if the type @d@ ends
--   up being unconstrained, Haskell will default to using @Double@,
--   which can lead to unexpected results due to floating-point error.
--   It's safest to stick to @dur@ unless you know you want a type
--   other than @Rational@ (such as @Double@).
--
--   >>> samples 1 (cut 2 dur)
--   [0 % 1,1 % 1,2 % 1]
--   >>> samples 1 (cut 2 dur')  -- defaults to Double
--   [0.0,1.0,2.0]
--
--   @dur' = 'dur' '<#>' fromRational@
dur' :: Fractional d => Active d
dur' = dur <#> fromRational


infixl 8 <#>

-- | Backwards 'fmap', that is, a synonym for @'flip' ('<$>')@.  This
--   can be useful when starting from some 'Active' like 'ui',
--   'interval', or 'dur', and then applying a function to it. For
--   example:
--
--   @interval 3 5 '<#>' \\t -> circle 1 # translateX t@
--
--   produces a circle translated continuously from 3 to 5 along the
--   x-axis.
--
--   ('<#>') has the same precedence as ('#') from the diagrams
--   library (namely, @infixl 8@) for the same reason: so an 'Active'
--   built via ('<#>') can be combined with others via infix
--   combinators such as 'parI' without needing parentheses, as in the
--   example below.
--
--   <<diagrams/src_Active_pamfDia.svg#diagram=pamfDia&width=200>>
--
--   > pamfEx :: Active (Sum Double)
--   > pamfEx = interval' 0 3 <#> Sum
--   >          `parI`
--   >          (sin'/2) <#> Sum

(<#>) :: Functor f => f a -> (a -> b) -> f b
(<#>) = flip (<$>)

-- > pamfDia = illustrateActive' 0.1 [] . fmap getSum $ pamfEx


-- | Create a "discrete" 'Active' from a nonempty list of values.  The
--   resulting 'Active' has duration 1, and takes on each value from
--   the list in turn for a duration of \(1/n\), where \(n\) is the
--   number of items in the list.  As illustrated below, each interval
--   is "open on the right", that is, at the precise moment when
--   switching from one value to the next, the second value is taken.
--
--   See also 'discrete', which takes a list instead of a 'NonEmpty'
--   for convenience.
--
--   If you want the result to last longer than 1 unit, you can use
--   'stretch'.
--
--   <<diagrams/src_Active_discreteNEDia.svg#diagram=discreteNEDia&width=200>>
--
--   > discreteNEEx :: Active Rational
--   > discreteNEEx = stretch 4 (discreteNE (1 :| [2,3]))

discreteNE :: NonEmpty a -> Active a
discreteNE (a :| as) = (Active 1 f)
  where
    f t
      | t == 1    = V.unsafeLast v
      | otherwise = V.unsafeIndex v $ floor (t * fromIntegral (V.length v))
    v = V.fromList (a:as)

-- > import Data.List.NonEmpty (NonEmpty(..))
-- > discreteNEDia = illustrateActive' (1/2) [(4/3,OC),(8/3,OC)] discreteNEEx


-- | Like 'discreteNE', but with a list for convenience.
--
--   __Partial__: throws an error when applied to the empty list.
--
--   >>> samples 30 (discrete ['a'..'e'])
--   "aaaaaabbbbbbccccccddddddeeeeeee"
discrete :: [a] -> Active a
discrete [] = error "Active.discrete must be called with a non-empty list."
discrete (a : as) = discreteNE (a :| as)


--------------------------------------------------
-- Running/sampling

-- | The semantic function for 'Active': interpret an 'Active' value
--   as a function from durations.  Looked at another way, this is how
--   you can sample an 'Active' value at a given time.
--
--   __Partial__: attempting to evaluate a finite active past its
--   duration, or at a negative time, results in a runtime
--   error. (Unfortunately, in Haskell it would be very difficult to
--   rule this out statically.)  See also 'runActiveMay'.
--
--   >>> let act = movie [lasting 2 "hello", lasting 3 "world"] :: Active String
--   >>> runActive act 1
--   "hello"
--   >>> runActive act 4
--   "world"

runActive :: Active a -> (Rational -> a)
runActive (Active d f) t
  | t < 0
    = error $ "Active.runActive: Active value evaluated at negative time "
              ++ show t
  | otherwise = case compare (Duration t) d of
      GT -> error "Active.runActive: Active value evaluated past its duration."
      _  -> f t

-- | Like 'runActive', but return a total function that returns
--   @Nothing@ when queried outside its range.
--
--   >>> let act = movie [lasting 2 "hello", lasting 3 "world"] :: Active String
--   >>> runActiveMay act 1
--   Just "hello"
--   >>> runActiveMay act 4
--   Just "world"
--   >>> runActiveMay act 6
--   Nothing
--   >>> runActiveMay act (-2)
--   Nothing

runActiveMay :: Active a -> (Rational -> Maybe a)
runActiveMay (Active d f) t
  | t < 0     = Nothing
  | otherwise = case compare (Duration t) d of
      GT -> Nothing
      _  -> Just (f t)

-- | Like 'runActiveMay', but return an 'Option' instead of 'Maybe'.
--   Sometimes this is more convenient since the 'Monoid' instance for
--   'Option' only requires a 'Semigroup' constraint on its type
--   argument.
runActiveOpt :: Active a -> (Rational -> Option a)
runActiveOpt a = Option . runActiveMay a

-- | Test whether an @Active@ is finite.
isFinite :: Active a -> Bool
isFinite (Active Forever _) = False
isFinite _                  = True

-- | Extract the duration of an 'Active' value.  Returns 'Nothing' for
--   infinite values.
--
--   >>> duration (lasting 3 'a')
--   Just (3 % 1)
--   >>> duration (movie [lasting 3 'a', lasting 2 'b'])
--   Just (5 % 1)
--   >>> duration (always 'a')
--   Nothing
duration :: Active a -> Maybe Rational
duration (Active d _) = fromDuration d

-- | (Unsafely) extract the duration of an @Active@ value that you know
--   to be finite.  __Partial__: throws an error if given an infinite
--   argument.
--
--   >>> durationF (lasting 3 'a')
--   3 % 1
durationF :: Active a -> Rational
durationF = fromMaybe (error "Active.durationF called on infinite active") . duration

-- | Extract the value at the beginning of an @Active@.
--
--   >>> start (always 3)
--   3
--   >>> start (omit 2 (stretch 3 dur))
--   2 % 3
start :: Active a -> a
start (Active _ f) = f 0

-- | Extract the value at the end of a finite 'Active'.
--
--   __Partial__: throws an error on infinite actives.  See also
--   'endMay'.
--
--   >>> end (activeF 3 (^2))
--   9 % 1
--   >>> end ui
--   1 % 1
--   >>> end (cut 3 $ movie [lasting 1 'a', lasting 3 'b', lasting 2 'c'])
--   'b'
end :: Active a -> a
end = fromMaybe (error "Active.end called on infinite active") . endMay

-- | A safe, total variant of 'end'; returns the value at the end of a
--   finite @Active@, or @Nothing@ if its argument is infinite.
--
--   >>> endMay (activeF 3 (^2))
--   Just (9 % 1)
--   >>> endMay dur
--   Nothing
endMay :: Active a -> Maybe a
endMay (Active (Duration d) f) = Just $ f d
endMay (Active Forever      _) = Nothing


-- | Generate a list of "frames" or "samples" taken at regular
--   intervals from an 'Active' value.  The first argument is the
--   "frame rate", or number of samples per unit time.  That is,
--   @samples f a@ samples @a@ at times
--   \( 0, \frac 1 f, \frac 2 f, \dots \),
--   ending at the last multiple of \(1/f\) which is /not
--   greater than/ the duration.  The list of samples will be infinite
--   iff the 'Active' is.
--
--   >>> samples 2 (interval 0 3 ^ 2)
--   [0 % 1,1 % 4,1 % 1,9 % 4,4 % 1,25 % 4,9 % 1]
--   >>> samples 1 (lasting 3 ())
--   [(),(),(),()]
--   >>> samples 1 (lasting 2.9 ())
--   [(),(),()]
--
--   Note that @samples 1 (lasting 3 ())@ yields a list of length
--   /four/, not three; this is because the last sample falls exactly
--   on the endpoint:
--
--   <<diagrams/src_Active_samplesDia.svg#diagram=samplesDia&width=200>>

samples :: Rational -> Active a -> [a]
samples 0  _ = error "Active.samples: Frame rate can't equal zero"
samples fr (Active (Duration d) f) = map f . takeWhile (<= d) . map (/fr) $ [0 ..]

  -- We'd like to just say (map f [0, 1/n .. d]) above but that
  -- doesn't work, because of the weird semantics of Enum: the last
  -- element of the list might actually be a bit bigger than d.  For
  -- example, if we replace the above definition with (map f [0, 1/n
  -- .. d]), then samples 1 (lasting 2.9 ()) = [(),(),(),()], whereas
  -- it should have a length of 3.

samples fr (Active Forever      f) = map (f . (/fr)) $ [0 ..]

-- > samplesDia = illustrateActive' (1/2) [(1,CC),(2,CC)] (lasting 3 2)


------------------------------------------------------------
-- Sequential composition
------------------------------------------------------------

-- $seq
--
-- Composing 'Active' values sequentially means placing them
-- end-to-end so one occurs after the other.  The most basic
-- sequential composition operator is ('->-'), which does exactly
-- that.
--
-- The only nuance is what happens at the precise point of overlap
-- (recall that finite 'Active' values are defined on a /closed/
-- interval).  Since durations are rational numbers, we might
-- reasonably sample at a frame rate which evenly divides the
-- durations used in constructing the 'Active', and hence end up
-- sampling precisely on the points of overlap between primitive
-- 'Active' values.
--
-- The answer is that ('->-') requires a 'Semigroup' instance for the
-- type 'a', and when composing @x ->- y@, the value at the end of @x@
-- will be combined with the value at the start of @y@ using ('<>').
-- If @a@ does not have a 'Semigroup' instance, one can, for example,
-- wrap it in 'Last', so that the value from @x@ will be ignored and
-- the value from @y@ taken. In fact, the ('->>') and ('>>-')
-- operators are provided for convenience which handle this common
-- situation; ('->>') uses the starting value from its right-hand
-- argument at the point of overlap, throwing away the ending value
-- from its left-hand argument (using 'Last'); ('>>-') does the
-- converse (using 'First').
--
-- In some situations, when composing active values sequentially, one
-- wants to /accumulate/ the ending values of previous actives and
-- combine them with subsequent ones; this is accomplished with
-- ('-<>-') and 'accumulate'.
--
-- Finite 'Active' values form a semigroup under horizontal
-- composition as long as the value type @a@ is a 'Semigroup';
-- additionally, if @a@ is a 'Monoid', then finite active values are
-- as well, with @'instant' 'mempty'@ as the identity.  However, the
-- 'Semigroup' and 'Monoid' instances for 'Active' are for parallel
-- rather than sequential composition.  The instances with sequential
-- composition are instead defined for the 'Sequential' newtype
-- wrapper.

infixr 4 ->-, ->>, >>-, -<>-

--------------------------------------------------
-- Stitching

-- | \"Stitching\" sequential composition.
--
--   @x ->- y@ is the active which behaves first as @x@, and then as
--   @y@; the total duration is the sum of the durations of @x@ and
--   @y@.  The value of @x ->- y@ at the instant @x@ and @y@ overlap
--   is the composition of @x@ and @y@'s values with respect to the
--   underlying 'Semigroup', that is, they are combined with ('<>').
--
--   If @x@ is infinite, @x ->- y = x@.
--
--   @'instant' 'mempty'@ is the identity for ('->-'),
--   whenever the underlying type is a 'Monoid'.
--
--   See also 'stitchNE' and 'stitch', which combine an entire list of
--   'Active' values using this operator, and the 'Sequential'
--   wrapper, which has 'Semigroup' and 'Monoid' instances
--   corresponding to ('->-').
--
--   <<diagrams/src_Active_seqMDia.svg#diagram=seqMDia&width=200>>
--
--   > seqMEx :: Active (Sum Rational)
--   > seqMEx = interval 0 2 <#> Sum ->- always 3 <#> Sum
--
--   In the above example, the values at the endpoints of the two
--   actives are combined via summing.  This particular example is a
--   bit silly; it is hard to imagine wanting this specific behavior
--   for @Active Rational@ values.  However, here are some examples of
--   cases where stitching sequential composition might be more desirable:
--
--   * Imagine making an animation in which one diagram disappears
--     just as another one appears. We might explicitly want a single
--     frame at the splice point with /both/ diagrams visible (since,
--     /e.g./, this might make the transition look better/more
--     continuous to the human eye).
--
--   * We can use the 'Max' or 'Min' semigroups to automatically pick
--     the larger/smaller of two values at a splice point, no matter
--     whether it comes from the left or the right.
--
--       <<diagrams/src_Active_seqMMaxDia.svg#diagram=seqMMaxDia&width=200>>
--
--       > seqMMaxEx :: Active (Max Rational)
--       > seqMMaxEx = lasting 1 (Max 3) ->- lasting 1 (Max 2) ->- lasting 1 (Max 4)
--
--   More generally, although explicit uses of this combinator may be
--   less common than ('->>') or ('>>-'), it is more fundamental:
--   those combinators are implemented in terms of this one, via the
--   'Last' and 'First' semigroups.

(->-) :: Semigroup a => Active a -> Active a -> Active a
a@(Active Forever _)         ->- _              = a
(Active d1@(Duration n1) f1) ->- (Active d2 f2) = Active (d1 + d2) f
  where
    f n | n <  n1   = f1 n
        | n == n1   = f1 n <> f2 0
        | otherwise = f2 (n - n1)

-- > seqMDia = illustrateActive' (1/4) [(2,OO)] $ getSum <$> seqMEx
-- > seqMMaxDia = illustrateActive' (1/4) [(1,CO),(2,OC)] $ getMax <$> seqMMaxEx


-- | A newtype wrapper for 'Active' values.  The 'Semigroup'
--   and 'Monoid' instances for this wrapper use stitching sequential
--   composition (that is, ('->-')).
newtype Sequential a = Sequential { getSequential :: Active a }

instance Semigroup a => Semigroup (Sequential a) where
  Sequential a1 <> Sequential a2 = Sequential (a1 ->- a2)

instance (Monoid a, Semigroup a) => Monoid (Sequential a) where
  mempty  = Sequential (instant mempty)
  mappend = (<>)
  mconcat [] = mempty
  mconcat ss = Sequential (stitch (coerce ss))


-- | \"Stitch\" a nonempty list of finite actives together, via
--   ('->-'), so values are combined via the 'Semigroup' instance at
--   the splice points.  (See also 'movieNE' and 'stitch'.)  Uses a
--   balanced fold which can make 'samples' more efficient than the
--   usual linear fold.
--
--   <<diagrams/src_Active_stitchDia.svg#diagram=stitchDia&width=200>>
--
--   > import Data.List.NonEmpty (NonEmpty((:|)))
--   > stitchEx :: Active (Max Rational)
--   > stitchEx = stitchNE . fmap (fmap Max . lasting 1) $ 3 :| [1,4,5,2]
stitchNE :: Semigroup a => NonEmpty (Active a) -> Active a
stitchNE = getSequential . foldB1 . coerce


-- | A variant of 'stitchNE' defined on lists instead of 'NonEmpty'.
--
--   @stitch []@ yields @'instant' 'mempty'@, the identity element for
--   ('->-').

stitch :: (Monoid a, Semigroup a) => [Active a] -> Active a
stitch []     = instant mempty
stitch (a:as) = stitchNE (a :| as)

-- > stitchDia = illustrateActive' (1/4) [(1,CO),(2,OC),(3,OC),(4,CO)] $ getMax <$> stitchEx


--------------------------------------------------
-- Movies

-- | Sequential composition, preferring the value from the right-hand
--   argument at the instant of overlap.
--
--   If @x@ is infinite, @x ->> y = x@.
--
--   <<diagrams/src_Active_seqRDia.svg#diagram=seqRDia&width=200>>
--
--   > seqREx :: Active Rational
--   > seqREx = interval 0 2 ->> always 3
--
--   >>> samples 1 (cut 4 (interval 0 2 ->> always 3))
--   [0 % 1,1 % 1,3 % 1,3 % 1,3 % 1]
(->>) :: forall a. Active a -> Active a -> Active a
a1 ->> a2 = coerce ((coerce a1 ->- coerce a2) :: Active (Last a))

-- > seqRDia = illustrateActive' (1/4) [(2,OC)] seqREx


-- | Sequential composition, preferring the value from the left-hand
--   argument at the instant of overlap.
--
--   If @x@ is infinite, @x >>- y = x@.
--
--   <<diagrams/src_Active_seqLDia.svg#diagram=seqLDia&width=200>>
--
--   > seqLEx :: Active Rational
--   > seqLEx = interval 0 2 >>- always 3
--
--   >>> samples 1 (cut 4 (interval 0 2 >>- always 3))
--   [0 % 1,1 % 1,2 % 1,3 % 1,3 % 1]
(>>-) :: forall a. Active a -> Active a -> Active a
a1 >>- a2 = coerce ((coerce a1 ->- coerce a2) :: Active (First a))

-- > seqLDia = illustrateActive' (1/4) [(2,CO)] seqLEx


-- | Make a "movie" out of a nonempty list of finite actives,
--   sequencing them one after another via ('->>'), so the value of
--   the right-hand 'Active' is taken at each splice point.  See also
--   'movie'.
movieNE :: forall a. NonEmpty (Active a) -> Active a
movieNE scenes = coerce (stitchNE (coerce scenes :: NonEmpty (Active (Last a))))


-- | A variant of 'movieNE' defined on lists instead of 'NonEmpty' for
--   convenience.
--
--   __Partial__: @movie []@ throws an error.
--
--   <<diagrams/src_Active_movieDia.svg#diagram=movieDia&width=200>>
--
--   > movieEx :: Active Rational
--   > movieEx = movie [lasting 1 3, lasting 1 2, interval 0 2 # stretch 0.5, lasting 1 4]

movie :: forall a. [Active a] -> Active a
movie []     = error "Active.movie: Can't make empty movie!"
movie (a:as) = coerce (stitchNE (coerce (a :| as) :: NonEmpty (Active (Last a))))

-- > {-# LANGUAGE TupleSections #-}
-- > movieDia = illustrateActive' (1/4) (map (,OC) [1..4]) movieEx


--------------------------------------------------
-- Accumulating

-- | Accumulating sequential composition.
--
--   @x -<>- y@ first behaves as @x@, and then behaves as @y@, except
--   that the final value of @x@ is combined via ('<>') with /every/
--   value from @y@.  So the final value of @x@ "accumulates" into the
--   next @Active@ value being composed.
--
--   If @x@ is infinite, then @x -<>- y = x@.
--
--   @'instant' 'mempty'@ is the identity for ('-<>-'),
--   whenever the underlying type is a 'Monoid'.
--
--   See also 'accumulateNE' and 'accumulate' which perform
--   accumulating sequential composition of a whole list.
--
--   An example of a situation where this is useful is in putting
--   together a sequence of geometric transformations of an object
--   following some path through space.  If we want the object to move
--   right one unit, then move up one unit, and so on, we can achieve
--   this via ('-<>-') (or 'accumulate'): after finishing its
--   rightward motion we don't want it to jump back to the origin and
--   then start moving up; we want the effect of the rightward motion
--   to persist, /i.e./ accumulate into the subsequent translations.
--
--   @x -<>- y = x ->> (('end' x '<>') '<$>' y)@
--
--   <<diagrams/src_Active_seqADia.svg#diagram=seqADia&width=200>>
--
--   > seqAEx :: Active (Sum Rational)
--   > seqAEx = stair -<>- stair -<>- stair
--   >   where
--   >     stair = (ui ->> lasting 0.5 1) <#> Sum
--
--   >>> :m +Data.Ratio
--   >>> let x = active 3 Sum :: Active (Sum Rational)
--   >>> let a1 = x ->- x
--   >>> let a2 = x -<>- x
--   >>> map (numerator . getSum) (samples 1 a1)
--   [0,1,2,3,1,2,3]
--   >>> map (numerator . getSum) (samples 1 a2)
--   [0,1,2,3,4,5,6]
--
(-<>-) :: Semigroup a => Active a -> Active a -> Active a
a@(Active Forever _)         -<>- _              = a
(Active d1@(Duration n1) f1) -<>- (Active d2 f2) = Active (d1 + d2) f
  where
    f n | n < n1    = f1 n
        | otherwise = f1 n1 <> f2 (n - n1)

-- > seqADia = illustrateActive' (0.1) [(1.5,CC),(3,CC)] (getSum <$> seqAEx)


-- | A newtype wrapper for finite 'Active' values.  The 'Semigroup'
--   and 'Monoid' instances for this wrapper use accumulating
--   sequential composition (that is, ('-<>-') rather than parallel
--   composition.
newtype Accumulating a = Accumulating { getAccumulating :: Active a }

instance Semigroup a => Semigroup (Accumulating a) where
  Accumulating a1 <> Accumulating a2 = Accumulating (a1 ->- a2)

instance (Monoid a, Semigroup a) => Monoid (Accumulating a) where
  mempty  = Accumulating (instant mempty)
  mappend = (<>)
  mconcat [] = mempty
  mconcat ss = Accumulating (accumulate (coerce ss))

-- | "Accumulate" a nonempty list of finite actives together in
--   sequence, via ('-<>-'), so the end value from each component
--   'Active' accumulates into the next.  Uses a balanced fold which
--   can make 'samples' more efficient than the usual linear fold.
accumulateNE :: Semigroup a => NonEmpty (Active a) -> Active a
accumulateNE = getAccumulating . foldB1 . coerce

-- | A variant of 'accumulateNE' defined on lists instead of
--   'NonEmpty'. @accumulate []@ yields @'instant' 'mempty'@, the
--   identity element for ('-<>-').
accumulate :: (Semigroup a, Monoid a) => [Active a] -> Active a
accumulate []     = instant mempty
accumulate (a:as) = accumulateNE (a :| as)

------------------------------------------------------------
-- Parallel composition
------------------------------------------------------------

-- $par
--
-- In addition to sequential composition (with one 'Active' following
-- another in time), 'Active'\s also support /parallel/ composition,
-- where two or more 'Active'\s happen simultaneously.  There are two
-- main types of parallel composition, with the difference coming down
-- to how a parallel composition between 'Active'\s of different
-- durations is handled.  /Unioning/ parallel composition ('parU')
-- results in an 'Active' as long as its longest input; conversely,
-- /intersecting/ parallel composition ('parI') results in an 'Active'
-- as long as its shortest input.  In addition, intersecting
-- composition can be generalized to an 'Applicative' instance, which
-- allows applying time-varying functions to time-varying values. Both
-- are provided since they are both useful in different situations,
-- and neither is more general than the other.
--
-- Active values being composed in parallel are all aligned so they
-- have the same starting time.  If you want to offset them in time
-- from each other, you can use 'stackAt', or more fundamentally the
-- 'delay' combinator, when the underlying type is a 'Monoid'; or
-- 'stackAtDef' when the underlying type is a 'Semigroup'.

--------------------------------------------------
-- Unioning parallel composition

-- $union
--
-- Unioning parallel composition composes actives in parallel while
-- "keeping as much information as possible".  This is the natural
-- form of composition to use when putting together many active
-- values, each of which may be defined for only part of the duration
-- of the overall result.
--
-- Unioning parallel composition has many nice advantages over
-- intersecting parallel composition:
--
-- * It keeps as much information as possible.
--
-- * When an identity element exists, it is the same as for sequential stitching
--   composition ('->-') (namely, @'instant' 'mempty'@).
--
-- * It is easy to implement intersecting parallel composition in
--   terms of unioning parallel composition: just compute the minimum
--   duration and use 'cutTo' to make the arguments the same length
--   before composing.  Conversely, it is somewhat unsatisfactory to
--   implement unioning parallel composition in terms of intersecting:
--   one can first pad with 'mempty' to make the arguments the same
--   duration before composing; however, this would require the
--   underlying type to be 'Monoid', and both forms of parallel
--   composition otherwise require only a 'Semigroup'.
--
-- However, despite these advantages, it does not make sense to take
-- unioning parallel composition as primitive and implement
-- intersecting parallel composition in terms of it, because we
-- actually want to generalize intersecting parallel composition to an
-- 'Applicative' instance for 'Active', which cannot be implemented in
-- terms of unioning parallel composition. See the discussion in the
-- section on intersecting composition below.


infixr 6 <∪>
infixr 6 `parU`

-- | Unioning parallel composition.  The duration of @x \`parU\` y@ is
--   the /maximum/ of the durations of @x@ and @y@.  Where they are
--   both defined, the values are combined with ('<>').  Where only
--   one is defined, its value is simply copied.
--
--   @'instant' 'mempty'@ is the identity for 'parU',
--   whenever the underlying type is a 'Monoid'.
--
--   <<diagrams/src_Active_parUDia.svg#diagram=parUDia&width=450>>
--
--   > parUExA, parUExB, parUEx :: Active (Sum Double)
--   > parUExA = interval' 0 3        <#> Sum
--   > parUExB = (1 + cos'/8) # cut 2 <#> Sum
--   >
--   > parUEx  = parUExA `parU` parUExB
--
--   This is the default combining operation for the 'Semigroup' and
--   'Monoid' instances for 'Active', that is, @('<>') = 'parU'@.

parU :: Semigroup a => Active a -> Active a -> Active a
a1@(Active d1 _) `parU` a2@(Active d2 _)
  = Active (d1 `max` d2)
           (\t -> fromJust . getOption $ runActiveOpt a1 t <> runActiveOpt a2 t)
                  -- fromJust is safe since the (Nothing, Nothing) case
                  -- can't happen: at least one of a1 or a2 will be defined everywhere
                  -- on the interval between 0 and the maximum of their durations.

-- > parUDia = drawChain
-- >   [ illustrateActives' 0.1 [[],[]] [parUExA <#> getSum, parUExB <#> getSum]
-- >   , illustrateActive' 0.1 [(2,CO)] (parUEx <#> getSum)
-- >   ]


-- | An infix Unicode synonym for 'parU'.
(<∪>) :: Semigroup a => Active a -> Active a -> Active a
(<∪>) = parU


-- | If @a@ is a 'Semigroup', then @Active a@ forms a 'Semigroup'
--   under unioning parallel composition, that is, @('<>') = 'parU'@.
--   Note that the choice of /which/ semigroup structure to pick for
--   the 'Semigroup' instance is somewhat arbitrary.
instance Semigroup a => Semigroup (Active a) where
  (<>) = parU

-- | If @a@ is a 'Monoid', then @Active a@ forms a 'Monoid' under
--   unioning parallel composition.  The identity element is
--   @'instant' 'mempty'@, the same as the identity element for the
--   sequential composition monoid (see 'Sequential').
instance (Monoid a, Semigroup a) => Monoid (Active a) where
  mempty  = instant mempty
  mappend = (<>)


-- | \"Stack\" a nonempty list of active values via unioning parallel
--   composition.  (This is actually a synonym for 'sconcat'.)
stackNE :: Semigroup a => NonEmpty (Active a) -> Active a
stackNE = sconcat


-- | \"Stack\" a list of active values via unioning parallel
--   composition.  @stack []@ results in @'instant' 'mempty'@, the
--   identity element for 'parU'.
--
--   <<diagrams/src_Active_stackDia.svg#diagram=stackDia&width=450>>
--
--   > stackExArgs :: [Active (Sum Double)]
--   > stackExArgs = map (<#> Sum)
--   >   [ interval' 0 3
--   >   , (1 + cos'/8)       # cut 2
--   >   , (((dur' - 2)/2)^2) # cut 4
--   >   ]
--   >
--   > stackEx :: Active (Sum Double)
--   > stackEx = stack stackExArgs

stack :: (Semigroup a, Monoid a) => [Active a] -> Active a
stack []     = instant mempty
stack (a:as) = stackNE (a :| as)

--   > stackDia = drawChain
--   >   [ illustrateActives' 0.1 [[],[],[]] (map (<#> getSum) stackExArgs)
--   >   , illustrateActive' 0.1 [(2,CO),(3,CO)] (stackEx <#> getSum)
--   >   ]


-- | 'stack' a list of finite actives in parallel, after first
--   offsetting each (via 'delay') by the given duration.  In essence
--   this creates a local context in which one can schedule actives at
--   given "absolute" times (which are nonetheless all relative to the
--   start of the resulting active value).
--
--   <<diagrams/src_Active_stackAtDia.svg#diagram=stackAtDia&width=700>>
--
--   > stackAtEx :: Active (Sum Double)
--   > stackAtEx = stackAt (zip [0, 2, 1/2] stackExArgs)
--
--   @stackAt@ requires the underlying type to be a 'Monoid'.  This is
--   a fundamental limitation, because there must be a default value
--   that can be used even in regions where none of the input actives
--   overlap.  For example, in the below example, 'stackAt' is used to
--   delay the second active past the end of the first, so the
--   resulting parallel composition takes on the value 'mempty' (in
--   this case, 0) on the open interval (2,3).
--
--   <<diagrams/src_Active_stackAtDia2.svg#diagram=stackAtDia2&width=700>>
--
--   > stackAtEx2Args :: [Active (Sum Rational)]
--   > stackAtEx2Args = map (<#> Sum) [ interval 0 2, lasting 2 1 ]
--   >
--   > stackAtEx2 :: Active (Sum Rational)
--   > stackAtEx2 = stackAt (zip [0,3] stackAtEx2Args)
--
--   If you want to use 'stackAt' on actives with an underlying type
--   that is a 'Semigroup' but not a 'Monoid', you have a few options:
--
--   * You can explicitly wrap your underlying values in 'Option',
--     which will turn a 'Semigroup' into a 'Monoid' and use @Option
--     Nothing@ as the default, identity value.
--
--   * You can use the provided 'stackAtDef' function instead, which
--     uses a given default value in place of 'mempty'.

stackAt :: (Monoid a, Semigroup a) => [(Rational, Active a)] -> Active a
stackAt [] = instant mempty
stackAt ps = stack . map (uncurry delay) $ ps

-- > stackAtDia = drawChain
-- >   [ illustrateActives' 0.1 [[],[],[]] args
-- >   , illustrateActives' 0.1 [[],[(2,OC)],[(1/2,OC)]]
-- >                            [a, lasting 2 0 ->> b, lasting (1/2) 0 ->> c]
-- >   , illustrateActive' 0.1 [(1/2, OC), (2, OC), (3, CO), (4, CO)]
-- >       $ getSum <$> stackAtEx
-- >   ]
-- >   where
-- >     args@[a,b,c] = map (<#> getSum) stackExArgs

-- > stackAtDia2 = drawChain
-- >   [ illustrateActives args
-- >   , illustrateActives' (1/2) [[], [(3,OC)]] [a, lasting 3 0 ->> b]
-- >   , illustrateActive'  (1/2) [(2,CO),(3,OC)] $ getSum <$> stackAtEx2
-- >   ]
-- >   where
-- >     args@[a,b] = map (<#> getSum) stackAtEx2Args


-- | Like 'stackAt', but uses the provided default value on intervals
--   where none of the input actives overlap.  This means that only a
--   'Semigroup' instance is required of the underlying type instead
--   of 'Monoid'.
--
--   <<diagrams/src_Active_stackAtDefDia.svg#diagram=stackAtDefDia&width=700>>
--
--   > stackAtDefEx :: Active (Sum Rational)
--   > stackAtDefEx = stackAtDef (Sum (1/2)) (zip [0,3] stackAtEx2Args)

stackAtDef :: Semigroup a => a -> [(Rational, Active a)] -> Active a
stackAtDef a as
  = option a id <$> stackAt ((map . second) (fmap (Option . Just)) as)

-- > stackAtDefDia = drawChain
-- >   [ illustrateActives args
-- >   , illustrateActiveRaw (1/2) [] b # translateX 3 <> illustrateActive a
-- >   , illustrateActive'  (1/2) [(2,CO),(3,OC)] $ getSum <$> stackAtDefEx
-- >   ]
-- >   where
-- >     args@[a,b] = map (<#> getSum) stackAtEx2Args


--------------------------------------------------
-- Intersecting parallel composition

-- $inter
--
-- Another way we can compose actives in parallel is to yield a result
-- that is defined only where /both/ inputs are defined.  One
-- situation in which this is particularly useful is in creating an
-- infinite (perhaps static or repeating) "background" value and then
-- composing it with a finite "foreground" value; the duration of the
-- infinite background will be automatically truncated to match that
-- of the foreground.
--
-- Intersecting parallel composition is also the only reasonable
-- semantics for an 'Applicative' instance: given a time-varying
-- function and a time-varying argument, we can only produce a
-- time-varying result when /both/ function and argument are defined.
--
-- In fact, the 'Applicative' instance for 'Active' can be taken as
-- the most fundamental form of intersecting parallel composition.  It
-- works in much the same way as 'ZipList':
--
-- * @pure :: a -> Active a@ creates an infinite constant.
--
-- * @('<*>') :: Active (a -> b) -> Active a -> Active b@
--   applies a time-varying function to a time-varying
--   argument; the duration of the result is the minimum of the
--   durations of the inputs.
--
-- For example, here is how we can add two time-varying numbers:
--
-- >>> let a = interval 0 3; b = always 2
-- >>> samples 1 ((+) <$> a <*> b)
-- [2 % 1,3 % 1,4 % 1,5 % 1]
--
-- In the example, @a@ is finite and @b@ is infinite; adding them
-- produces a finite result.
--
-- There are also 'Num', 'Fractional', and 'Floating' instances for
-- @Active a@ whenever there is a corresponding instance for @a@;
-- these work by lifting all the operations pointwise, via the
-- 'Applicative' instance.  Using the 'Num' instance, the example
-- given above can be much more simply written as
--
-- >>> let a = interval 0 3; b = always 2
-- >>> samples 1 (a + b)
-- [2 % 1,3 % 1,4 % 1,5 % 1]


-- | @Active@ values with an underlying numeric type can be treated as
--   numeric; all the arithmetic operations are lifted pointwise via
--   the 'Applicative' instance (see also the 'Fractional' and
--   'Floating' instances).  For example, this allows writing things
--   like
--
--   >>> samples 3 (cut 1 (cos (pi * dur' / 2)))
--   [1.0,0.8660254037844387,0.5000000000000001,6.123233995736766e-17]
--
--   rather than the more verbose, but equivalent,
--
--   >>> let a = cos <$> ((*) <$> pure pi <*> ((/) <$> dur' <*> pure 2))
--   >>> samples 3 (cut 1 a)
--   [1.0,0.8660254037844387,0.5000000000000001,6.123233995736766e-17]

instance Num a => Num (Active a) where
  fromInteger = pure . fromInteger
  (+)         = liftA2 (+)
  (*)         = liftA2 (*)
  negate      = fmap negate
  abs         = fmap abs
  signum      = fmap signum

instance Fractional a => Fractional (Active a) where
  fromRational = pure . fromRational
  (/) = liftA2 (/)

instance Floating a => Floating (Active a) where
  pi    = pure pi
  exp   = fmap exp
  log   = fmap log
  sqrt  = fmap sqrt
  (**)  = liftA2 (**)
  sin   = fmap sin
  cos   = fmap cos
  asin  = fmap asin
  acos  = fmap acos
  atan  = fmap atan
  sinh  = fmap sinh
  cosh  = fmap cosh
  asinh = fmap asinh
  acosh = fmap acosh
  atanh = fmap atanh

-- | @'always' x@ creates an infinite 'Active' which is constantly
--   'x'.  Note this is a synonym for 'pure'.
--
--   <<diagrams/src_Active_alwaysDia.svg#diagram=alwaysDia&width=200>>
--
--   > alwaysEx :: Active Rational
--   > alwaysEx = always 2

always :: a -> Active a
always = Active Forever . const

-- > alwaysDia = illustrateActive alwaysEx


-- | @'Active'@ is an 'Applicative' functor, somewhat akin to
--   'ZipList':
--
--   * 'pure' creates an infinite constant value.
--   * @f '<*>' x@ applies @f@ to @x@ pointwise, taking the minimum
--     duration of @f@ and @x@.
instance Applicative Active where
  pure = always
  Active d1 f1 <*> Active d2 f2 = Active (d1 `min` d2) (f1 <*> f2)


infixr 6 `parI`
infixr 6 <∩>

-- | Intersecting parallel composition.  The duration of @x \`parI\`
--   y@ is the /minimum/ of the durations of @x@ and @y@.
--
--   @'always' 'mempty'@ is the identity for 'parI', whenever the
--   underlying type is a 'Monoid'.
--
--   'parI' is often useful for composing infinite "backgrounds" with
--   finite "foregrounds", where we only care about the duration of
--   the foreground and simply want the background to be long enough
--   to match.
--
--   Note that this is a special case of the 'Applicative' instance
--   for 'Active'; in fact, it is equivalent to @'liftA2' ('<>')@.
--
--   @parI = liftA2 (<>)@
--
--   <<diagrams/src_Active_parIDia.svg#diagram=parIDia&width=450>>
--
--   > parIExA, parIExB, parIEx :: Active (Sum Double)
--   > parIExA = interval' 0 3        <#> Sum
--   > parIExB = (1 + cos'/8) # cut 2 <#> Sum
--   >
--   > parIEx = parIExA `parI` parIExB

parI :: Semigroup a => Active a -> Active a -> Active a
parI = liftA2 (<>)

-- > parIDia = drawChain
-- >   [ illustrateActives' 0.1 [[],[]] $ map (<#> getSum) [parIExA, parIExB]
-- >   , illustrateActive' 0.1 [] $ parIEx <#> getSum
-- >   ]


-- | An infix Unicode synonym for 'parI'.
(<∩>) :: Semigroup a => Active a -> Active a -> Active a
(<∩>) = parI

--------------------------------------------------
-- Other combinators

-- | Stretch an active value by a given factor.  For example,
--   @'stretch' 2 a@ is twice as long as @a@ (and hence half as fast).
--   Conversely, @'stretch' (1/2) a@ is half as long as @a@ (twice as
--   fast).  Stretching a finite active by a negative factor also
--   reverses it in time.
--
--   Stretching by a positive factor works perfectly well on infinite
--   active values, despite the fact that it no longer makes sense to
--   say that the result is "x times as long" as the input; it simply
--   stretches out the values in time.
--
--   __Partial__: throws an error if stretching an infinite active by
--   a negative factor, or stretching anything by zero.
--
--   <<diagrams/src_Active_stretchDia.svg#diagram=stretchDia&width=450>>
--
--   > stretchEx :: ActiveF Rational
--   > stretchEx = stretch 3 ui
--
--   >>> samples 1 (stretch 3 ui)
--   [0 % 1,1 % 3,2 % 3,1 % 1]
--   >>> take 4 (samples 1 (stretch (1/2) dur))
--   [0 % 1,2 % 1,4 % 1,6 % 1]
stretch :: Rational -> Active a -> Active a
stretch s a@(Active d f)
  | s < 0 = case isFinite a of
      True  -> stretch (-s) (backwards a)
      False -> error "Active.stretch: negative stretch on infinite active"
  | s == 0 = error "Active.stretch: stretch factor of zero"
  | otherwise = Active (s *^ d) (f . (/s))

-- > stretchDia = illustrateActiveFun (stretch 3) ui


-- | Flip a finite @Active@ value so it runs backwards.
--
--   __Partial__: throws an error on infinite arguments.  See also
--   'backwardsMay'.
--
--   @backwards . backwards = id@
--
--   <<diagrams/src_Active_backwardsDia.svg#diagram=backwardsDia&width=450>>
--
--   > backwardsExArg :: Active Double
--   > backwardsExArg = cut 4 (sin'/3 * dur' + 2)
--   >
--   > backwardsEx :: Active Double
--   > backwardsEx = backwards backwardsExArg

backwards :: Active a -> Active a
backwards
  = fromMaybe (error "Active.backwards called on infinite active")
  . backwardsMay

-- > backwardsDia = illustrateActiveFun' 0.1 [] [] backwards backwardsExArg

-- | A total, safe variant of 'backwards'.  Finite actives are turned
--   backwards; an infinite argument results in @Nothing@.
backwardsMay :: Active a -> Maybe (Active a)
backwardsMay (Active (Duration d) f) = Just $ Active (Duration d) (f . (d-))
backwardsMay _ = Nothing


-- | Stretch the second active so it has the same duration as the
--   first.  If both actives are infinite, do nothing.
--
--   __Partial__: throws an error if one of the arguments is finite
--   and the other infinite.  See also 'matchDurationMay'.
--
--   <<diagrams/src_Active_matchDurationDia.svg#diagram=matchDurationDia&width=450>>
--
--   > mdExA :: Active (Sum Double)
--   > mdExA = interval' 1 3 <#> Sum
--   >
--   > mdExB :: Active (Sum Double)
--   > mdExB = (cos'/3) # cut 5 <#> Sum
--   >
--   > mdEx :: Active (Sum Double)
--   > mdEx = matchDuration mdExA mdExB

matchDuration :: Active a -> Active b -> Active b
matchDuration a b = fromMaybe (error "Active.matchDuration called on arguments of different finitude") $
  matchDurationMay a b

-- > matchDurationDia = drawChain
-- >   [ illustrateActives' 0.1 [[],[]] $ map (<#> getSum) [mdExA, mdExB]
-- >   , illustrateActive' 0.1 [] $ mdEx <#> getSum
-- >   ]


-- | A total, safe variant of 'matchDuration' which returns @Nothing@
--   when given one finite and one infinite argument.
matchDurationMay :: Active a -> Active b -> Maybe (Active b)
matchDurationMay (Active Forever _)       b@(Active Forever _)
  = Just b
matchDurationMay (Active (Duration d1) _) b@(Active (Duration d2) _)
  = Just $ stretch (d1/d2) b
matchDurationMay _ _ = Nothing


-- | Stretch a finite active by whatever factor is required so that it
--   ends up with the given duration.
--
--   __Partial__: throws an error on an infinite active.  See also
--   'stretchToMay'.
--
--   @duration (stretchTo d a) = d@ (when @a@ is finite)
--
--   <<diagrams/src_Active_stretchToDia.svg#diagram=stretchToDia&width=200>>
--
--   > stretchToEx :: Active Rational
--   > stretchToEx = interval 0 3 # stretchTo 5
--
--   >>> duration (stretchTo 5 (interval 0 3))
--   Just (5 % 1)
stretchTo :: Rational -> Active a -> Active a
stretchTo d
  = fromMaybe (error "Active.stretchTo called on infinite active")
  . stretchToMay d

-- > stretchToDia = illustrateActive stretchToEx


-- | A safe, total variant of 'stretchTo'.  Performs 'stretchTo' on a
--   finite argument, and returns @Nothing@ for an infinite argument.
--   For example, if you want to stretch finite actives but leave
--   infinite ones alone, you could write @fromMaybe <*> stretchToMay s@.
stretchToMay :: Rational -> Active a -> Maybe (Active a)
stretchToMay n a@(Active (Duration d) _) = Just $ stretch (n / d) a
stretchToMay _ (Active Forever _)        = Nothing

-- | Take a "snapshot" of a given 'Active' at a particular time,
--   freezing the resulting value into an infinite constant.
--
--   __Partial__: throws an error if given a time outside the duration
--   of the active.
--
--   @snapshot t a = always (runActive a t)@
--
--   <<diagrams/src_Active_snapshotDia.svg#diagram=snapshotDia&width=450>>
--
--   > snapshotExArg :: Active Double
--   > snapshotExArg = cos' + 2
--   >
--   > snapshotEx :: Active Double
--   > snapshotEx = snapshot (9/8) snapshotExArg
--
--   >>> take 3 (samples 1 (snapshot (9/8) cos'))
--   [0.7071067811865477,0.7071067811865477,0.7071067811865477]
snapshot :: Rational -> Active a -> Active a
snapshot t a = always (runActive a t)

-- > snapshotDia = illustrateActiveFun' 0.1 [(9/8,CC)] [] (snapshot (9/8)) snapshotExArg


-- | @cut d a@ cuts the given 'Active' @a@ (which can be finite or
--   infinite) to the specified finite duration @d@.  Has no effect if
--   @a@ is already shorter than @d@.  This is analogous to 'take' on
--   lists.
--
--   @cut d dur = interval 0 d@
--
--   <<diagrams/src_Active_cutDia.svg#diagram=cutDia&width=450>>
--
--   > cutEx :: Active Double
--   > cutEx = cut 1.7 cos'
--
--   >>> samples 1 (cut 2 dur)
--   [0 % 1,1 % 1,2 % 1]
--   >>> samples 1 (cut 3 (interval 0 1))
--   [0 % 1,1 % 1]
cut :: Rational -> Active a -> Active a
cut c (Active d f) = Active (Duration c `min` d) f

-- > cutDia = illustrateActiveFun' 0.1 [] [] (cut 1.7) cos'


-- | @cutTo a1 a2@ 'cut'\s @a2@ to match the duration of @a1@, unless
--   @a2@ is already shorter than @a1@ in which case @cutTo a1 = id@.
cutTo :: Active a -> Active a -> Active a
cutTo a1
  | isFinite a1 = cut (durationF a1)
  | otherwise   = id


-- | @omit d a@ omits the first @d@ time units from @a@. The result is
--   only defined if @d@ is less than or equal to the duration of @a@.
--   This is analogous to 'drop' on lists, except that unlike 'drop',
--   it is partial: there is no "empty @Active@" to serve as the
--   analogue to @[]@.
--
--   __Partial__: throws an error if @d@ is longer than @a@.
--
--   <<diagrams/src_Active_omitDia.svg#diagram=omitDia&width=450>>
--
--   > omitEx :: Active Rational
--   > omitEx = omit 1.3 (interval 0 3)

omit :: Rational -> Active a -> Active a
omit o (Active d f)
  | Duration o > d = error "Active.omit: time to omit longer than the duration of the given active"
  | otherwise = Active (d `subDuration` (Duration o)) (f . (+o))

-- > omitDia = illustrateActiveFun (omit 1.3) (interval 0 3)


-- | @slice s e@ "slices out" a finite portion of an 'Active' starting
--   at time @s@ and ending at time (at most) @e@.  If the start time
--   is greater than the end time, the resulting slice is reversed in
--   time.
--
--   __Partial__: the result is only defined if \( \min(s,e) \leq d \) where
--   \( d \) is the duration of the active.
--
--   @
-- slice s e = cut (e - s) . omit s   (if e >= s)
-- slice s e = backwards . slice e s
--   @
--
--   <<diagrams/src_Active_sliceDia.svg#diagram=sliceDia&width=450>>
--
--   > sliceEx :: Active Rational
--   > sliceEx = slice 1.3 2.8 (interval 0 4)
--
--   <<diagrams/src_Active_sliceDia2.svg#diagram=sliceDia2&width=450>>
--
--   > sliceEx2 :: Active Rational
--   > sliceEx2 = slice 2.8 1.3 (interval 0 4)

slice :: Rational -> Rational -> Active a -> Active a
slice s e a@(Active d _)
  -- Could just defer the error to 'omit', but that might confuse
  -- users who would wonder why they got an error message about 'omit'
  -- even though they never used that function.
  | Duration (min s e) > d = error "Active.slice: starting time greater than the duration of the given active"
  | e >= s    = cut (e - s) . omit s $ a
  | otherwise = backwards . slice e s $ a

-- > sliceDia = illustrateActiveFun (slice 1.3 2.8) (interval 0 4)
-- > sliceDia2 = illustrateActiveFun (slice 2.8 1.3) (interval 0 4)


-- | \"Delay\" an 'Active' by a certain duration, by precomposing it
--   with the given duration of 'mempty'.
--
--   @delay d a = lasting d mempty ->- a@
--
--   <<diagrams/src_Active_delayDia.svg#diagram=delayDia&width=450>>
--
--   > delayExA, delayEx :: Active (Sum Rational)
--   > delayExA = interval 0 2 <#> Sum
--   > delayEx  = delay 1 delayExA

delay :: (Monoid a, Semigroup a) => Rational -> Active a -> Active a
delay d = (lasting d mempty ->-)

-- > delayDia = drawChain
-- >   [ illustrateActiveSum delayExA
-- >   , illustrateActive' (1/2) [(1,CC)] (delayEx <#> getSum)
-- >   ]


--------------------------------------------------

--------------------------------------------------
-- Utilities

-- | A balanced binary fold.
foldB1 :: Semigroup a => NonEmpty a -> a
foldB1 (a :| as) = maybe a (a <>) (foldBM as)
  where
    foldBM :: Semigroup a => [a] -> Maybe a
    foldBM = getOption . foldB (<>) (Option Nothing) . map (Option . Just)

    foldB :: (a -> a -> a) -> a -> [a] -> a
    foldB _   z []   = z
    foldB _   _ [x]  = x
    foldB (&) z xs   = foldB (&) z (pair (&) xs)

    pair _   []         = []
    pair _   [x]        = [x]
    pair (&) (x:y:zs) = (x & y) : pair (&) zs

----------------------------------------------------------------------
-- diagrams-haddock illustrations.  The code is not included in the
-- typeset documentation.
--
-- > import Data.List (intersperse)
-- >
-- > axes :: Diagram B
-- > axes = mconcat
-- >   [ hashes
-- >   , hashes # rotateBy (1/4)
-- >   , arrowV (5.5 *^ unitX)
-- >   , arrowV (5.5 *^ unitY)
-- >   ]
-- >   # lwO 2
-- >   where
-- >     hashes = atPoints (iterateN 5 (translateX 1) (1 ^& 0)) (repeat (vrule 0.15))
-- >
-- > illustrateActiveSum :: RealFrac d => Active (Sum d) -> Diagram B
-- > illustrateActiveSum = illustrateActive . fmap getSum
-- >
-- > illustrateActive :: RealFrac d => Active d -> Diagram B
-- > illustrateActive = illustrateActive' (1/2) []
-- >
-- > type Discontinuity = (Rational, DiscontinuityType)
-- > data DiscontinuityType = OC | CO | OO | CC | N
-- >
-- > illustrateActive' :: RealFrac d => Rational -> [Discontinuity] -> Active d -> Diagram B
-- > illustrateActive' r ds a = illustrateActiveRaw r ds a <> axes
-- >
-- > withActive :: (Active a -> b) -> (Active a -> b) -> Active a -> b
-- > withActive f i a
-- >   | isFinite a = f a
-- >   | otherwise  = i a
-- >
-- > illustrateActiveRaw :: RealFrac d => Rational -> [Discontinuity] -> Active d -> Diagram B
-- > illustrateActiveRaw pd discs = lwO 1 . frame 0.5 . withActive (endPt <> base) base . fmap realToFrac
-- >   where
-- >     endPt act
-- >       = closedPt
-- >         # moveTo (fromRational (durationF act) ^& end act)
-- >     base :: Active Double -> Diagram B
-- >     base act = foldMap drawSegment segments
-- >       where
-- >         portionToIllustrate = act # cut 5.5
-- >         discs' = (0,OC) : discs ++ [(durationF portionToIllustrate, N)]
-- >         segments = zip discs' (tail discs')
-- >         drawSegment ((s,d1), (e,d2)) = mconcat [endpts, spline]
-- >           where
-- >             eps = 1/100
-- >             s' = case d1 of { CO -> s + eps; OO -> s + eps; _ -> s }
-- >             e' = case d2 of { OC -> e - eps; OO -> e - eps; _ -> e }
-- >             act' = slice s' e' act
-- >             spline =
-- >               ( zipWith (^&) (map fromRational [s, s + pd ..]) (samples (1/pd) act')
-- >                 ++ [fromRational e ^& end act']
-- >               )
-- >               # cubicSpline False
-- >               # lc red
-- >             endpts = mconcat
-- >               [ (case d1 of CO -> openPt ; OO -> openPt ; _ -> closedPt)
-- >                   # moveTo (fromRational s ^& start act')
-- >               , (case d2 of N -> mempty ; OC -> openPt ; OO -> openPt ; _ -> closedPt)
-- >                   # moveTo (fromRational e ^& end act')
-- >               , (case d1 of OO -> closedPt ; _ -> mempty)
-- >                   # moveTo (fromRational s ^& runActive act s)
-- >               ]
-- >
-- > illustrateActiveFun :: RealFrac d => (Active d -> Active d) -> Active d -> Diagram B
-- > illustrateActiveFun = illustrateActiveFun' (1/2) [] []
-- >
-- > illustrateActiveFun'
-- >   :: RealFrac d => Rational -> [Discontinuity] -> [Discontinuity]
-- >   -> (Active d -> Active d) -> Active d -> Diagram B
-- > illustrateActiveFun' pd ds1 ds2 f act = drawChain
-- >   [ illustrateActive' pd ds1 act
-- >   , illustrateActive' pd ds2 (f act)
-- >   ]
-- >
-- > drawChain :: [Diagram B] -> Diagram B
-- > drawChain = hsep 1 . intersperse (arrowV (2 *^ unitX) # translateY 2.5)
-- >
-- > closedPt, openPt :: Diagram B
-- > closedPt = circle 0.1 # lw none  # fc red
-- > openPt   = circle 0.1 # lc red   # fc white
-- >

-- > illustrateActives :: RealFrac d => [Active d] -> Diagram B
-- > illustrateActives = beneath axes . foldMap (illustrateActiveRaw (1/2) [])
-- >
-- > illustrateActives' :: RealFrac d => Rational -> [[Discontinuity]] -> [Active d] -> Diagram B
-- > illustrateActives' r dss
-- >   = beneath axes . mconcat
-- >   . zipWith (illustrateActiveRaw r) dss

-- > exampleDia = illustrateActive (interval 0 3 <#> (/2))
