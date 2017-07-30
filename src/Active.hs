{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Active
-- Copyright   :  2011-2017 Brent Yorgey
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  byorgey@gmail.com
--
-- active is a small EDSL for building continuous, time-varying values
-- of arbitrary type. It is particularly useful for building media
-- such as animations, audio clips, and the like, but it is often
-- useful to have other values that vary over time (vectors, colors,
-- filters, volume levels...) and be able to create and use them in
-- the service of constructing time-varying media.
--
-- Some of the important concepts/features of the library include:
--
-- * Every 'Active' value has a /duration/, which is either a
--   nonnegative rational number, or infinity.
-- * An 'Active' value with duration
--   \(d\) can be thought of as a function \([0,d] \to a\), assigning a
--   value to each instant on the closed interval \([0,d]\).
-- * 'Active' values are /time-invariant/, that is, they do not have a
--   fixed, absolute starting time.  Put another way, time is always
--   relative: one can say that `a` should start two seconds after `b`
--   but one cannot say that `a` should start at 2pm on Thursday.
-- * 'Active' values can be composed both in sequence and in parallel,
--   with special attention paid to how underlying values should be
--   composed when there is overlap.
--
-- Throughout this Haddock documentation, various primitive 'Active'
-- values and combinators are illustrated using graphical
-- representations of time-varying numeric values, that is, values of
-- type @Active f d@ for some numeric type @d@.  They are drawn with
-- time increasing along the x-axis and numeric value on the y-axis.
-- For example, the 'Active' of duration 3 which has value \(t/2\) at
-- time \(t\) would be drawn like this:
--
-- <<diagrams/src_Active_exampleDia.svg#diagram=exampleDia&width=200>>
--
-- Some combinators are also illustrated by showing "before" and
-- "after" diagrams, to visualize their effect.  For example, the
-- 'backwards' combinator reverses a finite 'Active' in time; it could
-- be illustrated thus:
--
-- <<diagrams/src_Active_exampleCombDia.svg#diagram=exampleCombDia&width=450>>
--
-- Often, the meaning of combining @Active f a@ values depends on a
-- 'Semigroup' instance for @a@.  Most of the illustrations use the
-- 'Sum' semigroup over the underlying numeric type.  For example, the
-- operation of combining two 'Active' values in parallel is
-- illustrated by adding their respective values:
--
-- <<diagrams/src_Active_parUDia.svg#diagram=parUDia&width=450>>
--
-- The code for producing these diagrams isn't particularly pretty,
-- but you can look at it if you like---just view the source of this
-- module and scroll all the way to the bottom.
--
-----------------------------------------------------------------------------

module Active
  ( -- * Durations
    -- | A few things are re-exported from the "Active.Duration"
    --   module for convenience.

    Finitude(..), Duration(..), toDuration

    -- * The Active type
  , Active, ActF, ActI

    -- * Primitives
  , activeF, activeI, active
  , instant, lasting, always
  , ui, interval, dur
  , sin', cos'
  , (<#>)
  , discreteNE, discrete

    -- * Running/sampling

  , runActive, runActiveMay, runActiveOpt
  , withActive
  , duration, durationF
  , start, end, samples

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

  , IApplicative(..), iliftA2

  , parI, (<∩>)

    -- * Modifying

    -- ** Playing with time
  , backwards, snapshot, delay

    -- ** Stretching

  , stretch, stretch', stretchTo, matchDuration

    -- ** Slicing and dicing
  , cut, omit, slice

  ) where

import           Data.Coerce

import           Data.Bifunctor       (second)
import           Data.List.NonEmpty   (NonEmpty (..))
import qualified Data.List.NonEmpty   as NE
import           Data.Maybe           (fromJust)
import           Data.Semigroup
import qualified Data.Vector          as V
import           Linear.Vector

import           Active.Duration
import           Control.IApplicative


------------------------------------------------------------
--  Active
------------------------------------------------------------

-- | A value of type @Active f a@ is a time-varying value of type
--   @a@ with a given duration.
--
--   * @f@ is an index indicating whether the duration is finite or
--   infinite.
--   * @a@ is the type of the values.
--
--   If the duration is infinite, it can be thought of as a function
--   \( [0,+\infty) \to a \); if it has a finite duration \( d \), it
--   can be thought of as a function \( [0,d] \to a \) (note in
--   particular that the interval is /closed/ on both ends: the
--   function is defined at \(0\) as well as at the duration \(d\)).
--
--   @Active f@ is a @Functor@, and @Active@ is an 'IApplicative'; if
--   @a@ is a 'Semigroup' then @Active f a@ is as well.  @Active I a@
--   is an instance of 'Num', 'Fractional', and 'Floating' as long as
--   there is a corresponding instance for @a@.  These instances are
--   described in much more detail in the sections on sequential and
--   parallel composition below.
--
--   This definition is intentionally abstract, since the
--   implementation may change in the future to enable additional
--   optimizations.
--
--   Semantically, an 'Active' only needs to be defined on the
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

data Active :: Finitude -> * -> * where
  Active   :: Duration f Rational -> (Rational -> a) -> Active f a
  deriving Functor

-- | The type of finite 'Active' values; a convenient synonym for
--   @Active 'F@, so you can use the library without having to turn on
--   @DataKinds@.
type ActF = Active 'F

-- | The type of infinite 'Active' values; a convenient synonym for
--   @Active 'I@, so you can use the library without having to turn on
--   @DataKinds@.
type ActI = Active 'I

--------------------------------------------------
-- Constructing

-- | Smart constructor for finite 'Active' values, given a finite
--   numeric duration \(d\) and a function from \([0,d] \to a\).
--
--   @'activeF' d f = ('cut' d 'dur')    '<#>' f
--            = ('interval' 0 d) '<#>' f@
--
--   In the example below, @activeF 2 (^2)@ constructs the Active
--   value which lasts for 2 time units and takes on the value
--   \( t^2 \) at time \( t \).  Note that an alternative, perhaps more
--   idiomatic way to construct the same value would be @'cut' 2
--   ('dur'^2)@.
--
--   <<diagrams/src_Active_activeFDia.svg#diagram=activeFDia&width=200>>
--
--   > activeFEx :: ActF Rational
--   > activeFEx = activeF 2 (^2)

activeF :: Rational -> (Rational -> a) -> Active 'F a
activeF d = Active (Duration d)

-- > activeFDia = illustrateActive' 0.1 [] activeFEx


-- | Smart constructor for infinite 'Active' values, given a total
--   function of type \(d \to a\) giving a value of type \(a\) at every
--   time.
--
--   <<diagrams/src_Active_activeIDia.svg#diagram=activeIDia&width=200>>
--
--   > activeIEx :: ActI Double
--   > activeIEx = activeI (sqrt . fromRational)
--
--   Since @Active 'I a@ is an instance of 'Floating' whenever @a@ is,
--   @activeI (sqrt . fromRational)@ can alternatively be written as
--   @sqrt (fromRational '<$>' 'dur')@.
activeI :: (Rational -> a) -> Active 'I a
activeI = Active Forever

-- > activeIDia = illustrateActive' 0.1 [] activeIEx


-- | Generic smart constructor for 'Active' values, given a 'Duration'
--   and a function on the appropriate interval.
active :: Duration f Rational -> (Rational -> a) -> Active f a
active = Active


-- | A value of duration zero.
--
--   @'instant' a = 'lasting' 0 a@
--
--   <<diagrams/src_Active_instantDia.svg#diagram=instantDia&width=200>>
--
--   > instantEx :: ActF Rational
--   > instantEx = instant 2

instant :: a -> Active 'F a
instant = lasting 0

-- > instantDia = illustrateActive instantEx


-- | A constant value lasting for the specified duration.
--
-- @'lasting' d = 'activeF' d . const
--          = 'cut' d . always@
--
--   <<diagrams/src_Active_lastingDia.svg#diagram=lastingDia&width=200>>
--
--   > lastingEx :: ActF Rational
--   > lastingEx = lasting 3 2
--
--   This reads particularly nicely when used with postfix function
--   application, a la @(#)@ from the diagrams library.  For example:
--
--   @
-- c :: ActF Char
-- c = movie
--   [ 'a' # lasting 2
--   , 'b' # lasting 3
--   , 'c' # lasting 1
--   ]
-- @
--

lasting :: Rational -> a -> Active 'F a
lasting d = activeF d . const

-- > lastingDia = illustrateActive lastingEx


-- | The unit interval: the identity function on the interval \( [0,1] \).
--
--   <<diagrams/src_Active_uiDia.svg#diagram=uiDia&width=200>>
ui :: Active 'F Rational
ui = active 1 id

-- > uiDia = illustrateActive ui


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

sin' :: Floating n => Active 'I n
sin' = dur <#> \n -> sin (2*pi*fromRational n)

-- > sin'Dia = illustrateActive' 0.1 [] sin'


-- | An infinite cosine wave with a period of @1@, that is,
--   \( d \mapsto \cos(2\pi d) \).   This can be convenient when
--   creating repetitive behavior with a period measured in whole
--   number units.
--
--   <<diagrams/src_Active_cos'Dia.svg#diagram=cos'Dia&width=200>>

cos' :: Floating n => Active 'I n
cos' = dur <#> \n -> cos (2*pi*fromRational n)

-- > cos'Dia = illustrateActive' 0.1 [] cos'


-- | @interval a b@ varies linearly from \( a \) to \( b \) over a
--   duration of \( |a - b| \).  That is, it represents the function \( d \mapsto a + d \)
--   if \( a \leq b \), and \( d \mapsto a - d \) otherwise.
--
--   <<diagrams/src_Active_intervalDia.svg#diagram=intervalDia&width=200>>
--
--   > intervalEx1 :: ActF Rational
--   > intervalEx1 = interval 1 4
--
--   <<diagrams/src_Active_intervalDia2.svg#diagram=intervalDia2&width=200>>
--
--   > intervalEx2 :: ActF Rational
--   > intervalEx2 = interval 4 2

interval :: Rational -> Rational -> Active 'F Rational
interval a b
  | a <= b    = active (toDuration (b - a)) (a+)
  | otherwise = active (toDuration (a - b)) (a-)

-- > intervalDia  = illustrateActive intervalEx1
-- > intervalDia2 = illustrateActive intervalEx2


-- | @dur@ is the infinite active value representing the function
--   \( d \mapsto d \).  It is called @dur@ since it can be thought of as
--   representing "the current duration" at any point in time.
--
--   <<diagrams/src_Active_durDia.svg#diagram=durDia&width=200>>

dur :: Active 'I Rational
dur = active Forever fromRational

-- > durDia = illustrateActive dur


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
--   > pamfEx :: ActF (Sum Double)
--   > pamfEx = interval 0 3 <#> (Sum . fromRational)
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
--   See also 'discrete', which takes a list instead of a 'NonEmpty'.
--
--   If you want the result to last longer than 1 unit, you can use
--   'stretch'.
--
--   <<diagrams/src_Active_discreteNEDia.svg#diagram=discreteNEDia&width=200>>
--
--   > discreteNEEx :: ActF Rational
--   > discreteNEEx = stretch 4 (discreteNE (1 :| [2,3]))

discreteNE :: NonEmpty a -> Active 'F a
discreteNE (a :| as) = (Active 1 f)
  where
    f t
      | t == 1    = V.unsafeLast v
      | otherwise = V.unsafeIndex v $ floor (t * fromIntegral (V.length v))
    v = V.fromList (a:as)

-- > import Data.List.NonEmpty (NonEmpty(..))
-- > discreteNEDia = illustrateActive' (1/2) [(4/3,OC),(8/3,OC)] discreteNEEx


-- | Like 'discreteNE', but with a list for convenience.  Calling
--   'discrete' on the empty list is a runtime error.
--
--   >>> samples 30 (discrete ['a'..'e'])
--   "aaaaaabbbbbbccccccddddddeeeeeee"
discrete :: [a] -> Active 'F a
discrete [] = error "Active.discrete must be called with a non-empty list."
discrete (a : as) = discreteNE (a :| as)


--------------------------------------------------
-- Running/sampling

-- | The semantic function for 'Active': interpret an 'Active' value
--   as a function from durations.  Looked at another way, this is how
--   you can sample an 'Active' value at a given duration.  Note that
--   attempting to evaluate a finite active past its duration results
--   in a runtime error. (Unfortunately, in Haskell it would be very
--   difficult to rule this out statically.)
--
--   >>> let act = movie [lasting 2 "hello", lasting 3 "world"] :: ActF String
--   >>> runActive act 1
--   "hello"
--   >>> runActive act 4
--   "world"

runActive :: Active f a -> (Rational -> a)
runActive (Active d f) t
  = case compareDuration (Duration t') d of
      GT -> error "Active.runActive: Active value evaluated past its duration."
      _  -> f t'
  where
    t' = toRational t

-- | Like 'runActive', but return a total function that returns
--   @Nothing@ when queried outside its range.
--
--   >>> let act = movie [lasting 2 "hello", lasting 3 "world"] :: ActF String
--   >>> runActiveMay act 1
--   Just "hello"
--   >>> runActiveMay act 4
--   Just "world"
--   >>> runActiveMay act 6
--   Nothing

runActiveMay :: Active f a -> (Rational -> Maybe a)
runActiveMay (Active d f) t
  = case compareDuration (Duration t') d of
      GT -> Nothing
      _  -> Just (f t')
  where
    t' = toRational t

-- | Like 'runActiveMay', but return an 'Option' instead of 'Maybe'.
--   Sometimes this is more convenient since the 'Monoid' instance for
--   'Option' only requires a 'Semigroup' constraint on its type
--   argument.
runActiveOpt :: Active f a -> (Rational -> Option a)
runActiveOpt a = Option . runActiveMay a

-- | Do a case analysis on an 'Active' value of unknown finitude,
--   doing one thing if it is finite and another if it is infinite.
--
--   As an example, the @makeFinite@ function defined below leaves the
--   duration of finite actives alone, but cuts infinite actives down
--   to have a default duration of 3.
--
--   >>> let makeFinite :: Active f a -> ActF a; makeFinite = withActive id (cut 3)
--   >>> samples 1 (makeFinite (lasting 7 'a'))
--   "aaaaaaaa"
--   >>> samples 1 (makeFinite (always 'a'))
--   "aaaa"

withActive :: (Active 'F a -> b) -> (Active 'I a -> b) -> Active f a -> b
withActive onFinite onInfinite a@(Active d f) =
  case d of
    Duration _ -> onFinite a
    Forever    -> onInfinite a

-- | Extract the duration of an 'Active' value.  Returns 'Nothing' for
--   infinite values.
--
--   >>> duration (lasting 3 'a')
--   Just (3 % 1)
--   >>> duration (movie [lasting 3 'a', lasting 2 'b'])
--   Just (5 % 1)
--   >>> duration (always 'a')
--   Nothing
duration :: Active f a -> Maybe Rational
duration (Active d _) = fromDuration d

-- | Extract the duration of an 'Active' value that is known to be
--   finite.
--
--   >>> durationF (lasting 3 'a')
--   3 % 1
--   >>> durationF (movie [lasting 3 'a', lasting 2 'b'])
--   5 % 1
durationF :: Active F a -> Rational
durationF (Active d _) = fromDurationF d

-- | Extract the value at the beginning of an 'Active'.
--
--   >>> start (always 3)
--   3
--   >>> start (omit 2 (stretch 3 dur))
--   2 % 3
start :: Active f a -> a
start (Active _ f) = f 0

-- | Extract the value at the end of a finite 'Active'.
--
--   >>> end (activeF 3 (^2))
--   9 % 1
--   >>> end ui
--   1 % 1
--   >>> end (cut 3 $ movie [lasting 1 'a', lasting 3 'b', lasting 2 'c'])
--   'b'

end :: Active 'F a -> a
end (Active (Duration d) f) = f d

-- | Generate a list of "frames" or "samples" taken at regular
--   intervals from an 'Active' value.  The first argument is the
--   "frame rate", or number of samples per unit time.  That is,
--   @samples f a@ samples @a@ at times
--   \( 0, \frac 1 f, \frac 2 f, \dots \),
--   ending at the last multiple of \(1/f\) which is not
--   greater than the duration.  The list of samples will be infinite
--   iff the 'Active' is.
--
--   >>> samples 2 (interval 0 3 <#> (^2))
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

samples :: Rational -> Active f a -> [a]
samples 0  _ = error "Active.samples: Frame rate can't equal zero"
samples fr (Active (Duration d) f) = map f . takeWhile (<= d) . map (/toRational fr) $ [0 ..]

  -- We'd like to just say (map f [0, 1/n .. d]) above but that
  -- doesn't work, because of the weird behavior of Enum with floating
  -- point: the last element of the list might actually be a bit
  -- bigger than d.  This way we also avoid the error that can
  -- accumulate by repeatedly adding 1/n.

samples fr (Active Forever      f) = map (f . (/toRational fr)) $ [0 ..]

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
-- interval).  If one were to use @Double@ values as durations, it
-- probably wouldn't matter what happened at the precise point of
-- overlap, since the probability of sampling at that exact point
-- would be very small.  But since we are using rational durations, it
-- matters quite a bit, since one might reasonably sample at a frame
-- rate which evenly divides the durations used in constructing the
-- 'Active', and hence end up sampling precisely on the points of
-- overlap between primitive 'Active' values.
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

-- | "Stitching" sequential composition.
--
--   @x ->- y@ is the active which behaves first as @x@, and then as
--   @y@; the total duration is the sum of the durations of @x@ and
--   @y@.  The value of @x ->- y@ at the instant @x@ and @y@ overlap
--   is the composition of @x@ and @y@'s values with respect to the
--   underlying 'Semigroup', that is, they are combined with ('<>').
--
--   Note that @x@ must be finite, but @y@ may be infinite.
--
--   See also 'stitchNE' and 'stitch', which combine an entire list of
--   'Active' values using this operator, and the 'Sequential'
--   wrapper, which has 'Semigroup' and 'Monoid' instances
--   corresponding to ('->-').
--
--   <<diagrams/src_Active_seqMDia.svg#diagram=seqMDia&width=200>>
--
--   > seqMEx :: ActI (Sum Rational)
--   > seqMEx = interval 0 2 <#> Sum ->- always 3 <#> Sum
--
--   In the above example, the values at the endpoints of the two
--   actives are combined via summing.  This particular example is a
--   bit silly---it is hard to imagine wanting this behavior.  Here
--   are some examples of cases where this combining behavior might be
--   more desirable:
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
--       > seqMMaxEx :: ActF (Max Rational)
--       > seqMMaxEx = lasting 1 (Max 3) ->- lasting 1 (Max 2) ->- lasting 1 (Max 4)
--
--   More generally, although explicit uses of this combinator may be
--   less common than ('->>') or ('>>-'), it is more fundamental:
--   those combinators are implemented in terms of this one, via the
--   'Last' and 'First' semigroups.

(->-) :: Semigroup a => Active 'F a -> Active f a -> Active f a
(Active d1@(Duration n1) f1) ->- (Active d2 f2) = Active (addDuration d1 d2) f
  where
    f n | n <  n1   = f1 n
        | n == n1   = f1 n <> f2 0
        | otherwise = f2 (n - n1)

-- > seqMDia = illustrateActive' (1/4) [(2,OO)] $ getSum <$> seqMEx
-- > seqMMaxDia = illustrateActive' (1/4) [(1,CO),(2,OC)] $ getMax <$> seqMMaxEx


-- | A newtype wrapper for finite 'Active' values.  The 'Semigroup'
--   and 'Monoid' instances for this wrapper use stitching sequential
--   composition (that is, ('->-')) rather than parallel composition.
newtype Sequential a = Sequential { getSequential :: Active 'F a }

instance Semigroup a => Semigroup (Sequential a) where
  Sequential a1 <> Sequential a2 = Sequential (a1 ->- a2)

instance (Monoid a, Semigroup a) => Monoid (Sequential a) where
  mempty  = Sequential (instant mempty)
  mappend = (<>)
  mconcat [] = mempty
  mconcat ss = Sequential (stitch (coerce ss))


-- | "Stitch" a nonempty list of finite actives together, via ('->-'),
--   so values are combined via the 'Semigroup' instance at the splice
--   points.  (See also 'movieNE' and 'stitch'.)  Uses a balanced fold which can be
--   more efficient than the usual linear fold.
stitchNE :: Semigroup a => NonEmpty (Active 'F a) -> Active 'F a
stitchNE = getSequential . foldB1 . coerce


-- | A variant of 'stitchNE' defined on lists instead of 'NonEmpty'
--   for convenience; @stitch []@ is a runtime error.
--
--   <<diagrams/src_Active_stitchDia.svg#diagram=stitchDia&width=200>>
--
--   > stitchEx :: ActF (Max Rational)
--   > stitchEx = stitch . map (fmap Max . lasting 1) $ [3,1,4,5,2]

stitch :: Semigroup a => [Active 'F a] -> Active 'F a
stitch []     = error "Active.stitch: Can't make empty stitch!"
stitch (a:as) = stitchNE (a :| as)

-- > stitchDia = illustrateActive' (1/4) [(1,CO),(2,OC),(3,OC),(4,CO)] $ getMax <$> stitchEx


--------------------------------------------------
-- Movies

-- | Sequential composition, preferring the value from the right-hand
--   argument at the instant of overlap.
--
--   <<diagrams/src_Active_seqRDia.svg#diagram=seqRDia&width=200>>
--
--   > seqREx :: ActI Rational
--   > seqREx = interval 0 2 ->> always 3
--
--   >>> samples 1 (cut 4 (interval 0 2 ->> always 3))
--   [0 % 1,1 % 1,3 % 1,3 % 1,3 % 1]
(->>) :: forall f a. Active 'F a -> Active f a -> Active f a
a1 ->> a2 = coerce ((coerce a1 ->- coerce a2) :: Active f (Last a))

-- > seqRDia = illustrateActive' (1/4) [(2,OC)] seqREx


-- | Sequential composition, preferring the value from the left-hand
--   argument at the instant of overlap.
--
--   <<diagrams/src_Active_seqLDia.svg#diagram=seqLDia&width=200>>
--
--   > seqLEx :: ActI Rational
--   > seqLEx = interval 0 2 >>- always 3
--
--   >>> samples 1 (cut 4 (interval 0 2 >>- always 3))
--   [0 % 1,1 % 1,2 % 1,3 % 1,3 % 1]
(>>-) :: forall f a. Active 'F a -> Active f a -> Active f a
a1 >>- a2 = coerce ((coerce a1 ->- coerce a2) :: Active f (First a))

-- > seqLDia = illustrateActive' (1/4) [(2,CO)] seqLEx


-- | Make a "movie" out of a nonempty list of finite actives,
--   sequencing them one after another via ('->>'), so the value of
--   the right-hand 'Active' is taken at each splice point.  See also
--   'movie'.
movieNE :: forall a. NonEmpty (Active 'F a) -> Active 'F a
movieNE scenes = coerce (stitchNE (coerce scenes :: NonEmpty (Active 'F (Last a))))


-- | A variant of 'movieNE' defined on lists instead of 'NonEmpty' for
--   convenience; @movie []@ is a runtime error.
--
--   <<diagrams/src_Active_movieDia.svg#diagram=movieDia&width=200>>
--
--   > movieEx :: ActF Rational
--   > movieEx = movie [lasting 1 3, lasting 1 2, interval 0 2 # stretch 0.5, lasting 1 4]

movie :: forall a. [Active 'F a] -> Active 'F a
movie []     = error "Active.movie: Can't make empty movie!"
movie scenes = coerce (stitch (coerce scenes :: [Active 'F (Last a)]))

-- > {-# LANGUAGE TupleSections #-}
-- > movieDia = illustrateActive' (1/4) (map (,OC) [1..4]) movieEx


--------------------------------------------------
-- Accumulating

-- | Accumulating sequential composition.
--
--   @x -<>- y@ first behaves as @x@, and then behaves as @y@, except
--   that the final value of @x@ is combined via ('<>') with /every/
--   value from @y@.  So the final value of @x@ "accumulates" into the
--   next 'Active' value being composed.
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
--   > seqAEx :: ActF (Sum Rational)
--   > seqAEx = stair -<>- stair -<>- stair
--   >   where
--   >     stair = (ui ->> lasting 0.5 1) <#> Sum
--
--   >>> :m +Data.Ratio
--   >>> let x = active 3 Sum :: ActF (Sum Rational)
--   >>> let a1 = x ->- x
--   >>> let a2 = x -<>- x
--   >>> map (numerator . getSum) (samples 1 a1)
--   [0,1,2,3,1,2,3]
--   >>> map (numerator . getSum) (samples 1 a2)
--   [0,1,2,3,4,5,6]
--
(-<>-) :: Semigroup a => Active 'F a -> Active f a -> Active f a
(Active d1@(Duration n1) f1) -<>- (Active d2 f2) = Active (addDuration d1 d2) f
  where
    f n | n < n1    = f1 n
        | otherwise = f1 n1 <> f2 (n - n1)

-- > seqADia = illustrateActive' (0.1) [(1.5,CC),(3,CC)] (getSum <$> seqAEx)


-- | A newtype wrapper for finite 'Active' values.  The 'Semigroup'
--   and 'Monoid' instances for this wrapper use accumulating
--   sequential composition (that is, ('-<>-') rather than parallel
--   composition.
newtype Accumulating a = Accumulating { getAccumulating :: Active 'F a }

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
--   can be more efficient than the usual linear fold.
accumulateNE :: Semigroup a => NonEmpty (Active 'F a) -> Active 'F a
accumulateNE = getAccumulating . foldB1 . coerce

-- | A variant of 'accumulateNE' defined on lists instead of 'NonEmpty'
--   for convenience; @accumulate []@ is a runtime error.
accumulate :: Semigroup a => [Active 'F a] -> Active 'F a
accumulate []     = error "Active.accumulate: Can't accumulate empty list!"
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
--   composition (`->-`) (namely, @instant mempty@).
--
-- * It is easy to implement intersecting parallel composition in
--   terms of unioning parallel composition: just compute the minimum
--   duration and use 'cut' to make the arguments the same length
--   before composing.  Conversely, it is relatively unsatisfactory to
--   implement unioning parallel composition in terms of intersecting:
--   one can first pad with 'mempty' to make the arguments the same
--   duration before composing; however, this would require the
--   underlying type to be 'Monoid', and both forms of parallel
--   composition otherwise require only a 'Semigroup'.
--
-- However, despite these advantages, it does not make sense to take
-- unioning parallel composition as primitive and implement
-- intersecting parallel composition in terms of it, because we want
-- to be able to generalize intersecting parallel composition to an
-- 'Applicative' instance, which cannot be implemented in terms of
-- unioning parallel composition; see the discussion in the section on
-- intersecting composition below.


infixr 6 <∪>
infixr 6 `parU`

-- | Unioning parallel composition.  The duration of @x \`parU\` y@ is
--   the /maximum/ of the durations of @x@ and @y@.  Where they are
--   both defined, the values are combined with ('<>').  Where only
--   one is defined, its value is simply copied.  Notice that 'parU'
--   may be applied to active values of any finitude; the finitude of
--   the result is computed appropriately.
--
--   <<diagrams/src_Active_parUDia.svg#diagram=parUDia&width=450>>
--
--   > parUExA, parUExB, parUEx :: ActF (Sum Double)
--   > parUExA = interval 0 3 <#> fromRational <#> Sum
--   > parUExB = (1 + cos'/8) # cut 2          <#> Sum
--   >
--   > parUEx  = parUExA `parU` parUExB
--
--   This is the default combining operation for the 'Semigroup' and
--   'Monoid' instances for 'Active'.  Note, however, that 'parU' has
--   a strictly more general type than ('<>'), which requires the two
--   arguments to have the same finitude.

parU :: Semigroup a => Active f1 a -> Active f2 a -> Active (f1 ⊔ f2) a
a1@(Active d1 _) `parU` a2@(Active d2 _)
  = Active (d1 `maxDuration` d2)
           (\t -> fromJust . getOption $ runActiveOpt a1 t <> runActiveOpt a2 t)
                  -- fromJust is safe since the (Nothing, Nothing) case
                  -- can't happen: at least one of a1 or a2 will be defined everywhere
                  -- on the interval between 0 and the maximum of their durations.

-- > parUDia = drawChain
-- >   [ illustrateActives' 0.1 [[],[]] [parUExA <#> getSum, parUExB <#> getSum]
-- >   , illustrateActive' 0.1 [(2,CO)] (parUEx <#> getSum)
-- >   ]


-- | An infix Unicode synonym for 'parU'.
(<∪>) :: Semigroup a => Active f1 a -> Active f2 a -> Active (f1 ⊔ f2) a
(<∪>) = parU


-- | If @a@ is a 'Semigroup', then 'Active f a' forms a 'Semigroup'
--   under unioning parallel composition.  Notice that the two
--   arguments of ('<>') are restricted to be either both finite or
--   both infinite; ('parU') is strictly more general since it can
--   combine active values with different finitudes.
instance Semigroup a => Semigroup (Active f a) where
  (<>) = (<∪>)

-- | If @a@ is a 'Monoid', then 'Active F a' forms a 'Monoid' under
--   unioning parallel composition.  The identity element is
--   @'instant' 'mempty'@, the same as the identity element for the
--   sequential composition monoid (see 'Sequential').
instance (Monoid a, Semigroup a) => Monoid (Active 'F a) where
  mempty = instant mempty
  mappend = (<>)


-- | \"Stack\" a nonempty list of active values via unioning parallel
--   composition.  This is actually just a synonym for 'sconcat'.
stackNE :: Semigroup a => NonEmpty (Active f a) -> Active f a
stackNE = sconcat


-- | Like 'stackNE', but on a list for convenience.  Calling 'stack'
--   on the empty list is a runtime error.
--
--   <<diagrams/src_Active_stackDia.svg#diagram=stackDia&width=450>>
--
--   > stackExArgs :: [ActF (Sum Double)]
--   > stackExArgs = map (<#> Sum)
--   >   [ interval 0 3              <#> fromRational
--   >   , (1 + cos'/8)      # cut 2
--   >   , (((dur - 2)/2)^2) # cut 4 <#> fromRational
--   >   ]
--   >
--   > stackEx :: ActF (Sum Double)
--   > stackEx = stack stackExArgs

stack :: Semigroup a => [Active f a] -> Active f a
stack = sconcat . NE.fromList

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
--   > stackAtEx :: ActF (Sum Double)
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
--   > stackAtEx2Args :: [ActF (Sum Rational)]
--   > stackAtEx2Args = map (<#> Sum) [ interval 0 2, lasting 2 1 ]
--   >
--   > stackAtEx2 :: ActF (Sum Rational)
--   > stackAtEx2 = stackAt (zip [0,3] stackAtEx2Args)
--
--   If you want to use 'stackAt' on actives with an underlying type
--   that is not a 'Monoid', you have a few options:
--
--   * You can explicitly wrap your underlying values in 'Option',
--     which will turn a 'Semigroup' into a 'Monoid' and use @Option
--     Nothing@ as the default, identity value.
--
--   * You can use the provided 'stackAtDef' function instead, which
--     uses a given default value in place of 'mempty'.

stackAt :: (Monoid a, Semigroup a) => [(Rational, Active F a)] -> Active F a
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
--   > stackAtDefEx :: ActF (Sum Rational)
--   > stackAtDefEx = stackAtDef (Sum (1/2)) (zip [0,3] stackAtEx2Args)

stackAtDef :: Semigroup a => a -> [(Rational, Active F a)] -> Active F a
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
-- Intersecting parallel composition composes actives in parallel, but
-- the result is defined only where /both/ inputs are defined.  One
-- place this is particularly useful is in creating an infinite
-- (perhaps static or repeating) "background" value and then composing
-- it with a finite "foreground" value.  It is also the only possible
-- semantics for an 'Applicative' instance: given a time-varying
-- function and a time-varying argument, we can only produce a
-- time-varying result when /both/ function and argument are defined.
--
-- However, because of its 'Finitude' type parameter, an actual
-- 'Applicative' instance for 'Active' would be unsatisfactory:
--
-- * There is no way to implement @pure :: a -> Active F a@; the only
--   sensible duration to choose would be 0, but this would not
--   satisfy the 'Applicative' laws.
--
-- * Given this, we could only make an @instance Applicative (Active
--   I)@.  Although this would work, it would be unsatisfactory to be
--   restricted to applying only infinite time-varying functions to
--   infinite time-varying values; we would like to use the
--   @Applicative@ interface to work with finite durations as well.
--
-- In fact, 'Active' is an /indexed applicative functor/, where the
-- applicative structure on active values is mirrored by a /monoidal/
-- structure on the 'Finitude' type indices.  It works in much the
-- same way as 'ZipList', if there were a version of 'ZipList' that
-- tracked finitude at the type level. In particular:
--
-- * @ipure :: a -> Active I a@ creates an infinite constant.
--
-- * @('<:*>') :: Active f1 (a -> b) -> Active f2 a -> Active (f1 ⊓
--   f2) b@ applies a time-varying function to a time-varying
--   argument; the duration of the result is the minimum of the
--   durations of the inputs, and the finitude of the result is
--   computed appropriately at the type level.
--
-- Note that one can still use the normal 'fmap'/('<$>'), since
-- mapping leaves duration unchanged.  For example, here is how we
-- could add two time-varying numbers:
--
-- >>> let a = interval 0 3; b = always 2
-- >>> samples 1 ((+) <$> a <:*> b)
-- [2 % 1,3 % 1,4 % 1,5 % 1]
--
-- In the example, @a@ is finite and @b@ is infinite; adding them
-- produces a finite result.  Instead of writing @(+) \<$\> a \<:*\>
-- b@ we could also have written @'iliftA2' (+) a b@.
--
-- There are 'Num', 'Fractional', and 'Floating' instances for @Active
-- I a@. Unfortunately, we can only have instances for @Active I@, for
-- the same reason that we could only make an 'Applicative' instance
-- for @Active I@; there is no way to implement 'fromInteger' and
-- 'fromRational' for finite actives.  Ideally we would have an @INum@
-- class, parallel to @IApplicative@, but we would lose built-in support
-- for numeric constants.
--
-- At any rate, for infinite values at least, these instances allow us
-- to write things like
--
-- >>> samples 3 (cut 1 (cos (pi * (dur <#> fromRational) / 2)))
-- [1.0,0.8660254037844387,0.5000000000000001,6.123233995736766e-17]
--
-- rather than the more verbose, but equivalent,
--
-- >>> let a = cos <$> ((*) <$> ipure pi <:*> ((/) <$> (dur <#> fromRational) <:*> ipure 2))
-- >>> samples 3 (cut 1 a)
-- [1.0,0.8660254037844387,0.5000000000000001,6.123233995736766e-17]


instance IFunctor Active where
  imap f (Active d1 g) = Active d1 (f . g)

-- | @'Active'@ is an 'IApplicative', somewhat akin to 'ZipList':
--
--   * 'ipure' creates an infinite constant value.
--   * @f '<:*>' x@ applies @f@ to @x@ pointwise, taking the minimum
--     duration of @f@ and @x@.
instance IApplicative Active where
  type Id = 'I
  type (:*:) i j = i ⊓ j
  ipure = always
  Active d1 f1 <:*> Active d2 f2 = Active (d1 `minDuration` d2) (f1 <*> f2)

-- | Infinite 'Active' values can be treated as numeric. (See also the
--   'Fractional' and 'Floating' instances.)  For example, this allows
--   writing things like
--
--   >>> samples 3 (cut 1 (cos (pi * (dur <#> fromRational) / 2)))
--   [1.0,0.8660254037844387,0.5000000000000001,6.123233995736766e-17]
--
--   rather than the more verbose, but equivalent,
--
--   >>> let a = cos <$> ((*) <$> ipure pi <:*> ((/) <$> (dur <#> fromRational) <:*> ipure 2))
--   >>> samples 3 (cut 1 a)
--   [1.0,0.8660254037844387,0.5000000000000001,6.123233995736766e-17]
--
--   Note that it is not possible to have an instance for @Active F@,
--   since there would be no sensible way to implement 'fromInteger'.
--   Ideally we would have an @INum@ class, parallel to
--   'IApplicative', but we would lose built-in support for numeric
--   constants.
instance Num a => Num (Active 'I a) where
  fromInteger = ipure . fromInteger
  (+)         = iliftA2 (+)
  (*)         = iliftA2 (*)
  negate      = fmap negate
  abs         = fmap abs
  signum      = fmap signum

instance Fractional a => Fractional (Active 'I a) where
  fromRational = ipure . fromRational
  (/) = iliftA2 (/)

instance Floating a => Floating (Active 'I a) where
  pi    = ipure pi
  exp   = fmap exp
  log   = fmap log
  sqrt  = fmap sqrt
  (**)  = iliftA2 (**)
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
--   'x'.  Note this is a synonym for 'ipure'.
--
--   <<diagrams/src_Active_alwaysDia.svg#diagram=alwaysDia&width=200>>
--
--   > alwaysEx :: ActI Rational
--   > alwaysEx = always 2

always :: a -> Active 'I a
always = Active Forever . const

-- > alwaysDia = illustrateActive alwaysEx


infixr 6 `parI`
infixr 6 <∩>

-- | Intersecting parallel composition.  The duration of @x \`parI\`
--   y@ is the /minimum/ of the durations of @x@ and @y@.
--
--   This is often useful for composing infinite "backgrounds" with
--   finite "foregrounds", where we only care about the duration of
--   the foreground and simply want the background to be long enough
--   to match.
--
--   Note that this is a special case of the 'IApplicative' instance
--   for 'Active'; in fact, it is equivalent to @'iliftA2' ('<>')@.
--
--   @parI = iliftA2 (<>)@
--
--   <<diagrams/src_Active_parIDia.svg#diagram=parIDia&width=450>>
--
--   > parIExA, parIExB, parIEx :: ActF (Sum Double)
--   > parIExA = interval 0 3 <#> fromRational <#> Sum
--   > parIExB = (1 + cos'/8) # cut 2          <#> Sum
--   >
--   > parIEx = parIExA `parI` parIExB

parI :: Semigroup a => Active f1 a -> Active f2 a -> Active (f1 ⊓ f2) a
parI = iliftA2 (<>)

-- > parIDia = drawChain
-- >   [ illustrateActives' 0.1 [[],[]] $ map (<#> getSum) [parIExA, parIExB]
-- >   , illustrateActive' 0.1 [] $ parIEx <#> getSum
-- >   ]


-- | An infix Unicode synonym for 'parI'.
(<∩>) :: Semigroup a => Active f1 a -> Active f2 a -> Active (f1 ⊓ f2) a
(<∩>) = parI

--------------------------------------------------
-- Other combinators

-- | Do the actual stretching of an 'Active' value by a given positive
--   constant.  Unsafe because it does not check whether the constant
--   is positive.  This is not exported, only used to implement
--   'stretch' and 'stretch''.
unsafeStretch :: Rational -> Active f a -> Active f a
unsafeStretch s (Active d f) = Active (s *^ d) (f . (/s))

-- | Stretch an active value by a positive factor.  For example,
--   @'stretch' 2 a@ is twice as long as @a@ (and hence half as fast).
--   Conversely, @'stretch' (1/2) a@ is half as long as @a@ (twice as
--   fast).
--
--   This actually works perfectly well on infinite active values,
--   despite the fact that it no longer makes sense to say that the
--   result is "x times as long" as the input; it simply stretches out
--   the values in time.
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
stretch :: Rational -> Active f a -> Active f a
stretch s a
  | s <= 0    = error "Active.stretch: Nonpositive stretch factor.  Use stretch' instead."
  | otherwise = unsafeStretch s a

-- > stretchDia = illustrateActiveFun (stretch 3) ui


-- | Like 'stretch', but allows negative stretch factors, which
--   reverse the active.  As a result, it is restricted to only finite
--   actives.
--
--   <<diagrams/src_Active_stretch'Dia.svg#diagram=stretch'Dia&width=450>>
--
--   > stretch'Ex :: ActiveF Rational
--   > stretch'Ex = stretch' (-3) ui
--
--   >>> samples 1 (stretch' (-3) ui)
--   [1 % 1,2 % 3,1 % 3,0 % 1]
stretch' :: Rational -> Active 'F a -> Active 'F a
stretch' s a
  | s > 0     = unsafeStretch s a
  | s < 0     = unsafeStretch (abs s) (backwards a)
  | otherwise = error "Active.stretch': stretch factor of 0"

-- > stretch'Dia = illustrateActiveFun (stretch' (-3)) ui


-- | Flip an 'Active' value so it runs backwards.  For obvious
--   reasons, this only works on finite 'Active'\s.
--
--   @backwards . backwards = id@
--
--   <<diagrams/src_Active_backwardsDia.svg#diagram=backwardsDia&width=450>>
--
--   > backwardsEx :: ActiveF Rational
--   > backwardsEx = backwards (interval 0 3)

backwards :: Active 'F a -> Active 'F a
backwards (Active (Duration d) f) =  Active (Duration d) (f . (d-))

-- > backwardsDia = illustrateActiveFun backwards (interval 0 3)


-- | Stretch the second active so it has the same duration as the
--   first.
--
--   <<diagrams/src_Active_matchDurationDia.svg#diagram=matchDurationDia&width=450>>
--
--   > mdExA :: ActF (Sum Double)
--   > mdExA = movie [ interval 1 3 ] <#> fromRational <#> Sum
--   >
--   > mdExB :: ActF (Sum Double)
--   > mdExB = (cos'/3) # cut 5 <#> Sum
--   >
--   > mdEx :: ActF (Sum Double)
--   > mdEx = matchDuration mdExA mdExB

matchDuration :: Active 'F a -> Active 'F b -> Active 'F b
matchDuration (Active (Duration d1) _) b@(Active (Duration d2) _) = stretch (d1/d2) b

-- > matchDurationDia = drawChain
-- >   [ illustrateActives' 0.1 [[],[]] $ map (<#> getSum) [mdExA, mdExB]
-- >   , illustrateActive' 0.1 [] $ mdEx <#> getSum
-- >   ]


-- | Stretch a finite active by whatever factor is required so that it
--   ends up with the given duration.
--
--   <<diagrams/src_Active_stretchToDia.svg#diagram=stretchToDia&width=200>>
--
--   > stretchToEx :: ActF Rational
--   > stretchToEx = interval 0 3 # stretchTo 5
--
--   >>> durationF (stretchTo 5 (interval 0 3))
--   5 % 1
stretchTo :: Rational -> Active 'F a -> Active 'F a
stretchTo n a@(Active (Duration d) _) = stretch (n / d) a

-- > stretchToDia = illustrateActive stretchToEx


-- | Take a "snapshot" of a given 'Active' at a particular time,
--   freezing the resulting value into an infinite constant.
--
--   @snapshot t a = always (runActive a t)@
--
--   <<diagrams/src_Active_snapshotDia.svg#diagram=snapshotDia&width=450>>
--
--   > snapshotEx :: ActI Double
--   > snapshotEx = snapshot (1/8) cos'
--
--   >>> take 3 (samples 1 (snapshot (9/8) cos'))
--   [0.7071067811865477,0.7071067811865477,0.7071067811865477]
snapshot :: Rational -> Active f a -> Active 'I a
snapshot t a = always (runActive a t)

-- > snapshotDia = illustrateActiveFun' 0.1 [(9/8,CC)] [] (snapshot (1/8)) cos'


-- | @cut d a@ cuts the given 'Active' @a@ (which can be finite or
--   infinite) to the specified finite duration @d@.  Has no effect if
--   @a@ is already shorter than @d@.  This is analogous to 'take' on
--   lists.
--
--   @cut d dur = interval 0 d@
--
--   <<diagrams/src_Active_cutDia.svg#diagram=cutDia&width=450>>
--
--   > cutEx :: ActF Double
--   > cutEx = cut 1.7 cos'
--
--   >>> samples 1 (cut 2 dur)
--   [0 % 1,1 % 1,2 % 1]
--   >>> samples 1 (cut 3 (interval 0 1))
--   [0 % 1,1 % 1]
cut :: Rational -> Active f a -> Active 'F a
cut c (Active d f) = Active (Duration c `minDuration` d) f

-- > cutDia = illustrateActiveFun' 0.1 [] [] (cut 1.7) cos'


-- | @cutTo a1 a2@ cuts @a2@ to match the duration of @a1@, unless
--   @a2@ is already shorter than @a1@ in which case @cutTo a1 = id@.
--
--   @cutTo = cut . durationF@
cutTo :: Active 'F a -> Active f a -> Active 'F a
cutTo = cut . durationF


-- | @omit d a@ omits the first @d@ time units from @a@. The result is
--   only defined if @d@ is less than or equal to the duration of @a@.
--   This is analogous to 'drop' on lists.
--
--   <<diagrams/src_Active_omitDia.svg#diagram=omitDia&width=450>>
--
--   > omitEx :: ActF Rational
--   > omitEx = omit 1.3 (interval 0 3)

omit :: Rational -> Active f a -> Active f a
omit o (Active d f) = Active (d `subDuration` (Duration o)) (f . (+o))

-- > omitDia = illustrateActiveFun (omit 1.3) (interval 0 3)


-- | @slice s e@ "slices out" a finite portion of an 'Active' starting
--   at time @s@ and ending at time @e@.  If the start time is greater
--   than the end time, the resulting slice is reversed in time.  The
--   result is only defined if \( \min(s,e) \leq d \) where \( d \) is
--   the duration of the active.
--
--   @
-- slice s e = cut (e - s) . omit s   (if e >= s)
-- slice s e = backwards . slice e s
--   @
--
--   <<diagrams/src_Active_sliceDia.svg#diagram=sliceDia&width=450>>
--
--   > sliceEx :: ActF Rational
--   > sliceEx = slice 1.3 2.8 (interval 0 4)
--
--   <<diagrams/src_Active_sliceDia2.svg#diagram=sliceDia2&width=450>>
--
--   > sliceEx2 :: ActF Rational
--   > sliceEx2 = slice 2.8 1.3 (interval 0 4)

slice :: Rational -> Rational -> Active f a -> Active 'F a
slice s e
  | e >= s    = cut (e - s) . omit s
  | otherwise = backwards . slice e s

-- > sliceDia = illustrateActiveFun (slice 1.3 2.8) (interval 0 4)
-- > sliceDia2 = illustrateActiveFun (slice 2.8 1.3) (interval 0 4)


-- | "Delay" an 'Active' by a certain duration, by precomposing it
--   with the given duration of 'mempty'. This only makes sense for
--   @Active f a@ values where @a@ is a 'Monoid'.
--
--   @delay d a = lasting d mempty ->- a@
--
--   <<diagrams/src_Active_delayDia.svg#diagram=delayDia&width=450>>
--
--   > delayExA, delayEx :: ActF (Sum Rational)
--   > delayExA = interval 0 2 <#> Sum
--   >
--   > delayEx  = delay 1 delayExA

delay :: (Monoid a, Semigroup a) => Rational -> Active f a -> Active f a
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
-- > illustrateActiveSum :: RealFrac d => Active f (Sum d) -> Diagram B
-- > illustrateActiveSum = illustrateActive . fmap getSum
-- >
-- > illustrateActive :: RealFrac d => Active f d -> Diagram B
-- > illustrateActive = illustrateActive' (1/2) []
-- >
-- > type Discontinuity = (Rational, DiscontinuityType)
-- > data DiscontinuityType = OC | CO | OO | CC | N
-- >
-- > illustrateActive' :: RealFrac d => Rational -> [Discontinuity] -> Active f d -> Diagram B
-- > illustrateActive' r ds a = illustrateActiveRaw r ds a <> axes
-- >
-- > illustrateActiveRaw :: RealFrac d => Rational -> [Discontinuity] -> Active f d -> Diagram B
-- > illustrateActiveRaw pd discs = lwO 1 . frame 0.5 . withActive (endPt <> base) base . fmap realToFrac
-- >   where
-- >     endPt act
-- >       = closedPt
-- >         # moveTo (fromRational (durationF act) ^& end act)
-- >     base :: Active f Double -> Diagram B
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
-- > illustrateActiveFun :: RealFrac d => (Active f d -> Active f2 d) -> Active f d -> Diagram B
-- > illustrateActiveFun = illustrateActiveFun' (1/2) [] []
-- >
-- > illustrateActiveFun'
-- >   :: RealFrac d => Rational -> [Discontinuity] -> [Discontinuity]
-- >   -> (Active f d -> Active f2 d) -> Active f d -> Diagram B
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

-- > illustrateActives :: RealFrac d => [Active f d] -> Diagram B
-- > illustrateActives = beneath axes . foldMap (illustrateActiveRaw (1/2) [])
-- >
-- > illustrateActives' :: RealFrac d => Rational -> [[Discontinuity]] -> [Active f d] -> Diagram B
-- > illustrateActives' r dss
-- >   = beneath axes . mconcat
-- >   . zipWith (illustrateActiveRaw r) dss

-- > exampleDia = illustrateActive (interval 0 3 <#> (/2))
-- > exampleCombDia = illustrateActiveFun backwards (interval 0 3 <#> (/2))
