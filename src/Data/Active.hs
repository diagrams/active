{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE ViewPatterns               #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

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
--
-- There are two basic ways to create an @Active@ value.  The first is
-- to use 'mkActive' to create one directly, by specifying a start and
-- end time and a function of time.  More indirectly, one can use the
-- 'Applicative' instance together with the unit interval 'ui', which
-- takes on values from the unit interval from time 0 to time 1, or
-- 'interval', which creates an active over an arbitrary interval.
--
-- For example, to create a value of type @Active Double@ which
-- represents one period of a sine wave starting at time 0 and ending
-- at time 1, we could write
--
-- > mkActive 0 1 (\t -> sin (fromTime t * tau))
--
-- or
--
-- > (sin . (*tau)) <$> ui
--
-- 'pure' can also be used to create @Active@ values which are
-- constant and have no start or end time.  For example,
--
-- > mod <$> (floor <$> interval 0 100) <*> pure 7
--
-- cycles repeatedly through the numbers 0-6.
--
-- Note that the \"idiom bracket\" notation supported by the SHE
-- preprocessor (<http://personal.cis.strath.ac.uk/~conor/pub/she/>,
-- <http://hackage.haskell.org/package/she>) can make for somewhat
-- more readable 'Applicative' code.  For example, the above example
-- can be rewritten using SHE as
--
-- > {-# OPTIONS_GHC -F -pgmF she #-}
-- >
-- > ... (| mod (| floor (interval 0 100) |) ~7 |)
--
-- There are many functions for transforming and composing active
-- values; see the documentation below for more details.
--
--
-- With careful handling, this module should be suitable to generating
-- deep embeddings if 'Active' values.
--
-----------------------------------------------------------------------------

module Data.Active
       ( -- * Representing time

         -- ** Time and duration

         Time, Clock(..)
       , Duration, Waiting(..)

         -- ** Eras

       , Era, mkEra
       , start, end, duration

         -- * Deadlines

       , Deadline(..)

         -- * Dynamic values
       , Dynamic(..), mkDynamic, onDynamic

       , shiftDynamic
       , transitionDeadline

         -- * Active values
         -- $active
       , Active, mkActive, fromDynamic, isConstant, isDynamic

       , onActive, modActive, runActive

       , activeEra, setEra, atTime

       , activeStart, activeEnd

         -- * Combinators

         -- ** Special active values

       , ui, interval

         -- ** Transforming active values

       , stretch, stretchTo, during
       , shift, backwards

       , snapshot

         -- ** Working with values outside the era
       , clamp, clampBefore, clampAfter
       , trim, trimBefore, trimAfter

         -- ** Composing active values

       , after

       , (->>)

       , (|>>), movie

         -- * Deadlines

         , activeDeadline

         -- * Discretization

       , discrete
       , simulate

       ) where

import           Control.Applicative
import           Control.Arrow       ((&&&))
import           Control.Lens        hiding (backwards, (<.>))

import           Data.Functor.Apply
import           Data.Semigroup      hiding (First (..))
import qualified Data.Vector         as V

import           Linear
import           Linear.Affine


------------------------------------------------------------
-- Clock
------------------------------------------------------------
-- | A class that abstracts over time.

class (Affine t, Waiting (Diff t)) => Clock t where

  -- | Convert any value of a 'Real' type (including @Int@, @Integer@,
  --   @n@, @Float@, and @Double@) to a 'Time'.
  toTime :: (Real a, Fractional n) => a -> t n

  -- | Convert a 'Time' to a value of any 'Fractional' type (such as
  --   @n@, @Float@, or @Double@).
  fromTime :: (Real n, Fractional a) => t n -> a

  firstTime :: Ord n => t n -> t n -> t n
  lastTime  :: Ord n => t n -> t n -> t n

class Additive w => Waiting w where
  -- | Convert any value of a 'Real' type (including @Int@, @Integer@,
  --   @n@, @Float@, and @Double@) to a 'Duration'.
  toDuration :: (Real a, Fractional n) => a -> w n

  -- | Convert a 'Duration' to any other 'Fractional' type (such as
  --   @n@, @Float@, or @Double@).
  -- fromDuration :: (FractionalOf w a) => w -> a
  fromDuration :: (Real n, Fractional a) => w n -> a

toFractional :: (Real a, Fractional c) => a -> c
toFractional = fromRational . toRational

class Clock t => Deadline t a where
  -- choose time-now deadline-time (if before / at deadline) (if after deadline)
  choose :: Ord n => t n -> t n -> a -> a -> a

------------------------------------------------------------
-- Time
------------------------------------------------------------

-- | An abstract type for representing /points in time/.  Note that
--   literal numeric values may be used as @Time@s, thanks to the the
--   'Num' and 'Fractional' instances.  'toTime' and 'fromTime' are
--   also provided for convenience in converting between @Time@ and
--   other numeric types.
newtype Time n = Time n
  deriving (Eq, Ord, Show, Read, Enum, Num, Fractional, Real, RealFrac)

makeWrapped ''Time

instance Affine Time where
  type Diff Time = Duration
  (Time t1) .-. (Time t2) = Duration (t1 - t2)
  (Time t) .+^ (Duration d) = Time (t + d)

instance Clock Time where
  toTime    = fromRational . toRational
  fromTime  = fromRational . toRational
  firstTime = min
  lastTime  = max

instance Deadline Time a where
  -- choose tm deadline (if before / at deadline) (if after deadline)
  choose t1 t2 a b = if t1 <= t2 then a else b

-- | An abstract type representing /elapsed time/ between two points
--   in time.  Note that durations can be negative. Literal numeric
--   values may be used as @Duration@s thanks to the 'Num' and
--   'Fractional' instances. 'toDuration' and 'fromDuration' are also
--   provided for convenience in converting between @Duration@s and
--   other numeric types.
newtype Duration n = Duration n
  deriving (Eq, Ord, Show, Read, Enum, Num, Fractional, Real, RealFrac, Functor)

makeWrapped ''Duration

instance Applicative Duration where
  pure = Duration
  Duration f <*> Duration x = Duration (f x)

instance Additive Duration where
  zero = 0

instance Num n => Semigroup (Duration n) where
  (<>) = (^+^)

instance Num n => Monoid (Duration n) where
  mappend = (<>)
  mempty  = 0

instance Waiting Duration where
  toDuration = fromRational . toRational
  fromDuration = fromRational . toRational

-- | An @Era@ is a concrete span of time, that is, a pair of times
--   representing the start and end of the era. @Era@s form a
--   semigroup: the combination of two @Era@s is the smallest @Era@
--   which contains both.  They do not form a 'Monoid', since there is
--   no @Era@ which acts as the identity with respect to this
--   combining operation.
--
--   @Era@ is abstract. To construct @Era@ values, use 'mkEra'; to
--   deconstruct, use 'start' and 'end'.
newtype Era t n = Era (Min (t n), Max (t n))
  deriving Show

-- AJG: I explicitly implement this to make sure we use min and max,
-- and not compare (which does not reify into a deep embedded structure).
instance (Clock t, Ord n) => Semigroup (Era t n) where
  Era (Min min1, Max max1) <> Era (Min min2, Max max2)
    = Era (Min (firstTime min1 min2), Max (lastTime max1 max2))

-- | Create an 'Era' by specifying start and end 'Time's.
mkEra :: t n -> t n -> Era t n
mkEra s e = Era (Min s, Max e)

-- | Get the start 'Time' of an 'Era'.
start :: Era t n -> t n
start (Era (Min t, _)) = t

-- | Get the end 'Time' of an 'Era'.
end :: Era t n -> t n
end (Era (_, Max t)) = t

-- | Compute the 'Duration' of an 'Era'.
duration :: (Clock t, Num n) => Era t n -> Diff t n
duration = (.-.) <$> end <*> start

------------------------------------------------------------
-- Dynamic
------------------------------------------------------------

-- | A @Dynamic a@ can be thought of as an @a@ value that changes over
--   the course of a particular 'Era'.  It's envisioned that @Dynamic@
--   will be mostly an internal implementation detail and that
--   'Active' will be most commonly used.  But you never know what
--   uses people might find for things.

data Dynamic t n a = Dynamic { era        :: Era t n
                             , runDynamic :: t n -> a
                             }
  deriving Functor

-- | 'Dynamic' is an instance of 'Apply' (/i.e./ 'Applicative' without
--   'pure'): a time-varying function is applied to a time-varying
--   value pointwise; the era of the result is the combination of the
--   function and value eras.  Note, however, that 'Dynamic' is /not/
--   an instance of 'Applicative' since there is no way to implement
--   'pure': the era would have to be empty, but there is no such
--   thing as an empty era (that is, 'Era' is not an instance of
--   'Monoid').

instance (Clock t, Ord n) => Apply (Dynamic t n) where
  (Dynamic d1 f1) <.> (Dynamic d2 f2) = Dynamic (d1 <> d2) (f1 <.> f2)

-- | @'Dynamic' a@ is a 'Semigroup' whenever @a@ is: the eras are
--   combined according to their semigroup structure, and the values
--   of type @a@ are combined pointwise.  Note that @'Dynamic' a@ cannot
--   be an instance of 'Monoid' since 'Era' is not.
instance (Clock t, Ord n, Semigroup a) => Semigroup (Dynamic t n a) where
  Dynamic d1 f1 <> Dynamic d2 f2 = Dynamic (d1 <> d2) (f1 <> f2)

-- | Create a 'Dynamic' from a start time, an end time, and a
--   time-varying value.
mkDynamic :: t n -> t n -> (t n -> a) -> Dynamic t n a
mkDynamic s e = Dynamic (mkEra s e)

-- | Fold for 'Dynamic'.
onDynamic :: (t n -> t n -> (t n -> a) -> b) -> Dynamic t n a -> b
onDynamic f (Dynamic e d) = f (start e) (end e) d

-- | Shift a 'Dynamic' value by a certain duration.
shiftDynamic :: (Clock t, Num n) => Diff t n -> Dynamic t n a -> Dynamic t n a
shiftDynamic sh =
  onDynamic $ \s e d ->
    mkDynamic
      (s .+^ sh)
      (e .+^ sh)
      (\t -> d (t .-^ sh))

-- | take the first value until a deadline, then take the second value, inside a Dynamic.
transitionDeadline :: (Deadline t a, Ord n) => t n -> Dynamic t n (a -> a -> a)
transitionDeadline dl = mkDynamic dl dl (`choose` dl)

------------------------------------------------------------
--  Active
------------------------------------------------------------

-- $active
-- For working with time-varying values, it is convenient to have an
-- 'Applicative' instance: '<*>' lets us apply time-varying
-- functions to time-varying values; 'pure' allows treating constants
-- as time-varying values which do not vary.  However, as explained in
-- its documentation, 'Dynamic' cannot be made an instance of
-- 'Applicative' since there is no way to implement 'pure'.  The
-- problem is that all 'Dynamic' values must have a finite start and
-- end time.  The solution is to adjoin a special constructor for
-- pure/constant values with no start or end time, giving us 'Active'.

-- | There are two types of @Active@ values:
--
--   * An 'Active' can simply be a 'Dynamic', that is, a time-varying
--     value with start and end times.
--
--   * An 'Active' value can also be a constant: a single value,
--     constant across time, with no start and end times.
--
--   The addition of constant values enable 'Monoid' and 'Applicative'
--   instances for 'Active'.
newtype Active t n a = Active (MaybeApply (Dynamic t n) a)
  deriving (Functor, Apply, Applicative)

makeWrapped ''Active
makeWrapped ''MaybeApply

active :: Iso' (Active t n a) (Either (Dynamic t n a) a)
active = _Wrapped . _Wrapped

-- | Active values over a type with a 'Semigroup' instance are also an
--   instance of 'Semigroup'.  Two active values are combined
--   pointwise; the resulting value is constant iff both inputs are.
instance (Clock t, Ord n, Semigroup a) => Semigroup (Active t n a) where
  (view active -> a) <> (view active -> b) = review active $ combine a b
   where
     combine (Right m1) (Right m2)
       = Right (m1 <> m2)

     combine (Left (Dynamic dur f)) (Right m)
       = Left (Dynamic dur (f <> const m))

     combine (Right m) (Left (Dynamic dur f))
       = Left (Dynamic dur (const m <> f))

     combine (Left d1) (Left d2)
       = Left (d1 <> d2)

instance (Clock t, Ord n, Monoid a, Semigroup a) => Monoid (Active t n a) where
  mempty  = Active (MaybeApply (Right mempty))
  mappend = (<>)

-- | Create an 'Active' value from a 'Dynamic'.
fromDynamic :: Dynamic t n a -> Active t n a
fromDynamic = Active . MaybeApply . Left

-- | Create a dynamic 'Active' from a start time, an end time, and a
--   time-varying value.
mkActive :: t n -> t n -> (t n -> a) -> Active t n a
mkActive s e f = fromDynamic (mkDynamic s e f)

-- | Fold for 'Active's.  Process an 'Active a', given a function to
--   apply if it is a pure (constant) value, and a function to apply if
--   it is a 'Dynamic'.
onActive :: (a -> b) -> (Dynamic t n a -> b) -> Active t n a -> b
onActive f _ (Active (MaybeApply (Right a))) = f a
onActive _ f (Active (MaybeApply (Left d)))  = f d

-- | Modify an 'Active' value using a case analysis to see whether it
--   is constant or dynamic.
modActive :: (Clock t, Ord n)
  => (a -> b)
  -> (Dynamic t n a -> Dynamic t n b)
  -> Active t n a -> Active t n b
modActive f g = onActive (pure . f) (fromDynamic . g)

-- | Interpret an 'Active' value as a function from time.
runActive :: Active t n a -> t n -> a
runActive = onActive const runDynamic

-- | Get the value of an @Active a@ at the beginning of its era.
activeStart :: Active t n a -> a
activeStart = onActive id (onDynamic $ \s _ d -> d s)

-- | Get the value of an @Active a@ at the end of its era.
activeEnd :: Active t n a -> a
activeEnd = onActive id (onDynamic $ \_ e d -> d e)

-- | Get the 'Era' of an 'Active' value (or 'Nothing' if it is
--   a constant/pure value).
activeEra :: Active t n a -> Maybe (Era t n)
activeEra = onActive (const Nothing) (Just . era)

-- | Test whether an 'Active' value is constant.
isConstant :: Active t n a -> Bool
isConstant = onActive (const True) (const False)

-- | Test whether an 'Active' value is 'Dynamic'.
isDynamic :: Active t n a -> Bool
isDynamic = onActive (const False) (const True)

-- | take the first value until a deadline, then take the second value, inside an 'Active'.
activeDeadline :: (Ord n, Deadline t a) => t n -> Active t n (a -> a -> a)
activeDeadline = fromDynamic . transitionDeadline

------------------------------------------------------------
--  Combinators
------------------------------------------------------------

-- | @ui@ represents the /unit interval/, which takes on the value @t@
--   at time @t@, and has as its era @[0,1]@. It is equivalent to
--   @'interval' 0 1@, and can be visualized as follows:
--
--   <<http://www.cis.upenn.edu/~byorgey/hosted/ui.png>>
--
--   On the x-axis is time, and the value that @ui@ takes on is on the
--   y-axis.  The shaded portion represents the era.  Note that the
--   value of @ui@ (as with any active) is still defined outside its
--   era, and this can make a difference when it is combined with
--   other active values with different eras.  Applying a function
--   with 'fmap' affects all values, both inside and outside the era.
--   To manipulate values outside the era specifically, see 'clamp'
--   and 'trim'.
--
--   To alter the /values/ that @ui@ takes on without altering its
--   era, use its 'Functor' and 'Applicative' instances.  For example,
--   @(*2) \<$\> ui@ varies from @0@ to @2@ over the era @[0,1]@.  To
--   alter the era, you can use 'stretch' or 'shift'.
-- TODO: Num=>Clock
ui :: (Clock t, Real n, Fractional n, Fractional a) => Active t n a
ui = interval (toTime (0 :: Integer)) (toTime (1 :: Integer))

-- | @interval a b@ is an active value starting at time @a@, ending at
--   time @b@, and taking the value @t@ at time @t@.
interval :: (Clock t, Real n, Fractional a) => t n -> t n -> Active t n a
interval a b = mkActive a b fromTime

-- | @stretch s act@ \"stretches\" the active @act@ so that it takes
--   @s@ times as long (retaining the same start time).
stretch :: (Clock t, Real n, Fractional n) => n -> Active t n a -> Active t n a
stretch 0 = modActive id . onDynamic $ \s _ d -> mkDynamic s s d
stretch str = modActive id . onDynamic $ \s e d ->
    mkDynamic s (s .+^ (toFractional str *^ (e .-. s)))
      (\t -> d (s .+^ ((t .-. s) ^/ toFractional str)))

-- | @stretchTo d@ 'stretch'es an 'Active' so it has duration @d@.
--   Has no effect if (1) @d@ is non-positive, or (2) the 'Active'
--   value is constant, or (3) the 'Active' value has zero duration.
-- [AJG: conditions (1) and (3) no longer true: to consider changing]

stretchTo :: (Fractional n, Real n, Deadline t a) => Diff t n -> Active t n a -> Active t n a
stretchTo toD = modActive id . onDynamic $ \s e d ->
    mkDynamic s (s .+^ toD)
        (\ t -> choose (s .+^ toD) s
                     (d s)      -- avoiding dividing by zero
                     (d (s .+^ ((t .-. s) ^/ (fromDuration toD / fromDuration (e .-. s))))))

-- | @a1 \`during\` a2@ 'stretch'es and 'shift's @a1@ so that it has the
--   same era as @a2@.  Has no effect if either of @a1@ or @a2@ are constant.
during :: (Fractional n, Real n, Deadline t a) => Active t n a -> Active t n a -> Active t n a
during a1 a2 = maybe a1 (\(d,s) -> stretchTo d . atTime s $ a1)
                 ((duration &&& start) <$> activeEra a2)

-- | @shift d act@ shifts the start time of @act@ by duration @d@.
--   Has no effect on constant values.
shift :: (Clock t, Ord n, Num n) => Diff t n -> Active t n a -> Active t n a
shift sh = modActive id (shiftDynamic sh)

-- | Reverse an active value so the start of its era gets mapped to
--   the end and vice versa.  For example, @backwards 'ui'@ can be
--   visualized as
--
--   <<http://www.cis.upenn.edu/~byorgey/hosted/backwards.png>>
backwards :: (Clock t, Ord n, Num n) => Active t n a -> Active t n a
backwards =
  modActive id . onDynamic $ \s e d ->
    mkDynamic s e
      (\t -> d (s .+^ (e .-. t)))


-- | Take a \"snapshot\" of an active value at a particular time,
--   resulting in a constant value.
snapshot :: (Clock t, Ord n) => t n -> Active t n a -> Active t n a
snapshot t a = pure (runActive a t)

-- | \"Clamp\" an active value so that it is constant before and after
--   its era.  Before the era, @clamp a@ takes on the value of @a@ at
--   the start of the era.  Likewise, after the era, @clamp a@ takes
--   on the value of @a@ at the end of the era. @clamp@ has no effect
--   on constant values.
--
--   For example, @clamp 'ui'@ can be visualized as
--
--   <<http://www.cis.upenn.edu/~byorgey/hosted/clamp.png>>
--
--   See also 'clampBefore' and 'clampAfter', which clamp only before
--   or after the era, respectively.

clamp :: (Clock t, Ord n) => Active t n a -> Active t n a
clamp =
  modActive id . onDynamic $ \s e d ->
    mkDynamic s e
      (\t -> d (firstTime (lastTime t s) e))

-- | \"Clamp\" an active value so that it is constant before the start
--   of its era. For example, @clampBefore 'ui'@ can be visualized as
--
--   <<http://www.cis.upenn.edu/~byorgey/hosted/clampBefore.png>>
--
--   See the documentation of 'clamp' for more information.
clampBefore :: Active t n a -> Active t n a
clampBefore = undefined

--- XXX These are undefined!

-- | \"Clamp\" an active value so that it is constant after the end
--   of its era.  For example, @clampBefore 'ui'@ can be visualized as
--
--   <<http://www.cis.upenn.edu/~byorgey/hosted/clampAfter.png>>
--
--   See the documentation of 'clamp' for more information.
clampAfter :: Active t n a -> Active t n a
clampAfter = undefined


-- | \"Trim\" an active value so that it is empty outside its era.
--   @trim@ has no effect on constant values.
--
--   For example, @trim 'ui'@ can be visualized as
--
--   <<http://www.cis.upenn.edu/~byorgey/hosted/trim.png>>
--
--   Actually, @trim ui@ is not well-typed, since it is not guaranteed
--   that @ui@'s values will be monoidal (and usually they won't be)!
--   But the above image still provides a good intuitive idea of what
--   @trim@ is doing. To make this precise we could consider something
--   like @trim (First . Just <$> ui)@.
--
--   See also 'trimBefore' and 'trimActive', which trim only before or
--   after the era, respectively.

trim :: (Clock t, Ord n, Deadline t a, Monoid a) => Active t n a -> Active t n a
trim =
  modActive id . onDynamic $ \s e d ->
    mkDynamic s e
      (\t -> choose s t (choose t e (d t) mempty) mempty)


-- | \"Trim\" an active value so that it is empty /before/ the start
--   of its era. For example, @trimBefore 'ui'@ can be visualized as
--
--   <<http://www.cis.upenn.edu/~byorgey/hosted/trimBefore.png>>
--
--   See the documentation of 'trim' for more details.
trimBefore :: (Clock t, Ord n, Deadline t a, Monoid a) => Active t n a -> Active t n a
trimBefore =
  modActive id . onDynamic $ \s e d ->
    mkDynamic s e
      (\t -> choose s t (d t) mempty)

-- | \"Trim\" an active value so that it is empty /after/ the end
--   of its era.  For example, @trimAfter 'ui'@ can be visualized as
--
--   <<http://www.cis.upenn.edu/~byorgey/hosted/trimAfter.png>>
--
--   See the documentation of 'trim' for more details.
trimAfter :: (Clock t, Ord n, Deadline t a, Monoid a) => Active t n a -> Active t n a
trimAfter =
  modActive id . onDynamic $ \s e d ->
    mkDynamic s e
      (\t -> choose t e (d t) mempty)

-- | Set the era of an 'Active' value.  Note that this will change a
--   constant 'Active' into a dynamic one which happens to have the
--   same value at all times.
setEra :: Era t n -> Active t n a -> Active t n a
setEra er =
  onActive
    (mkActive (start er) (end er) . const)
    (fromDynamic . onDynamic (\_ _ -> mkDynamic (start er) (end er)))

-- | @atTime t a@ is an active value with the same behavior as @a@,
--   shifted so that it starts at time @t@.  If @a@ is constant it is
--   returned unchanged.
atTime :: (Clock t, Num n, Ord n) => t n -> Active t n a -> Active t n a
atTime t a = maybe a (\e -> shift (t .-. start e) a) (activeEra a)

-- | @a1 \`after\` a2@ produces an active that behaves like @a1@ but is
--   shifted to start at the end time of @a2@.  If either @a1@ or @a2@
--   are constant, @a1@ is returned unchanged.
after :: (Clock t, Num n, Ord n) => Active t n a -> Active t n a -> Active t n a
after a1 a2 = maybe a1 ((`atTime` a1) . end) (activeEra a2)

infixr 5 ->>


-- XXX illustrate

-- | Sequence/overlay two 'Active' values: shift the second to start
--   immediately after the first (using 'after'), then compose them
--   (using '<>').
(->>) :: (Clock t, Num n, Ord n, Semigroup a) => Active t n a -> Active t n a -> Active t n a
a1 ->> a2 = a1 <> (a2 `after` a1)


-- XXX illustrate

-- | \"Splice\" two 'Active' values together: shift the second to
--   start immediately after the first (using 'after'), and produce
--   the value which acts like the first up to the common end/start
--   point, then like the second after that.  If both are constant,
--   return the first.
(|>>) :: (Ord n, Num n, Deadline t a) => Active t n a -> Active t n a -> Active t n a
a1 |>> a2 = onActive pure (\ d1 ->
                activeDeadline (end (era d1))
                        <.> a1
                        <.> (a2 `after` a1)
          ) a1

-- XXX implement 'movie' with a balanced fold

-- | Splice together a list of active values using '|>>'.  The list
--   must be nonempty.
movie :: (Ord n, Num n, Deadline t a) => [Active t n a] -> Active t n a
movie = foldr1 (|>>)


------------------------------------------------------------
--  Discretization
------------------------------------------------------------

-- | Create an @Active@ which takes on each value in the given list in
--   turn during the time @[0,1]@, with each value getting an equal
--   amount of time.  In other words, @discrete@ creates a \"slide
--   show\" that starts at time 0 and ends at time 1.  The first
--   element is used prior to time 0, and the last element is used
--   after time 1.
--
--   It is an error to call @discrete@ on the empty list.
discrete :: (Clock t, Real n, Fractional n) => [a] -> Active t n a
discrete [] = error "Data.Active.discrete must be called with a non-empty list."
discrete xs = f <$> ui
  where f (t :: Rational)
            | t <= 0    = V.unsafeHead v
            | t >= 1    = V.unsafeLast v
            | otherwise = V.unsafeIndex v $ floor (t * fromIntegral (V.length v))
        v = V.fromList xs

-- | @simulate r act@ simulates the 'Active' value @act@, returning a
--   list of \"snapshots\" taken at regular intervals from the start
--   time to the end time.  The interval used is determined by the
--   rate @r@, which denotes the \"frame rate\", that is, the number
--   of snapshots per unit time.
--
--   If the 'Active' value is constant (and thus has no start or end
--   times), a list of length 1 is returned, containing the constant
--   value.
simulate :: (Clock t, Real n, Enum n, Fractional n) => n -> Active t n a -> [a]
simulate 0    = const []
simulate rate =
  onActive (:[])
           (\d -> map (runDynamic d . toTime)
                      (let s = fromTime $ start $ era d
                           e = fromTime $ end   $ era d
                       in  [s, s + 1/rate .. e]
                      )
           )

