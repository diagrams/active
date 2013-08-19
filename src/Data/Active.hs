{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE EmptyDataDecls             #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Active
-- Copyright   :  (c) 2013 Andy Gill, Brent Yorgey
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  byorgey@cis.upenn.edu
--
-----------------------------------------------------------------------------

module Data.Active where

import           Control.Applicative
import           Control.Arrow       ((***))
import           Control.Lens
import           Data.AffineSpace
import qualified Data.Map            as M
import           Data.Monoid.Inf
import           Data.Semigroup
import           Data.VectorSpace

------------------------------------------------------------
-- Clock
------------------------------------------------------------
-- | A class that abstracts over time.

class ( AffineSpace t
      , Waiting (Diff t)
      ) => Clock t where

  -- | Convert any value of a 'Real' type (including @Int@, @Integer@,
  --   @Rational@, @Float@, and @Double@) to a 'Time'.
  toTime :: Real a => a -> t
  -- | Convert a 'Time' to a value of any 'Fractional' type (such as
  --   @Rational@, @Float@, or @Double@).
  fromTime :: (FractionalOf t a) => t -> a

  firstTime :: t -> t -> t
  lastTime  :: t -> t -> t
class (FractionalOf w (Scalar w), VectorSpace w) => Waiting w where
  -- | Convert any value of a 'Real' type (including @Int@, @Integer@,
  --   @Rational@, @Float@, and @Double@) to a 'Duration'.
  toDuration :: Real a => a -> w

  -- | Convert a 'Duration' to any other 'Fractional' type (such as
  --   @Rational@, @Float@, or @Double@).
  fromDuration :: (FractionalOf w a) => w -> a

class Fractional a => FractionalOf v a where
  toFractionalOf :: v -> a

class Clock t => Deadline t a where
  -- choose deadline-time time-now (if before deadline) (if after deadline)
  chooseL :: t -> t -> a -> a -> a
  chooseR :: t -> t -> a -> a -> a

  -- chooseL takes the lefthand value at the precise deadline time.
  -- chooseR takes the righthand value.
  -- at all other times they are identical.

------------------------------------------------------------
-- Time + Duration
------------------------------------------------------------

-- | An abstract type for representing /points in time/.  Note that
--   literal numeric values may be used as @Time@s, thanks to the the
--   'Num' and 'Fractional' instances.  'toTime' and 'fromTime' are
--   also provided for convenience in converting between @Time@ and
--   other numeric types.
newtype Time = Time { _time :: Rational }
  deriving ( Eq, Ord, Show, Read, Enum, Num, Fractional, Real, RealFrac )

makeLenses ''Time

instance AffineSpace Time where
  type Diff Time = Duration
  (Time t1) .-. (Time t2) = Duration (t1 - t2)
  (Time t) .+^ (Duration d) = Time (t + d)

instance Clock Time where
  toTime = fromRational . toRational
  fromTime = fromRational . view time
  firstTime = min
  lastTime = max

instance Fractional a => FractionalOf Time a where
  toFractionalOf (Time d) = fromRational d

instance Deadline Time a where
  chooseL deadline now a b = if now <= deadline then a else b
  chooseR deadline now a b = if now <  deadline then a else b

-- | An abstract type representing /elapsed time/ between two points
--   in time.  Note that durations can be negative. Literal numeric
--   values may be used as @Duration@s thanks to the 'Num' and
--   'Fractional' instances. 'toDuration' and 'fromDuration' are also
--   provided for convenience in converting between @Duration@s and
--   other numeric types.
newtype Duration = Duration { _duration :: Rational }
  deriving ( Eq, Ord, Show, Read, Enum, Num, Fractional, Real, RealFrac
           , AdditiveGroup)

makeLenses ''Duration

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

class Shifty a where
  type ShiftyTime a :: *

  shift :: Diff (ShiftyTime a) -> a -> a

instance Shifty s => Shifty (Maybe s) where
  type ShiftyTime (Maybe s) = ShiftyTime s

  shift = fmap . shift

instance (Shifty a, Shifty b, ShiftyTime a ~ ShiftyTime b) => Shifty (a,b) where
  type ShiftyTime (a,b) = ShiftyTime a

  shift d = shift d *** shift d

instance Shifty Time where
  type ShiftyTime Time = Time

  shift d = (.+^ d)

instance AffineSpace t => Shifty (Inf pn t) where
  type ShiftyTime (Inf pn t) = t

  shift d = fmap (.+^ d)

------------------------------------------------------------
-- Era
------------------------------------------------------------

-- | An @Era@ is a (potentially infinite) span of time.  @Era@s form a
--   monoid: the combination of two @Era@s is the largest @Era@ which
--   is contained in both; the identity @Era@ is the bi-infinite @Era@
--   covering all time.
--
--   @Era@ is abstract. To construct @Era@ values, use 'mkEra'; to
--   deconstruct, use 'start' and 'end'.
newtype Era t = Era { _limits :: Maybe (NegInf t, PosInf t) }
  deriving (Show, Eq, Ord)

instance Ord t => Semigroup (Era t) where
  Era (Just ls1) <> Era (Just ls2) = Era (Just (ls1 <> ls2))
  _ <> _                           = Era Nothing

instance Ord t => Monoid (Era t) where
  mappend = (<>)
  mempty  = Era (Just mempty)

makeLenses ''Era

-- | Create an 'Era' by specifying (potentially infinite) start and
-- end times.
mkEra :: NegInf t -> PosInf t -> Era t
mkEra s e = Era (Just (s,e))

-- | Create a finite 'Era' by specifying finite start and end 'Time's.
mkEra' :: t -> t -> Era t
mkEra' s e = mkEra (Finite s) (Finite e)

-- | A getter for accessing the start time of an 'Era'.
start :: Getter (Era t) (Maybe (NegInf t))
start = limits . to (fmap fst)

-- | A getter for accessing the end time of an 'Era'.
end :: Getter (Era t) (Maybe (PosInf t))
end = limits . to (fmap snd)

instance AffineSpace t => Shifty (Era t) where
  type ShiftyTime (Era t) = t

  shift = over limits . shift

------------------------------------------------------------
-- Type tags for Active
------------------------------------------------------------

data I -- nfinite
data C -- losed
data O -- pen

-- Convert Closed to Open
type family Open x :: *
type instance Open I = I
type instance Open C = O
type instance Open O = O

-- Intersection of finite + infinite = finite.
type family Isect x y :: *
type instance Isect I I = I
type instance Isect C I = C
type instance Isect I C = C
type instance Isect C C = C

{- Ideally, the C/O/I type indices would actually determine what sort
of Eras could be contained in a Active_, so e.g. we don't need the
error case in unsafeClose.  How might this work?  Would need a GADT
variant of Inf?  But that would probably lead to trouble making it Ord
and so on...?
-}

------------------------------------------------------------
-- Active_
------------------------------------------------------------

-- | An @Active_ l r t a@ is a time-varying value of type @a@, over the
--   time type @t@, defined on some particular 'Era'.  @l@ and @r@
--   track whether the left and right ends of the @Era@ are
--   respectively infinite (@I@) or finite (@F@).  @Active_@ values
--   may be combined via parallel composition; see 'par_'.
data Active_ l r t a = Active_
  { _era       :: Era t
  , _runActive :: t -> a
  }
  deriving (Functor)

unsafeConvert_ :: Active_ l r t a -> Active_ l' r' t a
unsafeConvert_ (Active_ e f) = Active_ e f

makeLenses ''Active_

-- | Create a bi-infinite, constant 'Active_' value.
pure_ :: Ord t => a -> Active_ I I t a
pure_ a = Active_ mempty (pure a)

-- | \"Apply\" an 'Active_' function to an 'Active_' value, pointwise
--   in time, taking the intersection of their intervals.  This is
--   like '<*>' but with a richer indexed type.
app_ :: Ord t
     => Active_ l1 r1 t (a -> b)
     -> Active_ l2 r2 t a
     -> Active_ (Isect l1 l2) (Isect r1 r2) t b
app_ (Active_ e1 f1) (Active_ e2 f2) = Active_ (e1 <> e2) (f1 <*> f2)

-- | Parallel composition of 'Active_' values.  The 'Era' of the
--   result is the intersection of the 'Era's of the inputs.
par_ :: (Semigroup a, Ord t)
     => Active_ l1 r1 t a -> Active_ l2 r2 t a
     -> Active_ (Isect l1 l2) (Isect r1 r2) t a
par_ (Active_ e1 f1) (Active_ e2 f2) = Active_ (e1 <> e2) (f1 <> f2)

-- par_ p1 p2 = pure_ (<>) `app_` p1 `app_` p2
--   for the above to typecheck, would need to introduce a type-level proof
--   that I is a left identity for Isect.  Doable but not worth it. =)
--   can also do:
-- par_ p1 p2 = unsafeConvert_ $ pure_ (<>) `app_` p1 `app_` p2

instance AffineSpace t => Shifty (Active_ l r t a) where
  type ShiftyTime (Active_ l r t a) = t

  shift = over era . shift

------------------------------------------------------------
-- Active
------------------------------------------------------------

-- | An @Active t a@ is a time-varying value of type @a@, over the
--   time type @t@, defined on some particular 'Era'.  @Active@ values
--   may be combined via parallel composition.
--
--   Note this is an existentially quantified version of 'Active_',
--   where we do not track the infinite/finite status of the endpoints
--   in the type.  However, this means that 'Active', unlike
--   'Active_', can actually be an instance of 'Applicative',
--   'Semigroup', and 'Monoid'.
data Active t a where
  Active :: Active_ l r t a -> Active t a

-- | Apply a function at all times.
instance Functor (Active t) where
  fmap f (Active p) = Active (fmap f p)

-- | 'pure' creates a bi-infinite, constant 'Active' value.  '<*>'
--   applies a time-varying function to a time-varying value pointwise
--   in time, with the result being defined on the intersection of the
--   'Era's of the inputs.
instance Ord t => Applicative (Active t) where
  pure  = Active . pure_
  Active p1 <*> Active p2 = Active (p1 `app_` p2)

-- | Parallel composition of 'Active' values.  The result is defined
--   on the intersection of the 'Era's of the inputs.
instance (Semigroup a, Ord t) => Semigroup (Active t a) where
  Active p1 <> Active p2 = Active (p1 `par_` p2)

-- | The identity is the bi-infinite, constantly 'mempty' value; the
--   combining operation is parallel composition (see the 'Semigroup'
--   instance).
instance (Semigroup a, Monoid a, Ord t) => Monoid (Active t a) where
  mempty  = Active $ pure_ mempty
  mappend = (<>)

------------------------------------------------------------
-- SActive
------------------------------------------------------------

data Anchor = Start | End | Center
  deriving (Eq, Ord, Show, Read)

-- | An @SActive l r t a@ is a time-varying value of type @a@, over
--   the time type @t@, which is invariant under translation: that is,
--   instead of being defined on an 'Era', an @SActive@ value has
--   only a (generalized) duration.  Abstractly, @SActive l r t a@
--   represents equivalence classes of @Active_ l r t a@ values under
--   translation. However, in addition to @I@ and @C@, @l@ and @r@ may
--   also be @O@, indicating a finite, \"open\" endpoint (*i.e.* it is
--   undefined precisely at the endpoint).
--
--   @SActive@ values may be combined via sequential composition; see
--   'seqL' and 'seqR'.  This is why the name is prefixed with @S@:
--   think of it as \"Sequential Active\".
data SActive l r t a = SActive { _active_ :: Active_ l r t a
                               , _anchors :: M.Map Anchor t
                               }

makeLenses ''SActive

-- Concretely, SActive is just a wrapper around
-- Active_, but we are careful not to expose the absolute
-- positioning of the underlying Active_.

-- NOTE that there is no existential wrapper around SActive which
-- hides l and r (as there is with Active_/Active).  It is sensible to
-- combine Active values via parallel composition since any
-- combination of endpoint types may be composed.  However, with
-- SActive_ that is not the case -- we need to have open+closed or
-- closed+open.  So if we had an existentially quantified version we
-- would not even be able to perform sequential composition on it --
-- it would be pretty useless.

unsafeConvertS :: SActive l r t a -> SActive l' r' t a
unsafeConvertS = active_ %~ unsafeConvert_

float_ :: Active_ l r t a -> SActive l r t a
float_ = undefined -- SActive

floatR_ :: Active_ l r t a -> SActive l (Open r) t a
floatR_ = openR . float_

floatL_ :: Active_ l r t a -> SActive (Open l) r t a
floatL_ = openL . float_

openR :: SActive l r t a -> SActive l (Open r) t a
openR = unsafeConvertS

openL :: SActive l r t a -> SActive (Open l) r t a
openL = unsafeConvertS

closeR :: Eq t => a -> SActive l O t a -> SActive l C t a
closeR = unsafeCloseS end

closeL :: Eq t => a -> SActive O r t a -> SActive C r t a
closeL = unsafeCloseS start

unsafeCloseS :: Eq t
              => Getter (Era t) (Maybe (Inf pn t))
              -> a -> SActive l r t a -> SActive l' r' t a
unsafeCloseS = undefined
-- unsafeCloseS endpt a (SActive (Active_ e f) _) =
--   case e ^. endpt of
--     -- can we actually make this case impossible?  should we??
--     Infinity  -> error "close: this should never happen!  An Open endpoint is Infinite!"
--     Finite t' -> SActive (Active_ e (\t -> if t == t' then a else f t))

seqR :: (AffineSpace t, Deadline t a)
     => SActive l O t a -> SActive C r t a -> SActive l r t a
seqR = unsafeSeq chooseR

seqL :: (AffineSpace t, Deadline t a)
     => SActive l C t a -> SActive O r t a -> SActive l r t a
seqL = unsafeSeq chooseL

unsafeSeq :: (AffineSpace t, Deadline t a)
     => (t -> t -> a -> a -> a)
     -> SActive l r1 t a -> SActive l2 r t a -> SActive l r t a
unsafeSeq = undefined
-- unsafeSeq choice (SActive (Active_ (Era (s1, Finite e1)) f1))
--                  (SActive (Active_ (Era (Finite s2, e2)) f2))
--   = SActive (Active_ (Era (s1, shift (e1 .-. s2) e2))
--                       (\t -> choice e1 t (f1 t) (f2 t))
--              )
-- unsafeSeq _ _ _ = error "seq: impossible"

instance Deadline t a => Semigroup (SActive C O t a) where
  (<>) = seqR

instance Deadline t a => Monoid (SActive C O t a) where
  mappend = (<>)
  mempty  = SActive undefined undefined -- XXX what to do here?
                              -- Should we make a special empty Era value?

instance Deadline t a => Semigroup (SActive O C t a) where
  (<>) = seqL

instance Deadline t a => Monoid (SActive O C t a) where
  mappend = (<>)
  mempty  = SActive undefined undefined

------------------------------------------------------------
-- Derived API
------------------------------------------------------------

-- Sequence (using seqR) if possible.  If one of the inside boundaries
-- is infinite, the non-infinite one gets dropped; if both are
-- infinite the R one gets dropped?
seq :: Active t a -> Active t a -> Active t a
seq = undefined
