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
import           Control.Lens        (Lens', makeLenses, view, (^.))
import           Data.AffineSpace
import           Data.Monoid.Inf
import           Data.Semigroup
import           Data.VectorSpace

-- import Control.Arrow ((&&&))
-- import Control.Newtype

-- import Data.Array
-- import Data.Maybe

-- import Data.Functor.Apply
-- import Data.Monoid (First(..))

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
  -- choose time-now deadline-time (if before deadline) (if after deadline)
  chooseL :: t -> t -> a -> a -> a
  chooseR :: t -> t -> a -> a -> a

  -- chooseL takes the lefthand value at the precise deadline time.
  -- chooseR takes the righthand value.
  -- at all other times they are identical.

------------------------------------------------------------
-- Time
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
  chooseL t1 t2 a b = if t1 <= t2 then a else b
  chooseR t1 t2 a b = if t1 <  t2 then a else b

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

-- | An @Era@ is a (potentially infinite) span of time.  @Era@s form a
--   monoid: the combination of two @Era@s is the largest @Era@ which
--   is contained in both; the identity @Era@ is the bi-infinite @Era@
--   covering all time.
--
--   @Era@ is abstract. To construct @Era@ values, use 'mkEra'; to
--   deconstruct, use 'start' and 'end'.
newtype Era t = Era (NegInf t, PosInf t)
  deriving (Show, Eq, Ord, Semigroup, Monoid)

-- | Create an 'Era' by specifying (potentially infinite) start and
-- end times.
mkEra :: NegInf t -> PosInf t -> Era t
mkEra s e = Era (s,e)

-- | Create a finite 'Era' by specifying finite start and end 'Time's.
mkEra' :: t -> t -> Era t
mkEra' s e = Era (Finite s, Finite e)

-- | A lens for accessing the start time of an 'Era'.
start :: Lens' (Era t) (NegInf t)
start f (Era (s, e)) = (\s' -> Era (s',e)) <$> f s

-- | A lens for accessing the end time of an 'Era'.
end :: Lens' (Era t) (PosInf t)
end f (Era (s,e)) = (\e' -> Era (s,e')) <$> f e

------------------------------------------------------------

data I -- nfinite
data C -- losed
data O -- pen

type family Isect x y :: *
type instance Isect I I = I
type instance Isect C I = C
type instance Isect I C = C
type instance Isect C C = C

data PActiveX l r t a = PActiveX
  { _pEra       :: Era t
  , _runPActive :: t -> a
  }
  deriving (Functor)

makeLenses ''PActiveX

pPure :: Ord t => a -> PActiveX I I t a
pPure a = PActiveX mempty (pure a)

pApp :: Ord t
     => PActiveX l1 r1 t (a -> b)
     -> PActiveX l2 r2 t a
     -> PActiveX (Isect l1 l2) (Isect r1 r2) t b
pApp (PActiveX e1 f1) (PActiveX e2 f2) = PActiveX (e1 <> e2) (f1 <*> f2)

par :: (Semigroup a, Ord t)
    => PActiveX l1 r1 t a -> PActiveX l2 r2 t a -> PActiveX (Isect l1 l2) (Isect r1 r2) t a
par (PActiveX e1 f1) (PActiveX e2 f2) = PActiveX (e1 <> e2) (f1 <> f2)

-- par p1 p2 = pPure (<>) `pApp` p1 `pApp` p2
--   for the above to typecheck, would need to introduce a type-level proof
--   that I is a left identity for Isect.  Doable but not worth it. =)

data PActive t a where
  PActive :: PActiveX l r t a -> PActive t a

instance Functor (PActive t) where
  fmap f (PActive p) = PActive (fmap f p)

instance Ord t => Applicative (PActive t) where
  pure  = PActive . pPure
  PActive p1 <*> PActive p2 = PActive (p1 `pApp` p2)

instance (Semigroup a, Ord t) => Semigroup (PActive t a) where
  PActive p1 <> PActive p2 = PActive (p1 `par` p2)

instance (Semigroup a, Monoid a, Ord t) => Monoid (PActive t a) where
  mempty  = PActive $ pPure mempty
  mappend = (<>)

------------------------------------------------------------

-- Abstractly, SActiveX represents equivalence classes of PActive
-- under translation.  Concretely, SActiveX is just a wrapper around
-- PActiveX, where we are careful not to expose the absolute
-- positioning of the underlying PActiveX.
newtype SActiveX l r t a = SActiveX { _getPActive :: PActiveX l r t a }

float :: PActiveX l r t a -> SActiveX l r t a
float = SActiveX

openR :: SActiveX l C t a -> SActiveX l O t a
openR = unsafeOpen

openL :: SActiveX C r t a -> SActiveX O r t a
openL = unsafeOpen

-- do not export!
unsafeOpen :: SActiveX l r t a -> SActiveX l' r' t a
unsafeOpen (SActiveX (PActiveX e f)) = SActiveX (PActiveX e f)

closeR :: Eq t => a -> SActiveX l O t a -> SActiveX l C t a
closeR = unsafeClose end

closeL :: Eq t => a -> SActiveX O r t a -> SActiveX C r t a
closeL = unsafeClose start

-- do not export!
unsafeClose :: Eq t
            => Lens' (Era t) (Inf pn t)
            -> a -> SActiveX l r t a -> SActiveX l' r' t a
unsafeClose endpt a (SActiveX (PActiveX e f)) =
  case e ^. endpt of
    -- can we actually make this case impossible??
    Infinity  -> error "close: this should never happen!  An Open endpoint is Infinite!"
    Finite t' -> SActiveX (PActiveX e (\t -> if t == t' then a else f t))

seqR :: SActiveX l O t a -> SActiveX C r t a -> SActiveX l r t a
seqR (SActiveX (PActiveX (Era (s1, Finite e1)) f1))
     (SActiveX (PActiveX (Era (Finite s2, e2)) f2))
      -- XXX what to do here?  Can't make PosInf an AdditiveGroup...
  = SActiveX (PActiveX (Era (s1, e2 .+^ (Finite (e1 - s2))))
                       (\t -> chooseR t e1 (f1 t) (f2 t))
             )
seqR _ _ = error "seqR: impossible"

seqL :: SActiveX l C t a -> SActiveX O r t a -> SActiveX l r t a
seqL = undefined

{- Ideally, the C/O/I type indices would actually determine what sort
of Eras could be contained in a PActiveX, so e.g. we don't need the
error case in unsafeClose.  How might this work?  Would need a GADT
variant of Inf?  But that would probably lead to trouble making it Ord
and so on...?
-}
