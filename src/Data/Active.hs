{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE EmptyDataDecls             #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
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

import GHC.Exts

import           Control.Applicative
import           Control.Arrow       ((***))
import           Control.Lens
import           Prelude             hiding (Floating)
import           Data.AffineSpace
import           Data.Foldable       (Foldable(..))
import qualified Data.Map            as M
import           Data.Maybe          (isNothing)
import           Data.Semigroup
import           Data.Traversable    (Traversable, fmapDefault, foldMapDefault)
import           Data.VectorSpace

------------------------------------------------------------
-- EndpointTypes
------------------------------------------------------------

data EndpointType
  = I -- nfinite
  | C -- losed
  | O -- pen

-- Some functions on (promoted) EndpointTypes:

-- Convert Closed to Open
type family Open (x :: EndpointType) :: EndpointType
type instance Open I = I
type instance Open C = O
type instance Open O = O

-- Intersection of finite + infinite = finite.
type family Isect (x :: EndpointType) (y :: EndpointType) :: EndpointType
type instance Isect I I = I
type instance Isect C I = C
type instance Isect I C = C
type instance Isect C C = C

-- Some proof objects about EndpointTypes:

-- Proofs that finite endpoints are compatible (O/C or C/O)

data CompatPf (e1 :: EndpointType) (e2 :: EndpointType) where
  CompatCO :: CompatPf C O
  CompatOC :: CompatPf O C

class Compat (e1 :: EndpointType) (e2 :: EndpointType) where
  compat :: CompatPf e1 e2

instance Compat C O where
  compat = CompatCO

instance Compat O C where
  compat = CompatOC

-- Proofs that endpoints are Closed

data IsCPf :: EndpointType -> * where
  IsCPf :: IsCPf C

class AreC (l :: EndpointType) (r :: EndpointType) where
  areC :: (IsCPf l, IsCPf r)

instance AreC C C where
  areC = (IsCPf, IsCPf)

-- Proofs that endpoints are finite

data IsFinitePf :: EndpointType -> * where
  IsFiniteC :: IsFinitePf C
  IsFiniteO :: IsFinitePf O

class IsFinite (e :: EndpointType) where
  isFinite :: IsFinitePf e

instance IsFinite C where
  isFinite = IsFiniteC

instance IsFinite O where
  isFinite = IsFiniteO

-- Proofs that endpoints are not Open

data NotOpenPf :: EndpointType -> * where
  NotOpenI :: NotOpenPf I
  NotOpenC :: NotOpenPf C

class NotOpen (e :: EndpointType) where
  notOpen :: NotOpenPf e

instance NotOpen I where
  notOpen = NotOpenI

instance NotOpen C where
  notOpen = NotOpenC

class AreNotOpen (e1 :: EndpointType) (e2 :: EndpointType) where
  areNotOpen :: (NotOpenPf e1, NotOpenPf e2)

instance (NotOpen e1, NotOpen e2) => AreNotOpen e1 e2 where
  areNotOpen = (notOpen, notOpen)

-- For expressing no constraints

class NoConstraints (e1 :: EndpointType) (e2 :: EndpointType)
instance NoConstraints e1 e2

------------------------------------------------------------
-- Endpoints
------------------------------------------------------------

data Endpoint :: EndpointType -> * -> * where
  Infinity ::                    Endpoint I t
  Finite   :: IsFinite e => t -> Endpoint e t

deriving instance Show t => Show (Endpoint e t)
deriving instance Eq t   => Eq   (Endpoint e t)

instance Functor (Endpoint e) where
  fmap = fmapDefault

instance Foldable (Endpoint e) where
  foldMap = foldMapDefault

instance Traversable (Endpoint e) where
  traverse _ Infinity   = pure Infinity
  traverse f (Finite t) = Finite <$> f t

endpointCmp :: (t -> t -> t) -> Endpoint e1 t -> Endpoint e2 t -> Endpoint (Isect e1 e2) t
endpointCmp _   Infinity     Infinity     = Infinity
endpointCmp _   (Finite t1) Infinity     = Finite t1
endpointCmp _   Infinity     (Finite t2) = Finite t2
endpointCmp cmp (Finite t1) (Finite t2) = Finite (cmp t1 t2)

endpointMin :: Ord t => Endpoint e1 t -> Endpoint e2 t -> Endpoint (Isect e1 e2) t
endpointMin = endpointCmp min

endpointMax :: Ord t => Endpoint e1 t -> Endpoint e2 t -> Endpoint (Isect e1 e2) t
endpointMax = endpointCmp max

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

data Proxy a = Proxy

class (Clock t, Compat l r) => Deadline (l :: EndpointType) (r :: EndpointType) t a where
  -- choose deadline-time time-now (if before deadline) (if after deadline)
  choose :: Proxy l -> Proxy r -> t -> t -> a -> a -> a

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

instance Deadline C O Time a where
  choose _ _ deadline now a b = if now <= deadline then a else b

instance Deadline O C Time a where
  choose _ _ deadline now a b = if now <  deadline then a else b

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

-- Note this is a monoid action of durations on timey things.  But we
-- can't really use the Action type class because we want it to be
-- polymorphic in both the timey things AND the durations (so we can
-- do deep embedding stuff and use e.g. JSDuration or whatever).

class Shifty a where
  type ShiftyTime a :: *

  shift :: Diff (ShiftyTime a) -> a -> a

instance Shifty s => Shifty (Maybe s) where
  type ShiftyTime (Maybe s) = ShiftyTime s

  shift = fmap . shift

instance (Shifty a, Shifty b, ShiftyTime a ~ ShiftyTime b) => Shifty (a,b) where
  type ShiftyTime (a,b) = ShiftyTime a

  shift d = shift d *** shift d

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

------------------------------------------------------------
-- Era
------------------------------------------------------------

data EraType = Fixed | Floating
  deriving (Eq, Ord, Show)

type family   EmptyConstraints (et :: EraType)
                :: EndpointType -> EndpointType -> Constraint
type instance EmptyConstraints Fixed    = AreC
type instance EmptyConstraints Floating = Compat

type family   EraConstraints (et :: EraType)
                :: EndpointType -> EndpointType -> Constraint
type instance EraConstraints Fixed    = AreNotOpen
type instance EraConstraints Floating = NoConstraints

-- | An @Era@ is a (potentially infinite) span of time.  @Era@s form a
--   monoid: the combination of two @Era@s is the largest @Era@ which
--   is contained in both; the identity @Era@ is the bi-infinite @Era@
--   covering all time.
--
--   There is also a distinguished empty @Era@, which has no duration
--   and no start or end time.  Note that an @Era@ whose start and end
--   times coincide is /not/ the empty @Era@, though it has zero
--   duration.
--
--   @Era@ is (intentionally) abstract. To construct @Era@ values, use
--   'mkEra'; to deconstruct, use 'start' and 'end'.
data Era :: EraType -> EndpointType -> EndpointType -> * -> * where
  EmptyEra :: EmptyConstraints f l r => Era f l r t
  Era      :: EraConstraints f l r => Endpoint l t -> Endpoint r t -> Era f l r t

  -- We do not export the Era constructor, and maintain the invariant
  -- that the start time is always <= the end time.

deriving instance Show t => Show (Era f l r t)
deriving instance Eq   t => Eq   (Era f l r t)

-- | The empty era, which has no duration and no start or end time,
--   and is an annihilator for 'eraIsect'.
emptyFixedEra :: Era Fixed C C t
emptyFixedEra = EmptyEra

emptyFloatingEra :: Compat l r => Era Floating l r t
emptyFloatingEra = EmptyEra

-- | The era of ALL TIME
allTime :: Era f I I t
allTime = Era Infinity Infinity

-- | Check if an era is the empty era.
eraIsEmpty :: Ord t => Era f l r t -> Bool
eraIsEmpty EmptyEra = True
eraIsEmpty _        = False

-- | Create a fixed 'Era' by specifying (potentially infinite) start
--   and end times.
mkFixedEra :: Ord t => Endpoint l t -> Endpoint r t -> Era Fixed l r t
mkFixedEra s e = canonicalizeFixedEra $ Era s e
-- XXX need more constraints here?

-- XXX what to do for floating eras?

-- | Create a finite fixed 'Era' by specifying finite start and end 'Time's.
mkFixedEra' :: Ord t => t -> t -> Era Fixed C C t
mkFixedEra' s e = mkFixedEra (Finite s) (Finite e)

-- | A getter for accessing the start time of a fixed 'Era', or @Nothing@
--   if the era is empty.
start :: Getter (Era Fixed l r t) (Maybe (Endpoint l t))
start = undefined

-- | A getter for accessing the end time of an 'Era', or @Nothing@ if
--   the era is empty.
end :: Getter (Era Fixed l r t) (Maybe (Endpoint r t))
end = undefined

-- | Two fixed eras intersect to form the largest fixed era which is contained in
--   both, with the empty era as an annihilator.
eraIsect :: forall l1 r1 l2 r2 t. Ord t => Era Fixed l1 r1 t -> Era Fixed l2 r2 t -> Era Fixed (Isect l1 l2) (Isect r1 r2) t
eraIsect (Era l1 r1) (Era l2 r2) = canonicalizeFixedEra $ Era (endpointMax l1 l2) (endpointMin r1 r2)
eraIsect EmptyEra EmptyEra = case (areC :: (IsCPf l1, IsCPf r1), areC :: (IsCPf l2, IsCPf r2)) of ((IsCPf, IsCPf), (IsCPf, IsCPf)) -> EmptyEra
-- XXX redo this
-- eraIsect EmptyEra (Era Infinity Infinity)     = case (areC :: AreCPf l1 r1) of AreCPf -> EmptyEra
-- eraIsect EmptyEra (Era (Finite _) Infinity)   = case (areC :: AreCPf l1 r1) of AreCPf -> EmptyEra
-- eraIsect EmptyEra (Era Infinity (Finite _))   = case (areC :: AreCPf l1 r1) of AreCPf -> EmptyEra
-- eraIsect EmptyEra (Era (Finite _) (Finite _)) = case (areC :: AreCPf l1 r1) of AreCPf -> EmptyEra
-- eraIsect (Era Infinity Infinity)     EmptyEra = case (areC :: AreCPf l2 r2) of AreCPf -> EmptyEra
-- eraIsect (Era (Finite _) Infinity)   EmptyEra = case (areC :: AreCPf l2 r2) of AreCPf -> EmptyEra
-- eraIsect (Era Infinity (Finite _))   EmptyEra = case (areC :: AreCPf l2 r2) of AreCPf -> EmptyEra
-- eraIsect (Era (Finite _) (Finite _)) EmptyEra = case (areC :: AreCPf l2 r2) of AreCPf -> EmptyEra
  -- ugh, all the above cases are actually needed to make the type checker happy

-- Maintain the invariant that s <= e
canonicalizeFixedEra :: Ord t => Era Fixed l r t -> Era Fixed l r t
canonicalizeFixedEra (Era (Finite s) (Finite e)) | s > e = EmptyEra
canonicalizeFixedEra era = era

eraSeq :: forall l1 r1 l2 r2 t.
  Compat r1 l2 => Era Floating l1 r1 t -> Era Floating l2 r2 t -> Era Floating l1 r2 t
eraSeq era1 era2 =
  case (compat :: CompatPf r1 l2) of
    CompatOC -> case era1 of
      EmptyEra -> case (compat :: CompatPf l1 r1) of
        CompatCO -> case era2 of
          EmptyEra -> EmptyEra
          _        -> era2
    -- XXX a ton of other cases go here.

instance AffineSpace t => Shifty (Era Fixed l r t) where
  type ShiftyTime (Era Fixed l r t) = t

  shift = undefined

------------------------------------------------------------
-- Existential Eras
------------------------------------------------------------

data SomeEra :: EraType -> * -> * where
  SomeEra :: Era f l r t -> SomeEra f t

withEra :: SomeEra f t -> (Era f l r t -> x) -> x
withEra (SomeEra e) k = k e

floatEra :: Era Fixed l r t -> SomeEra Floating t
floatEra EmptyEra = SomeEra EmptyEra
floatEra (Era s e) = SomeEra (Era s e)

------------------------------------------------------------
-- Active
------------------------------------------------------------

-- | An @Active f l r t a@ is a time-varying value of type @a@, over the
--   time type @t@, defined on an 'Era' of type @f@.
data Active f l r t a = Active
  { _era       :: Era f l r t
  , _runActive :: t -> a
  }
  deriving (Functor)

makeLenses ''Active

-- | Create a bi-infinite, constant 'Active' value.
pureA :: Ord t => a -> Active f I I t a
pureA a = Active allTime (pure a)

-- | \"Apply\" a fixed 'Active' function to a fixed 'Active' value, pointwise
--   in time, taking the intersection of their intervals.  This is
--   like '<*>' but with a richer indexed type.
appA :: Ord t
     => Active Fixed l1 r1 t (a -> b)
     -> Active Fixed l2 r2 t a
     -> Active Fixed (Isect l1 l2) (Isect r1 r2) t b
appA (Active e1 f1) (Active e2 f2) = Active (eraIsect e1 e2) (f1 <*> f2)

-- | Parallel composition of fixed 'Active' values.  The 'Era' of the
--   result is the intersection of the 'Era's of the inputs.
parA :: (Semigroup a, Ord t)
     => Active Fixed l1 r1 t a -> Active Fixed l2 r2 t a
     -> Active Fixed (Isect l1 l2) (Isect r1 r2) t a
parA (Active e1 f1) (Active e2 f2) = Active (eraIsect e1 e2) (f1 <> f2)

-- parA p1 p2 = pureA (<>) `appA` p1 `appA` p2
--   for the above to typecheck, would need to introduce a type-level proof
--   that I is a left identity for Isect.  Doable but probably not worth it. =)

instance (Shifty a, AffineSpace t, t ~ ShiftyTime a) => Shifty (Active Fixed l r t a) where
  type ShiftyTime (Active Fixed l r t a) = t

  shift d = (runActive %~ shift d) . (era %~ shift d)

------------------------------------------------------------
-- Active
------------------------------------------------------------

-- | An @Active t a@ is a time-varying value of type @a@, over the
--   time type @t@, defined on some particular 'Era'.  @Active@ values
--   may be combined via parallel composition.
--
--   Note this is an existentially quantified version of 'Active',
--   where we do not track the infinite/finite status of the endpoints
--   in the type.  However, this means that 'Active', unlike
--   'Active', can actually be an instance of 'Applicative',
--   'Semigroup', and 'Monoid'.
data Active' f t a where
  Active' :: Active f l r t a -> Active' f t a

-- | Apply a function at all times.
instance Functor (Active' f t) where
  fmap f (Active' p) = Active' (fmap f p)

-- | 'pure' creates a bi-infinite, constant 'Active' value.  '<*>'
--   applies a time-varying function to a time-varying value pointwise
--   in time, with the result being defined on the intersection of the
--   'Era's of the inputs.
instance Ord t => Applicative (Active' Fixed t) where
  pure  = Active' . pureA
  Active' p1 <*> Active' p2 = Active' (p1 `appA` p2)

-- | Parallel composition of 'Active' values.  The result is defined
--   on the intersection of the 'Era's of the inputs.
instance (Semigroup a, Ord t) => Semigroup (Active' f a) where
  Active' p1 <> Active' p2 = Active' (p1 `parA` p2)

-- | The identity is the bi-infinite, constantly 'mempty' value; the
--   combining operation is parallel composition (see the 'Semigroup'
--   instance).
instance (Semigroup a, Monoid a, Ord t) => Monoid (Active' Fixed a) where
  mempty  = Active $ pureA mempty
  mappend = (<>)

instance (Shifty a, AffineSpace t, t ~ ShiftyTime a) => Shifty (Active' Fixed t a) where
  type ShiftyTime (Active' Fixed t a) = t

  shift d (Active' a) = Active' (shift d a)

------------------------------------------------------------
-- SActive
------------------------------------------------------------

-- data Anchor = Start | End | Anchor
--   deriving (Eq, Ord, Show, Read)

-- type AnchorMap t = M.Map Anchor t

-- Concretely, SActive is just a wrapper around
-- Active, but we are careful not to expose the absolute
-- positioning of the underlying Active.

-- NOTE that there is no existential wrapper around SActive which
-- hides l and r (as there is with Active/Active).  It is sensible to
-- combine Active values via parallel composition since any
-- combination of endpoint types may be composed.  However, with
-- SActive that is not the case -- we need to have open+closed or
-- closed+open.  So if we had an existentially quantified version we
-- would not even be able to perform sequential composition on it --
-- it would be pretty useless.

float_ :: (AffineSpace t, VectorSpace (Diff t)) => Active Era l r t a -> SActive l r t a
float_ a_ = addDefaultAnchors $ SActive (float'_ a_) M.empty
  where
    float'_ :: Active Era l r t a -> Active SEra l r t a
    float'_ (Active e f) = Active (floatEra e) f

addDefaultAnchors :: (AffineSpace t, VectorSpace (Diff t)) => SActive l r t a -> SActive l r t a
addDefaultAnchors (SActive a m) = SActive a (M.union m (defaultAnchors (a^.era)))

defaultAnchors :: (AffineSpace t, VectorSpace (Diff t)) => SEra l r t -> AnchorMap t
defaultAnchors EmptyEra      = M.empty
defaultAnchors (Era s e) = M.unions [startAnchor s, endAnchor e]
  where
    startAnchor (Finite s') = M.singleton Start s'
    startAnchor _           = M.empty
    endAnchor   (Finite e') = M.singleton End e'
    endAnchor   _           = M.empty

floatR_ :: (AffineSpace t, VectorSpace (Diff t)) => Active Era l r t a -> SActive l (Open r) t a
floatR_ = openR . float_

floatL_ :: (AffineSpace t, VectorSpace (Diff t)) => Active Era l r t a -> SActive (Open l) r t a
floatL_ = openL . float_

openR :: SActive l r t a -> SActive l (Open r) t a
openR = undefined -- unsafeConvertS

openL :: SActive l r t a -> SActive (Open l) r t a
openL = undefined -- unsafeConvertS

closeR :: Eq t => a -> SActive l O t a -> SActive l C t a
closeR = undefined -- unsafeCloseS end

closeL :: Eq t => a -> SActive O r t a -> SActive C r t a
closeL = undefined -- unsafeCloseS start

unsafeCloseS = undefined
-- unsafeCloseS :: Eq t
--               => Getter (Era l r t) (Maybe (Endpoint l t))
--               -> a -> SActive l r t a -> SActive l' r' t a
-- unsafeCloseS endpt a s@(SActive (Active e f) m) =
--   case e ^. endpt of
--     Nothing          -> unsafeConvertS s
--     -- can we actually make this case impossible?  should we??
--     Just Infinity    -> error "close: this should never happen!  An Open endpoint is Infinite!"
--     Just (Finite t') -> SActive (Active e (\t -> if t == t' then a else f t)) m

-- ugggggghhhh
-- (...) :: forall l1 r1 l2 r2 t a. (AffineSpace t, Deadline r1 l2 t a)
--     => SActive l1 r1 t a -> SActive l2 r2 t a -> SActive l1 r2 t a
-- SActive (Active EmptyEra _) _ ... sa2 = unsafeConvertS sa2
-- sa1 ... SActive (Active EmptyEra _) _ = unsafeConvertS sa1
-- (...)
--   (SActive (Active (Era s1 (Finite e1)) f1) m1)
--   (SActive (Active (Era (Finite s2) e2) f2) m2)
--   = SActive (Active (Era s1 (shift d e2))
--                      (\t -> choose (Proxy :: Proxy r1) (Proxy :: Proxy l2)
--                               e1 t (f1 t) (shift d f2 t))
--             )
--             (combineAnchors m1 (shift d m2))
--   where
--     d = e1 .-. s2
-- _ ... _ = error "... : impossible"

combineAnchors :: AnchorMap t -> AnchorMap t -> AnchorMap t
combineAnchors = M.unionWithKey select
  where
    select Start s _ = s
    select Fixed f _ = f
    select End   _ e = e

instance Deadline r l t a => Semigroup (SActive l r t a) where
  (<>) = undefined -- (...)

instance Deadline r l t a => Monoid (SActive l r t a) where
  mappend = (<>)
  mempty  = SActive (Active undefined (const undefined)) M.empty
    -- XXX what to do here

------------------------------------------------------------
-- Derived API
------------------------------------------------------------
