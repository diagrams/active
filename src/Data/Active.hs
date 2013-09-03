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

import           GHC.Exts            (Constraint)

import           Data.Active.Endpoint

import           Control.Applicative
import           Control.Arrow       ((***))
import           Control.Lens        (makeLenses, view, Getter, (%~))
import           Control.Monad       ((>=>))
import           Data.AffineSpace
import           Data.Array
import qualified Data.Map            as M
import           Data.Maybe          (fromJust)
import           Data.Proxy
import           Data.Semigroup
import           Data.VectorSpace
import           Prelude             hiding (Floating)

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

instance Clock t => Shifty (Endpoint e t) where
  type ShiftyTime (Endpoint e t) = t

  shift d = fmap (.+^ d)

------------------------------------------------------------
-- Era
------------------------------------------------------------

data EraType = Fixed | Floating
  deriving (Eq, Ord, Show)

data IsEraTypePf :: EraType -> * where
  IsEraTypeFixed    :: IsEraTypePf Fixed
  IsEraTypeFloating :: IsEraTypePf Floating

class IsEraType (f :: EraType) where
  isEraType :: IsEraTypePf f

instance IsEraType Fixed where
  isEraType = IsEraTypeFixed

instance IsEraType Floating where
  isEraType = IsEraTypeFloating

type family   EmptyConstraints (et :: EraType)
                :: EndpointType -> EndpointType -> Constraint
type instance EmptyConstraints Fixed    = AreC
type instance EmptyConstraints Floating = Compat

type family   EraConstraints (et :: EraType)
                :: EndpointType -> EndpointType -> Constraint
type instance EraConstraints Fixed    = AreNotOpen
type instance EraConstraints Floating = NoConstraints

lemma_EmptyConstraints_comm
  :: forall p1 p2 f l r x.
     (IsEraType f, EmptyConstraints f l r)
  => p1 f -> p2 l -> p2 r
  -> (EmptyConstraints f r l => x) -> x
lemma_EmptyConstraints_comm _ l r x
  = case isEraType :: IsEraTypePf f of
      IsEraTypeFixed    -> lemma_areC_isC l r    $ x
      IsEraTypeFloating -> lemma_Compat_comm l r $ x

lemma_EraConstraints_II
  :: forall p f r. IsEraType f => p f -> (EraConstraints f I I => r) -> r
lemma_EraConstraints_II _ r
  = case isEraType :: IsEraTypePf f of
      IsEraTypeFixed    -> r
      IsEraTypeFloating -> r

lemma_EraConstraints_comm
  :: forall p1 p2 f l r x.
     (IsEraType f, EraConstraints f l r)
  => p1 f -> p2 l -> p2 r
  -> (EraConstraints f r l => x) -> x
lemma_EraConstraints_comm _ l r x
  = case isEraType :: IsEraTypePf f of
      IsEraTypeFixed    -> lemma_areNotOpen__notOpen l r $ x
      IsEraTypeFloating -> x

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
allTime :: forall f t. IsEraType f => Era f I I t
allTime = lemma_EraConstraints_II (Proxy :: Proxy f)
        $ Era Infinity Infinity

-- | Check if an era is the empty era.
eraIsEmpty :: Ord t => Era f l r t -> Bool
eraIsEmpty EmptyEra = True
eraIsEmpty _        = False
  -- XXX this is wrong now, e.g. what happens if we have a one-point
  -- closed floating era and then call openR on it?

contains :: forall l r t. Ord t => Era Fixed l r t -> t -> Bool
contains EmptyEra _  = False
contains (Era s e) t = endpt s (<=) && endpt e (>=)
  where
    endpt :: forall e. Endpoint e t -> (t -> t -> Bool) -> Bool
    endpt Infinity _     = True
    endpt (Finite p) cmp = p `cmp` t

-- | Create a fixed 'Era' by specifying (potentially infinite) start
--   and end times.
mkFixedEra :: (NotOpen l, NotOpen r, Ord t) => Endpoint l t -> Endpoint r t -> Era Fixed l r t
mkFixedEra s e = canonicalizeFixedEra $ Era s e

-- | Create a finite fixed 'Era' by specifying finite start and end 'Time's.
mkFixedEra' :: Ord t => t -> t -> Era Fixed C C t
mkFixedEra' s e = mkFixedEra (Finite s) (Finite e)

-- | A getter for accessing the start time of a fixed 'Era', or @Nothing@
--   if the era is empty.
start :: Getter (Era Fixed l r t) (Maybe (Endpoint l t))
start f EmptyEra     = EmptyEra <$ f Nothing
start f er@(Era s _) = er <$ f (Just s)

-- | A getter for accessing the end time of an 'Era', or @Nothing@ if
--   the era is empty.
end :: Getter (Era Fixed l r t) (Maybe (Endpoint r t))
end f EmptyEra     = EmptyEra <$ f Nothing
end f er@(Era _ e) = er <$ f (Just e)

-- | Two fixed eras intersect to form the largest fixed era which is contained in
--   both, with the empty era as an annihilator.
eraIsect
  :: forall l1 r1 l2 r2 t.
     Ord t
  => Era Fixed l1 r1 t -> Era Fixed l2 r2 t
  -> Era Fixed (Isect l1 l2) (Isect r1 r2) t

eraIsect (Era l1 r1) (Era l2 r2)
  =                     lemma_areNotOpen__notOpen (Proxy :: Proxy l1) (Proxy :: Proxy r1)
                      $ lemma_areNotOpen__notOpen (Proxy :: Proxy l2) (Proxy :: Proxy r2)
                      $ lemma_isect_notOpen       (Proxy :: Proxy l1) (Proxy :: Proxy l2)
                      $ lemma_isect_notOpen       (Proxy :: Proxy r1) (Proxy :: Proxy r2)

  $ canonicalizeFixedEra
  $ Era (endpointMax l1 l2) (endpointMin r1 r2)

eraIsect EmptyEra EmptyEra
  =                     lemma_areC_isC (Proxy :: Proxy l1) (Proxy :: Proxy r1)
                      $ lemma_areC_isC (Proxy :: Proxy l2) (Proxy :: Proxy r2)

  $ EmptyEra

eraIsect EmptyEra (Era {})
  =                     lemma_areC_isC            (Proxy :: Proxy l1) (Proxy :: Proxy r1)
                      $ lemma_areNotOpen__notOpen (Proxy :: Proxy l2) (Proxy :: Proxy r2)
                      $ lemma_isect_C_notOpen     (Proxy :: Proxy l2)
                      $ lemma_isect_C_notOpen     (Proxy :: Proxy r2)

  $ EmptyEra

eraIsect (Era {}) EmptyEra
  =                     lemma_areNotOpen__notOpen (Proxy :: Proxy l1) (Proxy :: Proxy r1)
                      $ lemma_areC_isC            (Proxy :: Proxy l2) (Proxy :: Proxy r2)
                      $ lemma_isect_notOpen_C     (Proxy :: Proxy l1)
                      $ lemma_isect_notOpen_C     (Proxy :: Proxy r1)
  $ EmptyEra


-- Maintain the invariant that s <= e
canonicalizeFixedEra :: forall l r t. Ord t => Era Fixed l r t -> Era Fixed l r t
canonicalizeFixedEra (Era (Finite s) (Finite e))
  | s > e
  =                     lemma_areNotOpen__notOpen (Proxy :: Proxy l) (Proxy :: Proxy r)
                      $ lemma_notOpen_isFinite__C (Proxy :: Proxy l)
                      $ lemma_notOpen_isFinite__C                (Proxy :: Proxy r)
  $ EmptyEra
canonicalizeFixedEra era = era

eraSeq
  :: forall l1 r1 l2 r2 t.
    (Compat r1 l2, Clock t)
  => Era Floating l1 r1 t -> Era Floating l2 r2 t
  -> Era Floating l1 r2 t
eraSeq EmptyEra EmptyEra
  = lemma_Compat_trans3 (Proxy :: Proxy l1) (Proxy :: Proxy r1) (Proxy :: Proxy l2) (Proxy :: Proxy r2)
  $ EmptyEra

eraSeq EmptyEra e@(Era _ _)
  = lemma_Compat_trans2 (Proxy :: Proxy l1) (Proxy :: Proxy r1) (Proxy :: Proxy l2)
  $ e

eraSeq e@(Era _ _) EmptyEra
  = lemma_Compat_trans2 (Proxy :: Proxy r1) (Proxy :: Proxy l2) (Proxy :: Proxy r2)
  $ e

-- We know e1 and s2 are Finite because of Compat r1 l2 constraint
eraSeq (Era s1 (Finite e1)) (Era (Finite s2) e2)
  = Era s1 (shift (e1 .-. s2) e2)

instance Clock t => Shifty (Era Fixed l r t) where
  type ShiftyTime (Era Fixed l r t) = t

  shift _ EmptyEra  = EmptyEra
  shift d (Era s e) = Era (shift d s) (shift d e)

reverseEra
  :: forall f l r t. (IsFinite l, IsFinite r, IsEraType f)
  => Era f l r t -> Era f r l t
reverseEra EmptyEra
  = lemma_EmptyConstraints_comm (Proxy :: Proxy f) (Proxy :: Proxy l) (Proxy :: Proxy r)
  $ EmptyEra
reverseEra (Era (Finite s) (Finite e))
  = lemma_EraConstraints_comm (Proxy :: Proxy f) (Proxy :: Proxy l) (Proxy :: Proxy r)
  $ Era (Finite s) (Finite e)

------------------------------------------------------------
-- Existential Eras
------------------------------------------------------------

data Era' :: EraType -> * -> * where
  Era' :: Era f l r t -> Era' f t

deriving instance Show t => Show (Era' f t)

withEra :: Era' f t -> (forall l r. Era f l r t -> x) -> x
withEra (Era' e) k = k e

withEras
  :: Era' f t -> Era' f t
  -> (forall l1 r1 l2 r2. Era f l1 r1 t -> Era f l2 r2 t -> x)
  -> x
withEras e1 e2 k = withEra e1 $ \e1' -> withEra e2 $ \e2' -> k e1' e2'

wrapEra :: forall f l r t. Era f l r t -> Era' f t
wrapEra = Era'

floatEra :: forall l r t. Era Fixed l r t -> Maybe (Era Floating l r t)
floatEra EmptyEra  = Nothing
floatEra (Era s e) = Just (Era s e)

-- One might think the EmptyEra cases below (marked with XXX) ought to
-- result in an EmptyEra. In fact, this would be wrong (as the type
-- error makes clear (given sufficient amounts of vigorous
-- squinting)).  If we have an empty floating era, it must have one
-- closed and one open endpoint; opening the closed endpoint would
-- result not in a closed era, but in a zero-duration era with two
-- open endpoints, a bizarre abomination which should never be allowed
-- (to see why, imagine sequentially composing it with an Era on
-- either side, and consider what happens to the values at their
-- endpoints).  But I cannot see how to disallow this statically.

openREra :: forall l r t. Era Floating l r t -> Maybe (Era Floating l (Open r) t)
openREra EmptyEra           = Nothing
openREra (Era s Infinity)   = Just $ Era s Infinity
openREra (Era s (Finite e)) = lemma_F_FOpen (Proxy :: Proxy r)
                            $ Just $ Era s (Finite e)

openLEra :: forall l r t. Era Floating l r t -> Maybe (Era Floating (Open l) r t)
openLEra EmptyEra           = Nothing
openLEra (Era Infinity e)   = Just $ Era Infinity e
openLEra (Era (Finite s) e) = lemma_F_FOpen (Proxy :: Proxy l)
                            $ Just $ Era (Finite s) e

-- The Num t constraint is sort of a hack, but we need to create a
-- non-empty era.  It doesn't matter WHAT t value we choose (since the
-- Era is Floating) but we need to choose one.  Alternatively, we
-- could make another Era constructor for point eras, but that seems
-- like it would be a lot of work...
closeREra :: forall l r t. Num t => Era Floating l r t -> Era Floating l (Close r) t
closeREra EmptyEra           = lemma_Compat_Finite (Proxy :: Proxy l) (Proxy :: Proxy r)
                             $ lemma_F_FClose (Proxy :: Proxy r)
  $ Era (Finite 0) (Finite 0) :: Era Floating l (Close r) t

closeREra (Era s Infinity)
  = Era s Infinity

closeREra (Era s (Finite e)) = lemma_F_FClose (Proxy :: Proxy r)
  $ Era s (Finite e)

closeLEra :: forall l r t. Num t => Era Floating l r t -> Era Floating (Close l) r t
closeLEra EmptyEra           = lemma_Compat_Finite (Proxy :: Proxy l) (Proxy :: Proxy r)
                             $ lemma_F_FClose (Proxy :: Proxy l)
  $ Era (Finite 0) (Finite 0) :: Era Floating (Close l) r t

closeLEra (Era Infinity e)
  = Era Infinity e

closeLEra (Era (Finite s) e) = lemma_F_FClose (Proxy :: Proxy l)
  $ Era (Finite s) e

------------------------------------------------------------
-- Active
------------------------------------------------------------

-- | An @Active f l r t a@ is a time-varying value of type @a@, over the
--   time type @t@, defined on an 'Era' of type @f@.
data Active f l r t a = Active
  { _era       :: Era f l r t
  , _activeFun :: t -> a
  }
  deriving (Functor)

makeLenses ''Active

-- XXX should only export era and activeFun as an accessors for Active
-- Fixed.

fixed :: Active Fixed l r t a -> Active Fixed l r t a
fixed = id

floating :: Active Floating l r t a -> Active Floating l r t a
floating = id

mapTimed :: (t -> a -> b) -> Active Fixed l r t a -> Active Fixed l r t b
mapTimed g (Active e f) = Active e (\t -> g t (f t))

-- | Create a bi-infinite, constant 'Active' value.
pureA :: (IsEraType f, Ord t) => a -> Active f I I t a
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

instance (Shifty a, Clock t, t ~ ShiftyTime a) => Shifty (Active Fixed l r t a) where
  type ShiftyTime (Active Fixed l r t a) = t

  shift d = (activeFun %~ shift d) . (era %~ shift d)

emptyFloatA :: Compat l r => Active Floating l r t a
emptyFloatA = Active emptyFloatingEra (const undefined)

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

withActive :: Active' f t a -> (forall l r. Active f l r t a -> x) -> x
withActive (Active' a) k = k a

onActive' :: (forall l r. Active f l r t a -> Active f l' r' t a) -> Active' f t a -> Active' f t a
onActive' f (Active' a) = Active' (f a)

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
instance (Semigroup a, Ord t) => Semigroup (Active' Fixed t a) where
  Active' p1 <> Active' p2 = Active' (p1 `parA` p2)

-- | The identity is the bi-infinite, constantly 'mempty' value; the
--   combining operation is parallel composition (see the 'Semigroup'
--   instance).
instance (Semigroup a, Monoid a, Ord t) => Monoid (Active' Fixed t a) where
  mempty  = Active' $ pureA mempty
  mappend = (<>)

instance (Shifty a, Clock t, t ~ ShiftyTime a) => Shifty (Active' Fixed t a) where
  type ShiftyTime (Active' Fixed t a) = t

  shift d (Active' a) = Active' (shift d a)

------------------------------------------------------------
-- Anchors
------------------------------------------------------------

-- data Anchor = Start | End | Anchor
--   deriving (Eq, Ord, Show, Read)

-- type AnchorMap t = M.Map Anchor t

-- addDefaultAnchors :: (Clock t) => SActive l r t a -> SActive l r t a
-- addDefaultAnchors (SActive a m) = SActive a (M.union m (defaultAnchors (a^.era)))

-- defaultAnchors :: (Clock t) => SEra l r t -> AnchorMap t
-- defaultAnchors EmptyEra      = M.empty
-- defaultAnchors (Era s e) = M.unions [startAnchor s, endAnchor e]
--   where
--     startAnchor (Finite s') = M.singleton Start s'
--     startAnchor _           = M.empty
--     endAnchor   (Finite e') = M.singleton End e'
--     endAnchor   _           = M.empty

-- combineAnchors :: AnchorMap t -> AnchorMap t -> AnchorMap t
-- combineAnchors = M.unionWithKey select
--   where
--     select Start s _ = s
--     select Fixed f _ = f
--     select End   _ e = e

------------------------------------------------------------

float :: Active Fixed l r t a -> Maybe (Active Floating l r t a)
float (Active e f) = Active <$> floatEra e <*> Just f

-- unsafe because this should not be called on an Active with en empty era
-- basically  fromJust . float  with a better error message.
unsafeFloat :: Active Fixed l r t a -> Active Floating l r t a
unsafeFloat a = case float a of
                  Nothing -> error "unsafeFloat called on empty era"
                  Just a' -> a'

floatR :: Active Fixed l r t a -> Maybe (Active Floating l (Open r) t a)
floatR = float >=> openR

unsafeFloatR :: Active Fixed l r t a -> Active Floating l (Open r) t a
unsafeFloatR a = case floatR a of
                   Nothing -> error "unsafeFloatR on empty era"
                   Just a' -> a'

floatL :: Active Fixed l r t a -> Maybe (Active Floating (Open l) r t a)
floatL = float >=> openL

openR :: Active Floating l r t a -> Maybe (Active Floating l (Open r) t a)
openR (Active e f) = Active <$> openREra e <*> Just f

openL :: Active Floating l r t a -> Maybe (Active Floating (Open l) r t a)
openL (Active e f) = Active <$> openLEra e <*> Just f

closeR :: (Eq t, Num t) => a -> Active Floating l O t a -> Active Floating l C t a
closeR a (Active e f) = Active (closeREra e) f'
  where
    f' = case e of
           EmptyEra           -> f
           (Era _ (Finite y)) -> (\t -> if t == y then a else f t)

closeL :: (Eq t, Num t) => a -> Active Floating O r t a -> Active Floating C r t a
closeL a (Active e f) = Active (closeLEra e) f'
  where
    f' = case e of
           EmptyEra           -> f
           (Era (Finite x) _) -> (\t -> if t == x then a else f t)

(<<>>) :: forall l1 r1 l2 r2 t a.
         (Clock t, Deadline r1 l2 t a)
      => Active Floating l1 r1 t a -> Active Floating l2 r2 t a
      -> Active Floating l1 r2 t a
Active era1@EmptyEra f <<>> Active era2@EmptyEra _ = Active (eraSeq era1 era2) f

Active era1@EmptyEra _ <<>> Active era2@(Era {}) f = Active (eraSeq era1 era2) f

Active era1@(Era {}) f <<>> Active era2@EmptyEra _ = Active (eraSeq era1 era2) f

-- Know e1 and s2 are Finite because of Deadline constraint
Active era1@(Era _ (Finite e1)) f1 <<>> Active era2@(Era (Finite s2) _) f2
  = Active (eraSeq era1 era2)
           (\t -> choose (Proxy :: Proxy r1) (Proxy :: Proxy l2)
                    e1 t (f1 t) (shift (e1 .-. s2) f2 t))

instance Deadline r l t a => Semigroup (Active Floating l r t a) where
  (<>) = (<<>>)

instance Deadline r l t a => Monoid (Active Floating l r t a) where
  mappend = (<>)
  mempty  = lemma_Compat_comm (Proxy :: Proxy r) (Proxy :: Proxy l)
          $ Active emptyFloatingEra (const undefined)
            -- OK to use 'undefined' above since this function can
            -- never be called.

anchorStart
  :: forall l r t a. (IsFinite l, AreNotOpen l r, Clock t)
  => t -> Active Floating l r t a -> Active Fixed l r t a
anchorStart t (Active (Era (Finite s) e) f)
  = Active (Era (Finite t) (shift d e)) (shift d f)
  where d = t .-. s

  -- EmptyEra case can't happen because of AreNotOpen l r constraint.
  -- Era Infinity _  case can't happen because of IsFinite l constraint.

anchorEnd
  :: forall l r t a. (IsFinite r, AreNotOpen l r, Clock t)
  => t -> Active Floating l r t a -> Active Fixed l r t a
anchorEnd t (Active (Era s (Finite e)) f)
  = Active (Era (shift d s) (Finite t)) (shift d f)
  where d = t .-. e

  -- EmptyEra case can't happen because of AreNotOpen l r constraint.
  -- Era _ Infinity  case can't happen because of IsFinite r constraint.

------------------------------------------------------------
-- Derived API
------------------------------------------------------------

runActive :: Active f l r t a -> t -> a
runActive = view activeFun

interval :: Ord t => t -> t -> Active Fixed C C t ()
interval s e = Active (mkFixedEra' s e) (const ())

(...) :: Ord t => t -> t -> Active Fixed C C t ()
(...) = interval

ui :: (Num t, Ord t) => Active Fixed C C t t
ui = timeValued (0 ... 1)

timeValued :: Active Fixed l r t a -> Active Fixed l r t t
timeValued = mapTimed const

-- XXX should check if duration is <= 0?
spell :: (Clock t, Ord t, Num t) => Diff t -> Active Floating C C t ()
spell dur = fromJust . float $ interval 0 (0 .+^ dur)

backwards :: (Clock t, IsEraType f, IsFinite l, IsFinite r)
    => Active f l r t a -> Active f r l t a
backwards (Active EmptyEra f) = Active (reverseEra EmptyEra) f
backwards (Active er@(Era (Finite s) (Finite e)) f) = Active (reverseEra er) f'
  where
    f' t = f (e .+^ (s .-. t))

stretchFromStart :: (IsFinite l, Clock t) => Rational -> Active f l r t a -> Active f l r t a
stretchFromStart 0 _ = error "stretchFromStart by 0"  -- XXX ?
stretchFromStart _ a@(Active EmptyEra _) = a
stretchFromStart k (Active e@(Era (Finite s) Infinity) f)
  = Active e (stretchFunFromStart s k f)
stretchFromStart k (Active (Era (Finite s) (Finite e)) f)
  = Active (Era (Finite s) (Finite e')) (stretchFunFromStart s k f)
  where
    e' = s .+^ (fromRational k *^ (e .-. s))

stretchFunFromStart :: (Clock t) => t -> Rational -> (t -> a) -> t -> a
stretchFunFromStart s k f t = f (s .+^ ((t .-. s) ^/ fromRational k))

stretchFromEnd :: (IsFinite r, Clock t) => Rational -> Active f l r t a -> Active f l r t a
stretchFromEnd 0 _ = error "stretchFromEnd by 0" -- XXX ?
stretchFromEnd _ a@(Active EmptyEra _) = a
stretchFromEnd k (Active er@(Era Infinity (Finite e)) f)
  = Active er (stretchFunFromEnd e k f)
stretchFromEnd k (Active (Era (Finite s) (Finite e)) f)
  = Active (Era (Finite s') (Finite e)) (stretchFunFromEnd e k f)
  where
    s' = e .-^ (fromRational k *^ (e .-. s))

stretchFunFromEnd :: (Clock t) => t -> Rational -> (t -> a) -> t -> a
stretchFunFromEnd e k f t = f (e .-^ ((e .-. t) ^/ fromRational k))

snapshot :: (IsEraType f, Ord t)
         => t -> Active Fixed l r t a -> Maybe (Active f I I t a)
snapshot t (Active er f)
  | er `contains` t = Just $ pureA (f t)
  | otherwise       = Nothing

clamp :: Active f C C t a -> Active f I I t a
clamp (Active (Era (Finite s) (Finite e)) f)
  = undefined
--    Active (Era Infinity Infinity) undefined  -- XXX something to do
                                                -- with Clock or
                                                -- Deadline?

clampBefore :: Active f C r t a -> Active f I r t a
clampBefore = undefined

clampAfter :: Active f l C t a -> Active f l I t a
clampAfter = undefined

pad :: a -> Active f C C t a -> Active f I I t a
pad = undefined

padBefore :: a -> Active f C r t a -> Active f I r t a
padBefore = undefined

padAfter :: a -> Active f l C t a -> Active f l I t a
padAfter = undefined


movie :: (Deadline r l t a, Compat l r)
      => [Active Floating l r t a] -> Active Floating l r t a
movie = foldr (<<>>) emptyFloatA
  -- XXX use a balanced fold?


discrete :: (Clock t, Ord t, Num t, FractionalOf t Rational) => [a] -> Active Fixed C C t a
discrete [] = error "Data.Active.discrete must be called with a non-empty list."
discrete xs = f <$> ui
  where
    f t
      | toFractionalOf t <= (0 :: Rational) = arr ! 0
      | toFractionalOf t >= (1 :: Rational) = arr ! (n-1)
      | otherwise = arr ! floor (toFractionalOf t * fromIntegral n :: Rational)
    n   = length xs
    arr = listArray (0, n-1) xs
