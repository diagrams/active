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
import           Data.AffineSpace
import           Data.Foldable       (Foldable(..))
import qualified Data.Map            as M
import           Data.Maybe          (isNothing)
import           Data.Semigroup
import           Data.Traversable    (Traversable, fmapDefault, foldMapDefault)
import           Data.VectorSpace

------------------------------------------------------------
-- Endpoints
------------------------------------------------------------

data EndpointType
  = I -- nfinite
  | C -- losed
  | O -- pen

data CompatPf (e1 :: EndpointType) (e2 :: EndpointType) where
  CompatCO :: CompatPf C O
  CompatOC :: CompatPf O C

class Compat (e1 :: EndpointType) (e2 :: EndpointType) where
  compat :: CompatPf e1 e2

instance Compat C O where
  compat = CompatCO

instance Compat O C where
  compat = CompatOC

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

{- Ideally, the C/O/I type indices would actually determine what sort
of Eras could be contained in a Active_, so e.g. we don't need the
error case in unsafeClose.  How might this work?  Would need a GADT
variant of Inf?  But that would probably lead to trouble making it Ord
and so on...?
-}

data Endpoint :: EndpointType -> * -> * where
  Infinity ::      Endpoint I t
  Finite   :: t -> Endpoint C t
  FiniteO  :: t -> Endpoint O t

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
endpointCmp _   Infinity    Infinity    = Infinity
endpointCmp _   (Finite t1) Infinity    = Finite t1
endpointCmp _   Infinity    (Finite t2) = Finite t2
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
data GenEra :: (EndpointType -> EndpointType -> Constraint)
            -> EndpointType -> EndpointType -> * -> * where
  EmptyEra :: con l r => GenEra con l r t
  Era      :: Endpoint l t -> Endpoint r t -> GenEra con l r t

  -- We do not export the Era constructor, and maintain the invariant
  -- that the start time is always <= the end time.

deriving instance Show t => Show (Era l r t)
deriving instance Eq   t => Eq   (Era l r t)

data AreCPf :: EndpointType -> EndpointType -> * where
  AreCPf :: AreCPf C C

class AreC (l :: EndpointType) (r :: EndpointType) where
  areC :: AreCPf l r

instance AreC C C where
  areC = AreCPf

type Era  = GenEra AreC

type SEra = GenEra Compat

-- | Two eras intersect to form the largest era which is contained in
--   both, with the empty era as an annihilator.
eraIsect :: forall l1 r1 l2 r2 t. Ord t => Era l1 r1 t -> Era l2 r2 t -> Era (Isect l1 l2) (Isect r1 r2) t
eraIsect (Era l1 r1) (Era l2 r2) = canonicalizeEra $ Era (endpointMax l1 l2) (endpointMin r1 r2)
eraIsect EmptyEra EmptyEra = case (areC :: AreCPf l1 r1, areC :: AreCPf l2 r2) of (AreCPf, AreCPf) -> EmptyEra
eraIsect EmptyEra (Era Infinity Infinity)     = case (areC :: AreCPf l1 r1) of AreCPf -> EmptyEra
eraIsect EmptyEra (Era (Finite _) Infinity)   = case (areC :: AreCPf l1 r1) of AreCPf -> EmptyEra
eraIsect EmptyEra (Era Infinity (Finite _))   = case (areC :: AreCPf l1 r1) of AreCPf -> EmptyEra
eraIsect EmptyEra (Era (Finite _) (Finite _)) = case (areC :: AreCPf l1 r1) of AreCPf -> EmptyEra
eraIsect (Era Infinity Infinity)     EmptyEra = case (areC :: AreCPf l2 r2) of AreCPf -> EmptyEra
eraIsect (Era (Finite _) Infinity)   EmptyEra = case (areC :: AreCPf l2 r2) of AreCPf -> EmptyEra
eraIsect (Era Infinity (Finite _))   EmptyEra = case (areC :: AreCPf l2 r2) of AreCPf -> EmptyEra
eraIsect (Era (Finite _) (Finite _)) EmptyEra = case (areC :: AreCPf l2 r2) of AreCPf -> EmptyEra
  -- ugh, all the above cases are actually needed to make the type checker happy

-- Maintain the invariant that s <= e
canonicalizeEra :: Ord t => Era l r t -> Era l r t
canonicalizeEra (Era (Finite s) (Finite e)) | s > e = EmptyEra
canonicalizeEra era = era

-- | The empty era, which has no duration and no start or end time,
--   and is an annihilator for 'eraIsect'.
emptyEra :: Era C C t
emptyEra = EmptyEra

-- | The era of ALL TIME
allTime :: Era I I t
allTime = Era Infinity Infinity

-- | Check if an era is the empty era.
eraIsEmpty :: Ord t => Era l r t -> Bool
eraIsEmpty EmptyEra = True
eraIsEmpty _        = False

-- | Create an 'Era' by specifying (potentially infinite) start and
--   end times.
mkEra :: Ord t => Endpoint l t -> Endpoint r t -> Era l r t
mkEra s e = canonicalizeEra $ Era s e

-- | Create a finite 'Era' by specifying finite start and end 'Time's.
mkEra' :: Ord t => t -> t -> Era C C t
mkEra' s e = mkEra (Finite s) (Finite e)

-- | A getter for accessing the start time of an 'Era', or @Nothing@
--   if the era is empty.
start :: Getter (Era l r t) (Maybe (Endpoint l t))
start = undefined

-- | A getter for accessing the end time of an 'Era', or @Nothing@ if
--   the era is empty.
end :: Getter (Era l r t) (Maybe (Endpoint r t))
end = undefined

instance AffineSpace t => Shifty (Era l r t) where
  type ShiftyTime (Era l r t) = t

  shift = undefined

------------------------------------------------------------
-- Active_
------------------------------------------------------------

-- | An @Active_ l r t a@ is a time-varying value of type @a@, over the
--   time type @t@, defined on some particular 'Era'.  @l@ and @r@
--   track whether the left and right ends of the @Era@ are
--   respectively infinite (@I@) or finite (@F@).  @Active_@ values
--   may be combined via parallel composition; see 'par_'.
data Active_ era l r t a = Active_
  { _era       :: era l r t
  , _runActive :: t -> a
  }
  deriving (Functor)

makeLenses ''Active_

-- | Create a bi-infinite, constant 'Active_' value.
pure_ :: Ord t => a -> Active_ Era I I t a
pure_ a = Active_ allTime (pure a)

-- | \"Apply\" an 'Active_' function to an 'Active_' value, pointwise
--   in time, taking the intersection of their intervals.  This is
--   like '<*>' but with a richer indexed type.
app_ :: Ord t
     => Active_ Era l1 r1 t (a -> b)
     -> Active_ Era l2 r2 t a
     -> Active_ Era (Isect l1 l2) (Isect r1 r2) t b
app_ (Active_ e1 f1) (Active_ e2 f2) = Active_ (eraIsect e1 e2) (f1 <*> f2)

-- | Parallel composition of 'Active_' values.  The 'Era' of the
--   result is the intersection of the 'Era's of the inputs.
par_ :: (Semigroup a, Ord t)
     => Active_ Era l1 r1 t a -> Active_ Era l2 r2 t a
     -> Active_ Era (Isect l1 l2) (Isect r1 r2) t a
par_ (Active_ e1 f1) (Active_ e2 f2) = Active_ (eraIsect e1 e2) (f1 <> f2)

-- par_ p1 p2 = pure_ (<>) `app_` p1 `app_` p2
--   for the above to typecheck, would need to introduce a type-level proof
--   that I is a left identity for Isect.  Doable but not worth it. =)
--   can also do:
-- par_ p1 p2 = unsafeConvert_ $ pure_ (<>) `app_` p1 `app_` p2

instance (Shifty a, AffineSpace t, t ~ ShiftyTime a) => Shifty (Active_ Era l r t a) where
  type ShiftyTime (Active_ Era l r t a) = t

  shift d = (runActive %~ shift d) . (era %~ shift d)

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
  Active :: Active_ Era l r t a -> Active t a

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

instance (Shifty a, AffineSpace t, t ~ ShiftyTime a) => Shifty (Active t a) where
  type ShiftyTime (Active t a) = t

  shift d (Active a) = Active (shift d a)

------------------------------------------------------------
-- SEra
------------------------------------------------------------

eraSeq :: forall l1 r1 l2 r2 t.
  Compat r1 l2 => SEra l1 r1 t -> SEra l2 r2 t -> SEra l1 r2 t
eraSeq era1 era2 =
  case (compat :: CompatPf r1 l2) of
    CompatOC -> case era1 of
      EmptyEra -> case (compat :: CompatPf l1 r1) of
        CompatCO -> case era2 of
          EmptyEra -> EmptyEra
          _        -> era2
    -- XXX a ton of other cases go here.

------------------------------------------------------------
-- SActive
------------------------------------------------------------

data Anchor = Start | End | Fixed
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
data SActive l r t a = SActive { _active_ :: Active_ SEra l r t a
                               , _anchors :: AnchorMap t
                               }

type AnchorMap t = M.Map Anchor t

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

floatEra :: Era l r t -> SEra l r t
floatEra EmptyEra = error "Floating an empty era is not allowed!"
                    -- rule this out statically?  Would need to track
                    -- empty/nonempty in the types.

floatEra (Era s e) = Era s e


float_ :: (AffineSpace t, VectorSpace (Diff t)) => Active_ Era l r t a -> SActive l r t a
float_ a_ = addDefaultAnchors $ SActive (float'_ a_) M.empty
  where
    float'_ :: Active_ Era l r t a -> Active_ SEra l r t a
    float'_ (Active_ e f) = Active_ (floatEra e) f

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

floatR_ :: (AffineSpace t, VectorSpace (Diff t)) => Active_ Era l r t a -> SActive l (Open r) t a
floatR_ = openR . float_

floatL_ :: (AffineSpace t, VectorSpace (Diff t)) => Active_ Era l r t a -> SActive (Open l) r t a
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
-- unsafeCloseS endpt a s@(SActive (Active_ e f) m) =
--   case e ^. endpt of
--     Nothing          -> unsafeConvertS s
--     -- can we actually make this case impossible?  should we??
--     Just Infinity    -> error "close: this should never happen!  An Open endpoint is Infinite!"
--     Just (Finite t') -> SActive (Active_ e (\t -> if t == t' then a else f t)) m

-- ugggggghhhh
-- (...) :: forall l1 r1 l2 r2 t a. (AffineSpace t, Deadline r1 l2 t a)
--     => SActive l1 r1 t a -> SActive l2 r2 t a -> SActive l1 r2 t a
-- SActive (Active_ EmptyEra _) _ ... sa2 = unsafeConvertS sa2
-- sa1 ... SActive (Active_ EmptyEra _) _ = unsafeConvertS sa1
-- (...)
--   (SActive (Active_ (Era s1 (Finite e1)) f1) m1)
--   (SActive (Active_ (Era (Finite s2) e2) f2) m2)
--   = SActive (Active_ (Era s1 (shift d e2))
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
  mempty  = SActive (Active_ undefined (const undefined)) M.empty
    -- XXX what to do here

------------------------------------------------------------
-- Derived API
------------------------------------------------------------
