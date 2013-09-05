{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeFamilies          #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Active.Endpoint
-- Copyright   :  (c) 2013 Andy Gill, Brent Yorgey
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  byorgey@cis.upenn.edu
--
-- Finite or infinite interval endpoints, along with type-level tags
-- for tracking their flavor (infinite, open, or closed).
-----------------------------------------------------------------------------

module Data.Active.Endpoint
    ( -- * Endpoint types

      EndpointType(..), Open, Close, Isect

      -- * Endpoint properties

      -- | Various constraints which we may hold of one or two endpoints.

    , Compat(..), AreC(..), IsFinite(..), NotOpen(..), AreNotOpen(..), NoConstraints
      -- * Endpoints

    , Endpoint(..)
    , endpointCmp, endpointMin, endpointMax

      -- * Proofs

      -- | Tracking endpoint flavors at the type level requires a good
      --   bit of (trivial) theorem proving.

      -- ** Proof objects

    , CompatPf(..), IsCPf(..), IsFinitePf(..), NotOpenPf(..)

      -- ** Lemmata

    , lemma_F_FOpen
    , lemma_F_FClose
    , lemma_Compat_sym
    , lemma_Compat_trans2
    , lemma_Compat_trans3
    , lemma_areC_isC
    , lemma_isectFI_F
    , lemma_isectIF_F
    , lemma_isectFF_F
    , lemma_Compat_Finite
    , lemma_areNotOpen__notOpen
    , lemma_isect_notOpen
    , lemma_isect_C_notOpen
    , lemma_isect_notOpen_C
    , lemma_notOpen_isFinite__C
    )
    where

import Data.Foldable       (Foldable(..))
import Data.Proxy
import Data.Traversable    (Traversable(..), fmapDefault, foldMapDefault)
import Control.Applicative

------------------------------------------------------------
-- EndpointTypes
------------------------------------------------------------

-- | We track three flavors of interval endpoints:
data EndpointType
  = I -- ^ nfinite, /i.e./ the interval extends to infinity in one
      -- direction;
  | C -- ^ losed, /i.e./ the interval has finite extent and includes
      -- its endpoint;
  | O -- ^ pen, /i.e./ the interval has finite extent and does not
      -- include its endpoint.

-- | A type family which converts closed endpoints to open, and is the
--   identity on open or infinite endpoints.
type family Open (x :: EndpointType) :: EndpointType
type instance Open I = I
type instance Open C = O
type instance Open O = O

-- | 'Open' preserves finiteness, /i.e./ if @x@ is finite, so is @Open x@.
lemma_F_FOpen
  :: forall p x r.
     IsFinite x => p x -> (IsFinite (Open x) => r) -> r
lemma_F_FOpen _ r
  = case isFinite :: IsFinitePf x of
      IsFiniteC -> r
      IsFiniteO -> r

-- | 'Close' preserves finiteness.
lemma_F_FClose
  :: forall p x r.
     IsFinite x => p x -> (IsFinite (Close x) => r) -> r
lemma_F_FClose _ r
  = case isFinite :: IsFinitePf x of
      IsFiniteC -> r
      IsFiniteO -> r

-- | A type family which converts open endpoints to closed, and is the
--   identity on closed or infinite endpoints.
type family Close (x :: EndpointType) :: EndpointType
type instance Close I = I
type instance Close C = C
type instance Close O = C

-- | A type family which computes the intersection of two (non-open)
--   endpoints: the result is finite (@C@) if either of the inputs is,
--   or infinite (@I@) if both are.
type family Isect (x :: EndpointType) (y :: EndpointType) :: EndpointType
type instance Isect I I = I
type instance Isect C I = C
type instance Isect I C = C
type instance Isect C C = C

-- | Proofs that finite endpoints are compatible (@O\/C@ or @C\/O@).
data CompatPf (e1 :: EndpointType) (e2 :: EndpointType) where
  CompatCO :: CompatPf C O
  CompatOC :: CompatPf O C

-- | Two endpoints are \"compatible\" if they are both finite and of
--   different types, /i.e./ one is open and the other closed.  This
--   means they can fit together without any gap or overlap.
class Compat (e1 :: EndpointType) (e2 :: EndpointType) where
  compat :: CompatPf e1 e2

instance Compat C O where
  compat = CompatCO

instance Compat O C where
  compat = CompatOC

-- | 'Compat' is symmetric.
lemma_Compat_sym
  :: forall p r l x. Compat r l => p r -> p l -> (Compat l r => x) -> x
lemma_Compat_sym _ _ x
  = case (compat :: CompatPf r l) of
      CompatOC -> x
      CompatCO -> x

-- | A transitivity-like property of 'Compat'.
lemma_Compat_trans2
  :: forall p l1 r1 l2 x.
     (Compat l1 r1, Compat r1 l2)
  => p l1 -> p r1 -> p l2
  -> (l1 ~ l2 => x) -> x
lemma_Compat_trans2 _ _ _ x
  = case (compat :: CompatPf l1 r1, compat :: CompatPf r1 l2) of
      (CompatCO, CompatOC) -> x
      (CompatOC, CompatCO) -> x
      -- other cases can't happen

-- | A transitivity-like property of 'Compat'.
lemma_Compat_trans3
  :: forall p l1 r1 l2 r2 x.
     (Compat l1 r1, Compat r1 l2, Compat l2 r2)
  => p l1 -> p r1 -> p l2 -> p r2
  -> (Compat l1 r2 => x)
  -> x
lemma_Compat_trans3 l1 r1 l2 _ x
  = lemma_Compat_trans2 l1 r1 l2
  $ case compat :: CompatPf l2 r2 of
      CompatOC -> x
      CompatCO -> x

-- | Proofs that endpoints are Closed.
data IsCPf :: EndpointType -> * where
  IsCPf :: IsCPf C

-- | Both endpoints are closed.
class AreC (l :: EndpointType) (r :: EndpointType) where
  areC :: (IsCPf l, IsCPf r)

instance AreC C C where
  areC = (IsCPf, IsCPf)

-- | 'AreC' implies equality with @C@.
lemma_areC_isC
  :: forall p e1 e2 r.
     (AreC e1 e2)
  => p e1 -> p e2
  -> ((e1 ~ C, e2 ~ C) => r) -> r
lemma_areC_isC _ _ r
  = case areC :: (IsCPf e1, IsCPf e2) of
      (IsCPf, IsCPf) -> r

-- | Proofs that endpoints are finite.
data IsFinitePf :: EndpointType -> * where
  IsFiniteC :: IsFinitePf C
  IsFiniteO :: IsFinitePf O

-- | @IsFinite@ holds of a single endpoint which is either closed or
--   open, but not infinite.
class IsFinite (e :: EndpointType) where
  isFinite :: IsFinitePf e

instance IsFinite C where
  isFinite = IsFiniteC

instance IsFinite O where
  isFinite = IsFiniteO

-- | The intersection of finite and infinite is finite.
lemma_isectFI_F
  :: forall p e r.
     (NotOpen e, IsFinite e)
  => p e -> (IsFinite (Isect e I) => r) -> r
lemma_isectFI_F _ r
  = case isFinite :: IsFinitePf e of
      IsFiniteC -> r
      -- IsFiniteO case is impossible because of NotOpen assumption

-- | The intersection of infinite and finite is finite.
lemma_isectIF_F
  :: forall p e r.
     (NotOpen e, IsFinite e)
  => p e -> (IsFinite (Isect I e) => r) -> r
lemma_isectIF_F _ r
  = case isFinite :: IsFinitePf e of
      IsFiniteC -> r
      -- IsFiniteO case is impossible because of NotOpen assumption

-- | The intersection of finite and finite is finite.
lemma_isectFF_F
  :: forall p e1 e2 r.
     (NotOpen e1, NotOpen e2, IsFinite e1, IsFinite e2)
  => p e1 -> p e2 -> (IsFinite (Isect e1 e2) => r) -> r
lemma_isectFF_F _ _ r
  = case (isFinite :: IsFinitePf e1, isFinite :: IsFinitePf e2) of
      (IsFiniteC, IsFiniteC) -> r
      -- IsFiniteO cases are impossible because of NotOpen assumptions

-- | 'Compat' implies finiteness.
lemma_Compat_Finite
  :: forall p l r x.
     (Compat l r)
  => p l -> p r -> ((IsFinite l, IsFinite r) => x) -> x
lemma_Compat_Finite _ _ x
  = case compat :: CompatPf l r of
      CompatCO -> x
      CompatOC -> x

-- | Proofs that endpoints are not Open.
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

-- | 'AreNotOpen' implies 'NotOpen'.
lemma_areNotOpen__notOpen
  :: forall p e1 e2 r.
     AreNotOpen e1 e2
  => p e1 -> p e2
  -> ((NotOpen e1, NotOpen e2) => r) -> r
lemma_areNotOpen__notOpen _ _ r
  = case areNotOpen :: (NotOpenPf e1, NotOpenPf e2) of
      (NotOpenI, NotOpenI) -> r
      (NotOpenI, NotOpenC) -> r
      (NotOpenC, NotOpenI) -> r
      (NotOpenC, NotOpenC) -> r

-- | Intersection preserves non-open-ness.
lemma_isect_notOpen
  :: forall p e1 e2 r.
     (NotOpen e1, NotOpen e2)
  => p e1 -> p e2
  -> (NotOpen (Isect e1 e2) => r) -> r
lemma_isect_notOpen _ _ r
  = case (notOpen :: NotOpenPf e1, notOpen :: NotOpenPf e2) of
      (NotOpenI, NotOpenI) -> r
      (NotOpenI, NotOpenC) -> r
      (NotOpenC, NotOpenI) -> r
      (NotOpenC, NotOpenC) -> r

-- | Intersection with @C@ yields @C@.
lemma_isect_C_notOpen
  :: forall p e r.
     (NotOpen e)
  => p e
  -> (Isect C e ~ C => r) -> r
lemma_isect_C_notOpen _ r
  = case notOpen :: NotOpenPf e of
      NotOpenI -> r
      NotOpenC -> r

-- | Intersection with @C@ yields @C@.
lemma_isect_notOpen_C
  :: forall p e r.
     (NotOpen e)
  => p e
  -> (Isect e C ~ C => r) -> r
lemma_isect_notOpen_C _ r
  = case notOpen :: NotOpenPf e of
      NotOpenI -> r
      NotOpenC -> r

-- | Something both non-open and finite must equal @C@.
lemma_notOpen_isFinite__C
  :: forall p e r.
     (NotOpen e, IsFinite e)
  => p e
  -> (e ~ C => r) -> r
lemma_notOpen_isFinite__C _ r
  = case (notOpen :: NotOpenPf e, isFinite :: IsFinitePf e) of
      (NotOpenC, IsFiniteC) -> r
      -- other cases can't happen, since e would have to equal two
      -- different things

-- For expressing no constraints

-- | @NoConstraints@ is used when a constraint must be specified but
--   no constraints are wanted.
class NoConstraints (e1 :: EndpointType) (e2 :: EndpointType)
instance NoConstraints e1 e2

------------------------------------------------------------
-- Endpoints
------------------------------------------------------------

-- | The endpoint of an interval in time, indexed by its endpoint
--   type.  It can either be
--
--   * an infinite endpoint, indexed by @I@.
--
--   * a finite endpoint, storing a time value and a proof that the
--     endpoint type is finite (/i.e./ either @C@ or @O@).
data Endpoint :: EndpointType -> * -> * where
  Infinity ::                    Endpoint I t

  Finite   :: IsFinite e => t -> Endpoint e t

-- Haddock doesn't currently support comments on GADT constructors.
-- See http://trac.haskell.org/haddock/ticket/43 .

deriving instance Show t => Show (Endpoint e t)
deriving instance Eq t   => Eq   (Endpoint e t)

instance Functor (Endpoint e) where
  fmap = fmapDefault

instance Foldable (Endpoint e) where
  foldMap = foldMapDefault

instance Traversable (Endpoint e) where
  traverse _ Infinity   = pure Infinity
  traverse f (Finite t) = Finite <$> f t

-- | Compare two non-open endpoints.  If both are @Infinity@, return
--   @Infinity@.  If one is infinite and one is finite, return the
--   finite one.  If both are finite, return a finite endpoint with
--   value determined by the given function.
endpointCmp
  :: forall e1 e2 t.
     (NotOpen e1, NotOpen e2)
  => (t -> t -> t)
  -> Endpoint e1 t -> Endpoint e2 t -> Endpoint (Isect e1 e2) t
endpointCmp _   Infinity    Infinity    = Infinity
endpointCmp _   (Finite t1) Infinity    = lemma_isectFI_F (Proxy :: Proxy e1)
                                        $ Finite t1
endpointCmp _   Infinity    (Finite t2) = lemma_isectIF_F (Proxy :: Proxy e2)
                                        $ Finite t2
endpointCmp cmp (Finite t1) (Finite t2) = lemma_isectFF_F (Proxy :: Proxy e1)
                                                          (Proxy :: Proxy e2)
                                        $ Finite (cmp t1 t2)

-- | Compute the minimum of two endpoints, where @Infinity@ represents
--   positive infinity (/i.e./ when computing the upper endpoint of an
--   interval intersection).
endpointMin
  :: (Ord t, NotOpen e1, NotOpen e2)
  => Endpoint e1 t -> Endpoint e2 t -> Endpoint (Isect e1 e2) t
endpointMin = endpointCmp min

-- | Compute the minimum of two endpoints, where @Infinity@ represents
--   negative infinity (/i.e./ when computing the lower endpoint of an
--   interval intersection).
endpointMax
  :: (Ord t, NotOpen e1, NotOpen e2)
  => Endpoint e1 t -> Endpoint e2 t -> Endpoint (Isect e1 e2) t
endpointMax = endpointCmp max
