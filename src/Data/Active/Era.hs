{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TypeFamilies        #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Active.Era
-- Copyright   :  (c) 2013 Andy Gill, Brent Yorgey
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  byorgey@cis.upenn.edu
--
-- An @Era@ is a (potentially infinite) span of time within which an
-- @Active@ value is defined.  This module defines eras and operations
-- on them.
-----------------------------------------------------------------------------

module Data.Active.Era
    ( -- * Era types
      -- $eratypes

      EraType(..)
    , EmptyConstraints, EraConstraints

      -- * Eras

    , Era(..)

      -- ** Constructors
    , emptyFixedEra
    , emptyFreeEra
    , always
    , mkFixedEra
    , mkEra

      -- ** Accessors

    , eraContains

      -- ** Operations

    , eraIsect
    , eraSeq
    , reverseEra

    , freeEra
    , openREra
    , openLEra
    , closeREra
    , closeLEra

      -- * Proofs

      -- ** Properties and proof objects
    , IsEraType(..)
    , IsEraTypePf(..)

    )
    where

import GHC.Exts (Constraint)

import Data.Proxy
import Data.AffineSpace

import Data.Active.Endpoint
import Data.Active.Time

------------------------------------------------------------
-- Era
------------------------------------------------------------

-- $eratypes
-- There are two types of era:
--
-- * /Fixed/ eras have a definite location in time.
--
-- * /Free/ eras are /equivalence classes/ of fixed eras
--   under shifting in time.  Intuitively, they have a
--   duration but no definite location in time.
--
-- The type of an era is tracked with a type-level tag consisting of a
-- promoted (via @-XDataKinds@) 'EraType' value.
--
-- In addition, each era type imposes some constraints on the
-- endpoints of the era.  These constraints are encoded by the
-- 'EmptyConstraints' and 'EraConstraints' type families.

-- | Tags used to track the type of an era.
data EraType
  = Fixed  -- ^ Eras with a definite location in time
  | Free   -- ^ Equivalence classes of @Fixed@ eras under shifting in time
  deriving (Eq, Ord, Show)

data IsEraTypePf :: EraType -> * where
  IsEraTypeFixed :: IsEraTypePf Fixed
  IsEraTypeFree  :: IsEraTypePf Free

class IsEraType (f :: EraType) where
  isEraType :: IsEraTypePf f

instance IsEraType Fixed where
  isEraType = IsEraTypeFixed

instance IsEraType Free where
  isEraType = IsEraTypeFree

-- | Constraints on the endpoint types of the empty era, parameterized
--   by era type:
--
--   * The fixed empty era must have both endpoints of type @C@.
--
--   * The free empty era must have compatible endpoints (@C\/O@ or @O\/C@).
type family   EmptyConstraints (eraType :: EraType)
                :: EndpointType -> EndpointType -> Constraint
type instance EmptyConstraints Fixed = AreC
type instance EmptyConstraints Free  = Compat

-- | Constraints on the endpoint types of nonempty eras, parameterized
--   by era type.
--
--   * Fixed nonempty eras must have endpoints which are either @C@ or @I@.
--
--   * Free nonempty eras have no constraints on their endpoints.
type family   EraConstraints (eraType :: EraType)
                :: EndpointType -> EndpointType -> Constraint
type instance EraConstraints Fixed = AreNotOpen
type instance EraConstraints Free  = NoConstraints

lemma_EmptyConstraints_comm
  :: forall p1 p2 f l r x.
     (IsEraType f, EmptyConstraints f l r)
  => p1 f -> p2 l -> p2 r
  -> (EmptyConstraints f r l => x) -> x
lemma_EmptyConstraints_comm _ l r x
  = case isEraType :: IsEraTypePf f of
      IsEraTypeFixed    -> lemma_areC_isC l r    $ x
      IsEraTypeFree -> lemma_Compat_sym l r $ x

lemma_EraConstraints_II
  :: forall p f r. IsEraType f => p f -> (EraConstraints f I I => r) -> r
lemma_EraConstraints_II _ r
  = case isEraType :: IsEraTypePf f of
      IsEraTypeFixed    -> r
      IsEraTypeFree -> r

lemma_EraConstraints_comm
  :: forall p1 p2 f l r x.
     (IsEraType f, EraConstraints f l r)
  => p1 f -> p2 l -> p2 r
  -> (EraConstraints f r l => x) -> x
lemma_EraConstraints_comm _ l r x
  = case isEraType :: IsEraTypePf f of
      IsEraTypeFixed    -> lemma_areNotOpen__notOpen l r $ x
      IsEraTypeFree -> x

-- | XXX write me
data Era :: EraType -> EndpointType -> EndpointType -> * -> * where
  EmptyEra :: EmptyConstraints f l r => Era f l r t
  Era      :: EraConstraints f l r => Endpoint l t -> Endpoint r t -> Era f l r t

deriving instance Show t => Show (Era f l r t)
deriving instance Eq   t => Eq   (Era f l r t)

-- | The empty fixed era, which has no duration and no start or end
--   time, and is an annihilator for 'eraIsect'.
emptyFixedEra :: Era Fixed C C t
emptyFixedEra = EmptyEra

-- | The empty free era, which can be thought of as a half-open
--   interval of zero duration.  It is an identity for sequential
--   composition.
emptyFreeEra :: Compat l r => Era Free l r t
emptyFreeEra = EmptyEra

-- | The bi-infinite era of all time.
always :: forall f t. IsEraType f => Era f I I t
always = lemma_EraConstraints_II (Proxy :: Proxy f)
        $ Era Infinity Infinity

-- | Check whether a fixed era contains a given moment in time.
eraContains :: forall l r t. Ord t => Era Fixed l r t -> t -> Bool
eraContains EmptyEra _  = False
eraContains (Era s e) t = endpt s (<=) && endpt e (>=)
  where
    endpt :: forall e. Endpoint e t -> (t -> t -> Bool) -> Bool
    endpt Infinity _     = True
    endpt (Finite p) cmp = p `cmp` t

-- | Create a fixed 'Era' by specifying its endpoints.
mkFixedEra :: (NotOpen l, NotOpen r, Ord t) => Endpoint l t -> Endpoint r t -> Era Fixed l r t
mkFixedEra s e = Era s e

-- | Create a finite 'Era' by specifying finite start and end times.
mkEra :: (EraConstraints f l r, IsFinite l, IsFinite r, Ord t) => t -> t -> Era f l r t
mkEra s e = Era (Finite s) (Finite e)

-- | Two fixed eras intersect to form the largest fixed era which is contained in
--   both.
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


-- | Sequence two compatible free eras.
eraSeq
  :: forall l1 r1 l2 r2 t.
    (Compat r1 l2, Clock t)
  => Era Free l1 r1 t -> Era Free l2 r2 t
  -> Era Free l1 r2 t
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

-- | Reverse an era so it runs backwards. XXX
reverseEra
  :: forall f l r t. (IsFinite l, IsFinite r, IsEraType f)
  => Era f l r t -> Era f r l t
reverseEra EmptyEra
  = lemma_EmptyConstraints_comm (Proxy :: Proxy f) (Proxy :: Proxy l) (Proxy :: Proxy r)
  $ EmptyEra
reverseEra (Era (Finite s) (Finite e))
  = lemma_EraConstraints_comm (Proxy :: Proxy f) (Proxy :: Proxy l) (Proxy :: Proxy r)
  $ Era (Finite s) (Finite e)

freeEra :: forall l r t. Era Fixed l r t -> Maybe (Era Free l r t)
freeEra EmptyEra  = Nothing
freeEra (Era s e) = Just (Era s e)

-- One might think the EmptyEra cases below (marked with XXX) ought to
-- result in an EmptyEra. In fact, this would be wrong (as the type
-- error makes clear (given sufficient amounts of vigorous
-- squinting)).  If we have an empty free era, it must have one
-- closed and one open endpoint; opening the closed endpoint would
-- result not in a closed era, but in a zero-duration era with two
-- open endpoints, a bizarre abomination which should never be allowed
-- (to see why, imagine sequentially composing it with an Era on
-- either side, and consider what happens to the values at their
-- endpoints).  But I cannot see how to disallow this statically.

openREra :: forall l r t. Era Free l r t -> Maybe (Era Free l (Open r) t)
openREra EmptyEra           = Nothing
openREra (Era s Infinity)   = Just $ Era s Infinity
openREra (Era s (Finite e)) = lemma_F_FOpen (Proxy :: Proxy r)
                            $ Just $ Era s (Finite e)

openLEra :: forall l r t. Era Free l r t -> Maybe (Era Free (Open l) r t)
openLEra EmptyEra           = Nothing
openLEra (Era Infinity e)   = Just $ Era Infinity e
openLEra (Era (Finite s) e) = lemma_F_FOpen (Proxy :: Proxy l)
                            $ Just $ Era (Finite s) e

-- The Num t constraint is sort of a hack, but we need to create a
-- non-empty era.  It doesn't matter WHAT t value we choose (since the
-- Era is Free) but we need to choose one.  Alternatively, we
-- could make another Era constructor for point eras, but that seems
-- like it would be a lot of work...
closeREra :: forall l r t. Num t => Era Free l r t -> Era Free l (Close r) t
closeREra EmptyEra           = lemma_Compat_Finite (Proxy :: Proxy l) (Proxy :: Proxy r)
                             $ lemma_F_FClose (Proxy :: Proxy r)
  $ Era (Finite 0) (Finite 0) :: Era Free l (Close r) t

closeREra (Era s Infinity)
  = Era s Infinity

closeREra (Era s (Finite e)) = lemma_F_FClose (Proxy :: Proxy r)
  $ Era s (Finite e)

closeLEra :: forall l r t. Num t => Era Free l r t -> Era Free (Close l) r t
closeLEra EmptyEra           = lemma_Compat_Finite (Proxy :: Proxy l) (Proxy :: Proxy r)
                             $ lemma_F_FClose (Proxy :: Proxy l)
  $ Era (Finite 0) (Finite 0) :: Era Free (Close l) r t

closeLEra (Era Infinity e)
  = Era Infinity e

closeLEra (Era (Finite s) e) = lemma_F_FClose (Proxy :: Proxy l)
  $ Era (Finite s) e
