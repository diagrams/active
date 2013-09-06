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
    , mkEra
    , mkEra'

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
    , IsEraTypePf(..)
    , IsEraType(..)

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
  isEraType       :: IsEraTypePf f
  canonicalizeEra :: Ord t => Era f l r t -> Era f l r t

-- Maintain the invariant that s <= e for fixed eras.
canonicalizeFixedEra :: forall l r t. Ord t => Era Fixed l r t -> Era Fixed l r t
canonicalizeFixedEra (Era (Finite s) (Finite e))
  | s > e
  =                     lemma_areNotOpen__notOpen (Proxy :: Proxy l) (Proxy :: Proxy r)
                      $ lemma_notOpen_isFinite__C (Proxy :: Proxy l)
                      $ lemma_notOpen_isFinite__C                (Proxy :: Proxy r)
  $ EmptyEra
canonicalizeFixedEra era = era

instance IsEraType Fixed where
  isEraType = IsEraTypeFixed

  -- Maintain the invariant that s <= e for fixed eras.
  canonicalizeEra = canonicalizeFixedEra

-- If endpoints are of compatible types, check and see if they are at
-- the same time: if so, switch to an EmptyEra representation.  Note
-- this can happen e.g. by constructing a one-point C/C free era and
-- then calling openR or openL on it.
canonicalizeFreeEra :: forall l r t. Ord t => Era Free l r t -> Era Free l r t
canonicalizeFreeEra er@(Era (Finite s) (Finite e)) =
  case (isFinite :: IsFinitePf l, isFinite :: IsFinitePf r) of
    (IsFiniteO, IsFiniteO) -> er
    (IsFiniteC, IsFiniteC) -> er
    (IsFiniteO, IsFiniteC) -> if s >= e then EmptyEra else er
    (IsFiniteC, IsFiniteO) -> if s >= e then EmptyEra else er
canonicalizeFreeEra era = era

instance IsEraType Free where
  isEraType = IsEraTypeFree
  canonicalizeEra = canonicalizeFreeEra

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

  -- invariants:
  --
  --   * Empty eras (both fixed and free) are always represented using
  --     EmptyEra.
  --   * With (Era (Finite s) (Finite e)), s <= e.

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

-- | Create an 'Era' by specifying its endpoints.
mkEra' :: (IsEraType f, EraConstraints f l r, Ord t) => Endpoint l t -> Endpoint r t -> Era f l r t
mkEra' s e = canonicalizeEra $ Era s e

-- | Create a finite 'Era' by specifying finite start and end times.
mkEra :: (IsEraType f, EraConstraints f l r, IsFinite l, IsFinite r, Ord t) => t -> t -> Era f l r t
mkEra s e = mkEra' (Finite s) (Finite e)

-- | Two fixed eras intersect to form the largest fixed era which is contained in
--   both.
eraIsect
  :: forall l r l' r' t.
     Ord t
  => Era Fixed l r t -> Era Fixed l' r' t
  -> Era Fixed (Isect l l') (Isect r r') t

eraIsect (Era l r) (Era l' r')
  =                     lemma_areNotOpen__notOpen (Proxy :: Proxy l ) (Proxy :: Proxy r )
                      $ lemma_areNotOpen__notOpen (Proxy :: Proxy l') (Proxy :: Proxy r')
                      $ lemma_isect_notOpen       (Proxy :: Proxy l ) (Proxy :: Proxy l')
                      $ lemma_isect_notOpen       (Proxy :: Proxy r ) (Proxy :: Proxy r')
  $ canonicalizeEra
  $ Era (endpointMax l l') (endpointMin r r')

eraIsect EmptyEra EmptyEra
  =                     lemma_areC_isC (Proxy :: Proxy l ) (Proxy :: Proxy r)
                      $ lemma_areC_isC (Proxy :: Proxy l') (Proxy :: Proxy r')

  $ EmptyEra

eraIsect EmptyEra (Era {})
  =                     lemma_areC_isC            (Proxy :: Proxy l ) (Proxy :: Proxy r )
                      $ lemma_areNotOpen__notOpen (Proxy :: Proxy l') (Proxy :: Proxy r')
                      $ lemma_isect_C_notOpen     (Proxy :: Proxy l')
                      $ lemma_isect_C_notOpen     (Proxy :: Proxy r')

  $ EmptyEra

eraIsect (Era {}) EmptyEra
  =                     lemma_areNotOpen__notOpen (Proxy :: Proxy l ) (Proxy :: Proxy r )
                      $ lemma_areC_isC            (Proxy :: Proxy l') (Proxy :: Proxy r')
                      $ lemma_isect_notOpen_C     (Proxy :: Proxy l )
                      $ lemma_isect_notOpen_C     (Proxy :: Proxy r )
  $ EmptyEra

-- | Sequence two compatible free eras.
eraSeq
  :: forall α β β' γ t.
    (Compat β β', Clock t)
  => Era Free α β t -> Era Free β' γ t
  -> Era Free α γ t
eraSeq EmptyEra EmptyEra
  = lemma_Compat_trans3 (Proxy :: Proxy α) (Proxy :: Proxy β) (Proxy :: Proxy β') (Proxy :: Proxy γ)
  $ EmptyEra

eraSeq EmptyEra e@(Era _ _)
  = lemma_Compat_trans2 (Proxy :: Proxy α) (Proxy :: Proxy β) (Proxy :: Proxy β')
  $ e

eraSeq e@(Era _ _) EmptyEra
  = lemma_Compat_trans2 (Proxy :: Proxy β) (Proxy :: Proxy β') (Proxy :: Proxy γ)
  $ e

-- We know e1 and s2 are Finite because of Compat β β' constraint
eraSeq (Era s1 (Finite e1)) (Era (Finite s2) e2)
  = Era s1 (shift (e1 .-. s2) e2)

instance Clock t => Shifty (Era Fixed l r t) where
  type ShiftyTime (Era Fixed l r t) = t

  shift _ EmptyEra  = EmptyEra
  shift d (Era s e) = Era (shift d s) (shift d e)

-- | Reverse an era with two finite endpoints.  This is the identity
--   on endpoint times, and swaps the endpoint types.
reverseEra
  :: forall f l r t. (IsFinite l, IsFinite r, IsEraType f)
  => Era f l r t -> Era f r l t
reverseEra EmptyEra
  = lemma_EmptyConstraints_comm (Proxy :: Proxy f) (Proxy :: Proxy l) (Proxy :: Proxy r)
  $ EmptyEra
reverseEra (Era (Finite s) (Finite e))
  = lemma_EraConstraints_comm (Proxy :: Proxy f) (Proxy :: Proxy l) (Proxy :: Proxy r)
  $ Era (Finite s) (Finite e)

-- | Turn a fixed era into a free era, by forgetting its concrete
--   location in time.  Returns @Nothing@ iff given the empty fixed
--   era as input.
freeEra :: forall l r t. Era Fixed l r t -> Maybe (Era Free l r t)
freeEra EmptyEra  = Nothing
freeEra (Era s e) = Just (Era s e)

-- | Make the right endpoint of a free era open.  Has no effect on
--   right-infinite eras or eras which are right-finite but already
--   open.  Returns @Nothing@ if called on a left-open right-closed
--   empty era (since that would result in a both-open zero-duration
--   era, an absurdity).
openREra :: forall l r t. Ord t => Era Free l r t -> Maybe (Era Free l (Open r) t)
openREra EmptyEra           = case compat :: CompatPf l r of
                                CompatCO -> Just EmptyEra
                                CompatOC -> Nothing
openREra (Era s Infinity)   = Just $ Era s Infinity
openREra (Era s (Finite e)) = lemma_F_FOpen (Proxy :: Proxy r)
                            $ Just $ canonicalizeEra $ Era s (Finite e)

-- | Make the left endpoint of a free era open.  Has no effect on
--   left-infinite eras or eras which are left-finite but already
--   open.  Returns @Nothing@ if called on a left-closed right-open
--   empty era (since that would result in a both-open zero-duration
--   era, an absurdity).
openLEra :: forall l r t. Ord t => Era Free l r t -> Maybe (Era Free (Open l) r t)
openLEra EmptyEra           = case compat :: CompatPf l r of
                                CompatCO -> Nothing
                                CompatOC -> Just EmptyEra
openLEra (Era Infinity e)   = Just $ Era Infinity e
openLEra (Era (Finite s) e) = lemma_F_FOpen (Proxy :: Proxy l)
                            $ Just $ canonicalizeEra $ Era (Finite s) e

-- | Close the right endpoint of a free era.  Has no effect on
--   right-infinite or right-closed eras.
closeREra :: forall l r t. Num t => Era Free l r t -> Era Free l (Close r) t
-- The Num t constraint is sort of a hack, but we need to create a
-- non-empty era.  It doesn't matter WHAT t value we choose (since the
-- Era is Free) but we need to choose one.  Alternatively, we
-- could make another Era constructor for point eras, but that seems
-- like it would be a lot of work...

closeREra EmptyEra           = lemma_Compat_Finite (Proxy :: Proxy l) (Proxy :: Proxy r)
                             $ lemma_F_FClose (Proxy :: Proxy r)
  $ Era (Finite 0) (Finite 0) :: Era Free l (Close r) t

closeREra (Era s Infinity)
  = Era s Infinity

closeREra (Era s (Finite e)) = lemma_F_FClose (Proxy :: Proxy r)
  $ Era s (Finite e)

-- | Close the left endpoint of a free era.  Has no effect on
--   left-infinite or left-closed eras.
closeLEra :: forall l r t. Num t => Era Free l r t -> Era Free (Close l) r t
closeLEra EmptyEra           = lemma_Compat_Finite (Proxy :: Proxy l) (Proxy :: Proxy r)
                             $ lemma_F_FClose (Proxy :: Proxy l)
  $ Era (Finite 0) (Finite 0) :: Era Free (Close l) r t

closeLEra (Era Infinity e)
  = Era Infinity e

closeLEra (Era (Finite s) e) = lemma_F_FClose (Proxy :: Proxy l)
  $ Era (Finite s) e
