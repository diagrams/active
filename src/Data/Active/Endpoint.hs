{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE KindSignatures #-}

module Data.Active.Endpoint where

import Data.Foldable       (Foldable(..))
import Data.Proxy
import Data.Traversable    (Traversable(..), fmapDefault, foldMapDefault)
import Control.Applicative

------------------------------------------------------------
-- EndpointTypes
------------------------------------------------------------

data EndpointType
  = I -- nfinite
  | C -- losed
  | O -- pen

-- data SingEndpointType :: EndpointType -> * where
--   SI :: SingEndpointType I
--   SC :: SingEndpointType C
--   SO :: SingEndpointType O

-- deriving instance Show (SingEndpointType e)

-- class SingEndpointTypeI (e :: EndpointType) where
--   endpointTypeI :: SingEndpointType e

-- instance SingEndpointTypeI I where
--   endpointTypeI = SI

-- instance SingEndpointTypeI C where
--   endpointTypeI = SC

-- instance SingEndpointTypeI O where
--   endpointTypeI = SO

-- Some functions on (promoted) EndpointTypes:

-- Convert Closed to Open
type family Open (x :: EndpointType) :: EndpointType
type instance Open I = I
type instance Open C = O
type instance Open O = O

lemma_F_FOpen
  :: forall p x r.
     IsFinite x => p x -> (IsFinite (Open x) => r) -> r
lemma_F_FOpen _ r
  = case isFinite :: IsFinitePf x of
      IsFiniteC -> r
      IsFiniteO -> r

lemma_F_FClose
  :: forall p x r.
     IsFinite x => p x -> (IsFinite (Close x) => r) -> r
lemma_F_FClose _ r
  = case isFinite :: IsFinitePf x of
      IsFiniteC -> r
      IsFiniteO -> r

-- Convert Open to Closed
type family Close (x :: EndpointType) :: EndpointType
type instance Close I = I
type instance Close C = C
type instance Close O = C

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

lemma_Compat_comm
  :: forall p r l x. Compat r l => p r -> p l -> (Compat l r => x) -> x
lemma_Compat_comm _ _ x
  = case (compat :: CompatPf r l) of
      CompatOC -> x
      CompatCO -> x

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

-- Proofs that endpoints are Closed

data IsCPf :: EndpointType -> * where
  IsCPf :: IsCPf C

class AreC (l :: EndpointType) (r :: EndpointType) where
  areC :: (IsCPf l, IsCPf r)

instance AreC C C where
  areC = (IsCPf, IsCPf)

lemma_areC_isC
  :: forall p e1 e2 r.
     (AreC e1 e2)
  => p e1 -> p e2
  -> ((e1 ~ C, e2 ~ C) => r) -> r
lemma_areC_isC _ _ r
  = case areC :: (IsCPf e1, IsCPf e2) of
      (IsCPf, IsCPf) -> r

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

lemma_isectFI_F
  :: forall p e r.
     (NotOpen e, IsFinite e)
  => p e -> (IsFinite (Isect e I) => r) -> r
lemma_isectFI_F _ r
  = case isFinite :: IsFinitePf e of
      IsFiniteC -> r
      -- IsFiniteO case is impossible because of NotOpen assumption

lemma_isectIF_F
  :: forall p e r.
     (NotOpen e, IsFinite e)
  => p e -> (IsFinite (Isect I e) => r) -> r
lemma_isectIF_F _ r
  = case isFinite :: IsFinitePf e of
      IsFiniteC -> r
      -- IsFiniteO case is impossible because of NotOpen assumption

lemma_isectFF_F
  :: forall p e1 e2 r.
     (NotOpen e1, NotOpen e2, IsFinite e1, IsFinite e2)
  => p e1 -> p e2 -> (IsFinite (Isect e1 e2) => r) -> r
lemma_isectFF_F _ _ r
  = case (isFinite :: IsFinitePf e1, isFinite :: IsFinitePf e2) of
      (IsFiniteC, IsFiniteC) -> r
      -- IsFiniteO cases are impossible because of NotOpen assumptions

lemma_Compat_Finite
  :: forall p l r x.
     (Compat l r)
  => p l -> p r -> ((IsFinite l, IsFinite r) => x) -> x
lemma_Compat_Finite _ _ x
  = case compat :: CompatPf l r of
      CompatCO -> x
      CompatOC -> x

-- Proofs that endpoints are not Open

-- XXX turn this into   O -> forall a. a ?
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

lemma_isect_C_notOpen
  :: forall p e r.
     (NotOpen e)
  => p e
  -> (Isect C e ~ C => r) -> r
lemma_isect_C_notOpen _ r
  = case notOpen :: NotOpenPf e of
      NotOpenI -> r
      NotOpenC -> r

lemma_isect_notOpen_C
  :: forall p e r.
     (NotOpen e)
  => p e
  -> (Isect e C ~ C => r) -> r
lemma_isect_notOpen_C _ r
  = case notOpen :: NotOpenPf e of
      NotOpenI -> r
      NotOpenC -> r

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

endpointMin
  :: (Ord t, NotOpen e1, NotOpen e2)
  => Endpoint e1 t -> Endpoint e2 t -> Endpoint (Isect e1 e2) t
endpointMin = endpointCmp min

endpointMax
  :: (Ord t, NotOpen e1, NotOpen e2)
  => Endpoint e1 t -> Endpoint e2 t -> Endpoint (Isect e1 e2) t
endpointMax = endpointCmp max
