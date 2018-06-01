{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE RankNTypes #-}

import           Prelude hiding (cycle, repeat, pure)
import qualified Prelude as P
import GHC.Exts (Constraint)

class IFunctor (f :: k -> * -> *) where
  imap :: (a -> b) -> f i a -> f i b

class IFunctor f => IApplicative (f :: k -> * -> *) where
  type I :: k
  type (:*:) (a :: k) (b :: k) :: k
  ipure :: a -> f I a
  (<:*>) :: f i (a -> b) -> f j a -> f (i :*: j) b

data Finitude = Fin | Inf

type family Isect (f1 :: Finitude) (f2 :: Finitude) :: Finitude where
  Isect Fin f = Fin
  Isect f Fin = Fin
  Isect f g   = Inf

newtype FList (f :: Finitude) (a :: *) = FList [a]
  deriving Show

instance IFunctor FList where
  imap f (FList xs) = FList (map f xs)

cycle :: [a] -> FList Inf a
cycle = FList . P.cycle

repeat :: a -> FList Inf a
repeat = FList . P.repeat

fin :: [a] -> FList Fin a
fin as = length as `seq` (FList as)

instance IApplicative FList where
  type I = Inf
  type (:*:) i j = Isect i j
  ipure = repeat
  (FList fs) <:*> (FList xs) = FList (zipWith ($) fs xs)

data N = Z | S N | NInf

type family Succ (n :: N) :: N where
  Succ NInf = NInf
  Succ n    = S n

type family Min (m :: N) (n :: N) :: N where
  Min NInf n = n
  Min m NInf = m
  Min Z n   = Z
  Min m Z   = Z
  Min (S m) (S n) = S (Min m n)

data Vec :: N -> * -> * where
  VNil  :: Vec Z a
  VCons :: a -> Vec n a -> Vec (S n) a
  VInf  :: a -> Vec NInf a -> Vec NInf a

deriving instance Show a => Show (Vec n a)

vrepeat :: a -> Vec NInf a
vrepeat a = VInf a (vrepeat a)

vcycle :: [a] -> Vec NInf a
vcycle as = vcycle' as as
  where
    vcycle' [] as' = vcycle' as' as'
    vcycle' (a:as) as' = VInf a (vcycle' as as')

instance IFunctor Vec where
  imap _ VNil = VNil
  imap f (VCons a as) = VCons (f a) (imap f as)
  imap f (VInf a as)  = VInf (f a) (imap f as)

instance IApplicative Vec where
  type I = NInf
  type (:*:) m n = Min m n
  ipure a = VInf a (ipure a)
  VInf f fs <:*> VInf x xs = VInf (f x) (fs <:*> xs)
  VInf f fs <:*> VCons x xs = VCons (f x) (fs <:*> xs)
  VCons f fs <:*> VInf x xs = VCons (f x) (fs <:*> xs)
  VNil <:*> _ = VNil
  _ <:*> VNil = VNil
  VCons f fs <:*> VCons x xs = VCons (f x) (fs <:*> xs)

------------------------------------------------------------

newtype List (i :: *) a = List [a]
  deriving Show

instance IFunctor List where
  imap f (List as) = List (fmap f as)

instance IApplicative List where
  type I = ()
  type (:*:) i j = ()
  ipure = List . pure
  List fs <:*> List xs = List (fs <*> xs)

------------------------------------------------------------
-- Generalizing...

newtype Ix f (i :: *) (a :: *) = Ix (f a)
  deriving Show

instance Functor f => IFunctor (Ix f) where
  imap f (Ix x) = Ix (fmap f x)

instance Applicative f => IApplicative (Ix f) where
  type I = ()
  type (:*:) i j = ()
  ipure = Ix . P.pure
  Ix f <:*> Ix x = Ix (f <*> x)

----------------------------------------------------------------------
-- Now, can we define pure and <*> so they work on indexed OR
-- non-indexed things?  With clever use of type families, perhaps?
--
-- Hmmm... really not sure whether this is possible.
----------------------------------------------------------------------

-- this works...
type family AppClass (f :: k) :: k -> Constraint
type instance AppClass (f :: * -> *) = Applicative
type instance AppClass (f :: i -> * -> *) = IApplicative

-- ...but not sure how to make this work.
pure :: forall (f :: k -> *) (a :: *). AppClass f f => a -> f a
pure = undefined
