{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE UndecidableInstances  #-}

module Control.IApplicative.Examples where

import           Data.Finitude
import Control.IApplicative

import           GHC.Exts      (Constraint)
import           Prelude       hiding (cycle, pure, repeat, (<*>))
import qualified Prelude       as P


newtype FList (f :: Finitude) (a :: *) = FList [a]
  deriving Show

instance IFunctor FList where
  imap f (FList xs) = FList (map f xs)

cycle :: [a] -> FList I a
cycle = FList . P.cycle

repeat :: a -> FList I a
repeat = FList . P.repeat

fin :: [a] -> FList F a
fin as = length as `seq` (FList as)

instance IApplicative FList where
  type Id = I
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
  type Id = NInf
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
  type Id = ()
  type (:*:) i j = ()
  ipure = List . P.pure
  List fs <:*> List xs = List (fs P.<*> xs)
