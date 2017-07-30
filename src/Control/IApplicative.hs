{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds      #-}
{-# LANGUAGE TypeFamilies   #-}
{-# LANGUAGE TypeOperators  #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Control.IApplicative
-- Copyright   :  2016-2017 XXX
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  diagrams-discuss@groups.google.com
--
-- Monoidally indexed applicative functors.
-----------------------------------------------------------------------------

module Control.IApplicative
  ( -- * Indexed functors
    IFunctor(..)

    -- * Indexed applicative functors
  , IApplicative(..), iliftA2

    -- * Lifting non-indexed (applicative) functors
  , Ixed(..)

  ) where

-- | Functors indexed by an arbitrary kind.  The map operation
--   (@imap@) is index-preserving.
class IFunctor (f :: k -> * -> *) where
  imap :: (a -> b) -> f i a -> f i b

infixl 4 <:*>

-- | Applicative functors, indexed by a type-level monoid (of
--   arbitrary kind).  'ipure' and ('<:*>') at the value level are
--   mirrored by the monoid identity and combining operation on the
--   indices at the type level.  The monoid laws on the type indices
--   are exactly what are needed to ensure the Applicative laws.
class IFunctor f => IApplicative (f :: k -> * -> *) where

  -- | The identity element for the type-level index monoid.
  type Id :: k

  -- | The associative combining operation for the type-level index
  -- monoid.
  type (:*:) (a :: k) (b :: k) :: k

  -- | 'ipure' is the indexed analoge to 'pure'; the value it creates
  --   has the identity element as the type index.
  ipure :: a -> f Id a

  -- | '(<:*>)' is the indexed analogue to '(<*>)', where the type
  --   indices are combined according to the operation for the
  --   type-level monoid.
  (<:*>) :: f i (a -> b) -> f j a -> f (i :*: j) b

-- | An indexed analogue to 'liftA2'.
iliftA2 :: IApplicative f => (a -> b -> c) -> f i a -> f j b -> f (i :*: j) c
iliftA2 g x y = (imap g x) <:*> y

------------------------------------------------------------
-- Turning normal functors into indexed ones

-- | Lift a normal functor into a (trivially) indexed one.
newtype Ixed f (i :: *) (a :: *) = Ixed (f a)
  deriving Show

instance Functor f => IFunctor (Ixed f) where
  imap f (Ixed x) = Ixed (fmap f x)

-- | A normal applicative functor can be treated as an indexed
--   applicative functor with a trivial index.
instance Applicative f => IApplicative (Ixed f) where
  type Id = ()
  type (:*:) i j = ()
  ipure = Ixed . pure
  Ixed f <:*> Ixed x = Ixed (f <*> x)

