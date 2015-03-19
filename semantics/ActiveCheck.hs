{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}

module ActiveCheck where

import           Control.Applicative.Free
import           Control.Comonad.Cofree
import qualified Data.FingerTree          as FT
import           Data.Semigroup

newtype Duration = Duration Rational
  deriving (Num, Eq, Ord, Show)

instance Semigroup Duration where
  Duration r1 <> Duration r2 = Duration (r1 + r2)

instance Monoid Duration where
  mempty = 0
  mappend = (<>)

data Certainty = Exactly | AtLeast
  deriving (Eq, Show)

instance Semigroup Certainty where
  AtLeast <> _       = AtLeast
  _       <> AtLeast = AtLeast
  Exactly <> Exactly = Exactly

instance Monoid Certainty where
  mempty  = Exactly
  mappend = (<>)

newtype Duration' = Duration' (Certainty, Duration)
  deriving (Eq, Show, Semigroup, Monoid)

data ActiveErr = ActiveErr

data ActiveF f a
  = Par (Ap f a)
  | Seq (f a) (f a)
  | Prim Duration (Duration -> a)
  | DynErr ActiveErr

data Decorated (d :: *) (f :: (* -> *) -> * -> *) r (a :: *) where
  Deco :: d -> f r a -> Decorated d f r a

newtype Fix1 :: ((* -> *) -> * -> *) -> (* -> *) where
    In :: f (Fix1 f) a -> Fix1 f a

type Active = Fix1 (Decorated Duration' ActiveF)

checkEq :: Duration -> Duration -> Active a -> Active a
checkEq d1 d2 a
  | d1 == d2  = a
  | otherwise = In ( Deco (Duration' (AtLeast, 0)) ( DynErr ActiveErr) )  -- duration mismatch

checkDuration :: Duration -> Active a -> Active a
checkDuration dur act@(In (Deco (Duration' (Exactly, d)) _)) = checkEq dur d act
checkDuration dur act@(In (Deco (Duration' (AtLeast, d)) actF)) = _

-- -- no, should pull Duration' out into a separate annotation, to check it first.
-- -- have two mutually recursive versions of checkDuration, just like for DUALTree.
-- -- Use cofree comonad for decoration??
-- checkDuration :: Duration -> Active a -> Active a
-- checkDuration dur act@(Par (Duration' (Exactly,d)) as) = checkEq dur d act
-- checkDuration dur act@(Par (Duration' (AtLeast,d)) as)
--   | dur >= d = Par (Duration' (Exactly, dur)) (map (checkDuration dur) as)
-- checkDuration dur act@(Seq (Duration' (Exactly,d)) as) = checkEq dur d act
-- checkDuration dur act@(Seq (Duration' (AtLeast,d)) as) = _
-- checkDuration dur act@(Prim d f)  = checkEq dur d act
-- checkDuration dur act@(Pure d' a) = _
-- checkDuration dur act@(DynErr e)  = _
-- In
-- instance FT.Measured Duration (RawActive a) where
--   measure (RawActive d _) = d

-- data Active a = Active (FT.FingerTree Duration' (RawActive a))

-- instance Functor Active where
--   fmap f (Active ft) = Active (FT.unsafeFmap (fmap f) ft)
--     -- safe since Functor instance for RawActive cannot change its Duration

-- -- instance Applicative Active where
-- --   pure =
