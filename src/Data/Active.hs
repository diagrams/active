{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE TypeOperators              #-}

module Active where

import           Control.Applicative.Free
import           Data.Semigroup

------------------------------------------------------------
-- Duration
------------------------------------------------------------

-- | @Duration@s are nonnegative rational numbers, with the usual 'Ord'
--   structure and a monoidal structure given by addition.
newtype Duration = Duration Rational
  deriving (Num, Eq, Ord, Show)

instance Semigroup Duration where
  Duration r1 <> Duration r2 = Duration (r1 + r2)

instance Monoid Duration where
  mempty = 0
  mappend = (<>)

------------------------------------------------------------
-- Lower bounded durations
------------------------------------------------------------

-- | A given value can be known 'Exactly', or can represent a lower
--   bound ('AtLeast').
data Certainty = Exactly | AtLeast
  deriving (Eq, Show)

-- | The semigroup for 'Certainty' corresponds to the natural additive
--   semigroup on lower bounds (see 'LB').  That is, 'Exactly' is the
--   identity element and 'AtLeast' is an annihilator.
instance Semigroup Certainty where
  AtLeast <> _       = AtLeast
  _       <> AtLeast = AtLeast
  Exactly <> Exactly = Exactly

instance Monoid Certainty where
  mempty  = Exactly
  mappend = (<>)

-- | A value of type LB m represents either an exact value of type m, or
--   a lower bound of type m.  This should only be used when the monoid
--   structure on m is monotonic with respect to the linear ordering on
--   m, that is,
--
--     x < y ==> xz < yz and zx < zy for all x, y, z.
--
--   In this case the monoid structure on LB m is inherited from the
--   that on m.
newtype LB m = LB (Certainty, m)
  deriving (Eq, Show, Semigroup, Monoid)

------------------------------------------------------------
-- Natural transformations and higher-order functors
------------------------------------------------------------

-- | Natural transformations.
type (f ~> g) = forall a. f a -> g a

-- | Higher-order functors.
class HFunctor f where
  hmap :: (g ~> h) -> (f g ~> f h)

instance HFunctor Ap where
  hmap _   (Pure a) = Pure a
  hmap eta (Ap x f) = Ap (eta x) (hmap eta f)

-- | Higher-order fixpoint.
newtype Fix1 (f :: (k -> *) -> (k -> *)) (a :: k) :: * where
  In :: f (Fix1 f) a -> Fix1 f a

out :: Fix1 f ~> f (Fix1 f)
out (In f) = f

-- | Catamorphism for higher-order fixpoint.
cata1 :: HFunctor f => (f r ~> r) -> (Fix1 f ~> r)
cata1 phi = phi . hmap (cata1 phi) . out

-- Decorated d f r a is an f-structure, parameterized by (r :: * -> *)
-- and (a :: *), paired with ("decorated by") a value of type @d@.
data Decorated (d :: *) (f :: (* -> *) -> * -> *) r (a :: *) where
  Deco :: d -> f r a -> Decorated d f r a

------------------------------------------------------------
-- Active
------------------------------------------------------------

-- Dynamic errors which can arise while building Active values
data ActiveErr = Mismatch Duration Duration
               | TooShort Duration Duration
               | Impossible String

-- Active structure functor.
data ActiveF f a
  = Par (Ap f a)         -- Parallel composition, with a free Applicative
                         --   Note this includes 'Pure'.
  | Seq (f a) (f a)      -- Sequential composition.  Invariant: at
                         --   most one of the two branches has an
                         --   unknown (AtLeast) duration.  Eventual
                         --   intention is that this will be kept
                         --   balanced somehow.
  | Prim Duration (Duration -> a)   -- Primitive time-varying value
  | DynErr ActiveErr     -- Dynamic error

instance HFunctor ActiveF where
  hmap eta (Par a)     = Par (hmap eta a)
  hmap eta (Seq a1 a2) = Seq (eta a1) (eta a2)
  hmap _   (Prim d f)  = Prim d f
  hmap _   (DynErr a)  = DynErr a

-- Decorated + Fix1 basically let us build 'Active' as a higher-order
-- cofree comonad---because of the higher-order-ness we unfortunately
-- can't reuse e.g. Control.Comonad.Cofree from the 'free' package.
--
-- Active values are trees built out of ActiveF, i.e. where each
-- internal node corresponds to parallel or sequential composition,
-- and each leaf is a primitive time-varying value, and where each
-- node has been decorated with a lower-bounded duration.
type Active = Fix1 (Decorated (LB Duration) ActiveF)

------------------------------------------------------------
-- Dynamic checking for Active
------------------------------------------------------------

activeErr :: ActiveErr -> Active a
activeErr e = In (Deco (LB (Exactly, 0)) (DynErr e))

checkEq :: Duration -> Duration -> Active a -> Active a
checkEq d1 d2 a
  | d1 == d2  = a
  | otherwise = activeErr $ Mismatch d1 d2

activeDur :: Active a -> LB Duration
activeDur (In (Deco d _)) = d

resolveDuration :: Duration -> Active a -> Active a
resolveDuration dur act@(In (Deco (LB (Exactly, d)) _)) = checkEq dur d act
resolveDuration dur     (In (Deco (LB (AtLeast, d)) a))
  | d > dur = activeErr $ TooShort dur d
  | otherwise = In (Deco (LB (Exactly, dur)) (resolveDurationF dur a))

resolveDurationF :: Duration -> ActiveF Active a -> ActiveF Active a
resolveDurationF d (Par ap)   = Par (resolveDurationAp d ap)
resolveDurationF _ (Prim _ _) = DynErr (Impossible errStr)
  where errStr = "resolveDurationF on Prim (Prims have exact duration)"
resolveDurationF _ e@(DynErr _) = e  -- (this is impossible too, but who cares)

-- This is the interesting case.  Resolve the durations of a1 and a2
-- so that they sum to d.  This is possible because of the invariant
-- that at most one of the two sides has an unknown duration.  (In
-- fact, at this point we know that *exactly* one of the two sides has
-- an unknown duration.)
resolveDurationF d (Seq a1 a2)
  = case activeDur a1 of
      (LB (Exactly, d1)) -> Seq a1 (resolveDuration (d - d1) a2)
      (LB (AtLeast, _ )) ->
        case activeDur a2 of
          (LB (Exactly, d2)) -> Seq (resolveDuration (d - d2) a1) a2
          (LB (AtLeast, _)) -> DynErr $
            Impossible "resolveDurationF on Seq with both sides Exact"

-- Resolve the duration of a parallel composition (i.e. free
-- Applicative structure) of Actives.
resolveDurationAp :: Duration -> Ap Active a -> Ap Active a

-- Pure can have any duration, nothing to do
resolveDurationAp _ p@(Pure _) = p

-- Recurse through an Ap. This is necessary since there may be more Seqs buried
-- in there.
resolveDurationAp d (Ap x f) = Ap (resolveDuration d x) (resolveDurationAp d f)
