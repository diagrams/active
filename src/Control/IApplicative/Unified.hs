{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

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
-- pure :: forall (f :: k -> *) (a :: *). AppClass f f => a -> f a
-- pure = undefined

-- Attempt #2, with type classes that dispatch on kind!

class Applicativey (f :: k) a b i j where
  type AppC (f :: k) :: k -> Constraint
  type PureType f a b :: *
  type AppType f a b i j :: *

  pure :: PureType f a b
  (<*>) :: AppType f a b i j

instance Applicative f => Applicativey (f :: * -> *) (a :: *) (b :: *) i j where
  type AppC f = Applicative
  type PureType f a b = a -> f a
  type AppType f a b i j = f (a -> b) -> f a -> f b

  pure = P.pure
  (<*>) = (P.<*>)

instance IApplicative f => Applicativey (f :: k -> * -> *) (a :: *) (b :: *) (i :: k) (j :: k) where
  type AppC f = IApplicative
  type PureType f a b = a -> f Id a
  type AppType f a b i j = f i (a -> b) -> f j a -> f (i :*: j) b

  pure = ipure
  (<*>) = (<:*>)

-- The above type checks!  But when I try to use it...
{-

<interactive>:106:1:
    Could not deduce (AppType f0 a0 b0 i0 j0
                      ~ (Maybe a1 -> Maybe a2 -> f a))
    from the context (Functor f,
                      Num a,
                      Num a4,
                      Applicativey f1 a3 b i j,
                      AppType f1 a3 b i j ~ (Maybe a4 -> Maybe a5 -> f a))
      bound by the inferred type for ‘it’:
                 (Functor f, Num a, Num a4, Applicativey f1 a3 b i j,
                  AppType f1 a3 b i j ~ (Maybe a4 -> Maybe a5 -> f a)) =>
                 f (a -> a)
      at <interactive>:106:1-26
    The type variables ‘f0’, ‘a0’, ‘b0’, ‘i0’, ‘j0’, ‘a1’, ‘a2’ are ambiguous
    When checking that ‘it’ has the inferred type
      it :: forall (f :: * -> *) a f1 a1 b i j a2 a3.
            (Functor f, Num a, Num a2, Applicativey f1 a1 b i j,
             AppType f1 a1 b i j ~ (Maybe a2 -> Maybe a3 -> f a)) =>
            f (a -> a)
    Probable cause: the inferred type is ambiguous

-}
