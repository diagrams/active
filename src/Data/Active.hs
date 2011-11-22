{-# LANGUAGE DeriveFunctor
           , GeneralizedNewtypeDeriving
           , TypeSynonymInstances
           , MultiParamTypeClasses
           , TypeFamilies
  #-}
module Data.Active where

import Data.Semigroup
import Data.Functor.Apply
import Control.Applicative
import Control.Newtype

import Data.VectorSpace hiding ((<.>))
import Data.AffineSpace

newtype Time = Time { unTime :: Rational }
  deriving ( Eq, Ord, Show, Read, Enum, Num, Fractional, Real, RealFrac
           , AdditiveGroup, InnerSpace
           )

instance Newtype Time Rational where
  pack   = Time
  unpack = unTime
  
instance VectorSpace Time where
  type Scalar Time = Rational
  s *^ (Time t) = Time (s * t)
  
newtype Duration = Duration { unDuration :: Rational }
  deriving ( Eq, Ord, Show, Read, Enum, Num, Fractional, Real, RealFrac
           , AdditiveGroup)
           
instance Newtype Duration Rational where
  pack   = Duration
  unpack = unDuration

instance AffineSpace Time where
  type Diff Time = Duration
  (Time t1) .-. (Time t2) = Duration (t1 - t2)
  (Time t) .+^ (Duration d) = Time (t + d)

newtype Era = Era (Min Time, Max Time)
  deriving (Semigroup)

mkEra :: Time -> Time -> Era
mkEra begin end = Era (Min begin, Max end)

start :: Era -> Time
start (Era (Min t, _)) = t

end :: Era -> Time
end (Era (_, Max t)) = t

duration :: Era -> Duration
duration = (.-.) <$> end <*> start

data Dynamic a = Dynamic { era        :: Era
                         , runDynamic :: Time -> a
                         }
  deriving (Functor)

instance Apply Dynamic where
  (Dynamic d1 f1) <.> (Dynamic d2 f2) = Dynamic (d1 <> d2) (f1 <.> f2)
  
instance Semigroup a => Semigroup (Dynamic a) where
  Dynamic d1 f1 <> Dynamic d2 f2 = Dynamic (d1 <> d2) (f1 <> f2)
  
newtype Active a = Active (MaybeApply Dynamic a)
  deriving (Functor, Apply, Applicative)

-- XXX think about this more carefully, probably a better way to code it!
instance Semigroup a => Semigroup (Active a) where
  (Active (MaybeApply (Right m1))) <> (Active (MaybeApply (Right m2)))
    = Active (MaybeApply (Right (m1 <> m2)))
      
  (Active (MaybeApply (Left (Dynamic dur f)))) <> (Active (MaybeApply (Right m)))
    = Active (MaybeApply (Left (Dynamic dur (f <> const m))))
      
  (Active (MaybeApply (Right m))) <> (Active (MaybeApply (Left (Dynamic dur f))))
    = Active (MaybeApply (Left (Dynamic dur (const m <> f))))

  (Active (MaybeApply (Left d1))) <> (Active (MaybeApply (Left d2)))
    = Active (MaybeApply (Left (d1 <> d2)))

instance (Monoid a, Semigroup a) => Monoid (Active a) where
  mempty = Active (MaybeApply (Right mempty))
  mappend = (<>)

mkActive :: Time -> Time -> (Time -> a) -> Active a
mkActive begin end f
  = Active (MaybeApply (Left (Dynamic (mkEra begin end) f)))

ui :: Active Double
ui = mkActive 0 1 (fromRational . unTime)

onActive :: (a -> b) -> (Dynamic a -> b) -> Active a -> b
onActive f _ (Active (MaybeApply (Right a))) = f a
onActive _ f (Active (MaybeApply (Left d)))  = f d

simulate :: Rational -> Active a -> [a]
simulate rate act =
  onActive (:[])
           (\d -> map (runDynamic d)
                      (let s = start (era d)
                           e = end   (era d)
                       in  [s, s + 1^/rate .. e]
                      )
           )
           act
