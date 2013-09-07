{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Active
-- Copyright   :  (c) 2013 Andy Gill, Brent Yorgey
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  byorgey@cis.upenn.edu
--
-----------------------------------------------------------------------------

module Data.Active
    ( -- * Active

      Active

      -- ** Constructors

    , emptyActive, mkActive, (..$), pureA

      -- ** Accessors

    , era, activeFun

      -- ** Operations

    , mapT
    , appA, parA
    , asFixed, asFree

    )
    where

import           Control.Applicative
import           Control.Lens         (Lens', generateSignatures, lensRules,
                                       makeLenses, makeLensesWith, view, (%~),
                                       (&), (.~))
import           Control.Monad        ((>=>))
import           Data.AffineSpace
import           Data.Array
import           Data.Maybe           (fromJust)
import           Data.Proxy
import           Data.Semigroup
import           Data.VectorSpace
import           Prelude

import           Data.Active.Endpoint
import           Data.Active.Era
import           Data.Active.Time

------------------------------------------------------------
-- Active
------------------------------------------------------------

-- | An @Active f l r t a@ is a time-varying value of type @a@, over
--   the time type @t@, defined on an 'Era' of type @f@ with endpoints
--   of type @l@ and @r@.
data Active f l r t a = Active
  { _era       :: Era f l r t
  , _activeFun :: t -> a
  }
  deriving (Functor)

makeLensesWith (lensRules & generateSignatures .~ False) ''Active

-- | A lens for accessing the era of a fixed @Active@ value.
era :: Lens' (Active Fixed l r t a) (Era Fixed l r t)

-- | A lens for accessing the underlying function of a fixed @Active@
-- value.
activeFun :: Lens' (Active Fixed l r t a) (t -> a)

-- | The identity function with a restricted type, sometimes
--   convenient for giving type inference a nudge in the right
--   direction.
asFixed :: Active Fixed l r t a -> Active Fixed l r t a
asFixed = id

-- | The identity function with a restricted type, sometimes
--   convenient for giving type inference a nudge in the right
--   direction.
asFree :: Active Free l r t a -> Active Free l r t a
asFree = id

mapT :: (t -> a -> b) -> Active Fixed l r t a -> Active Fixed l r t b
mapT g (Active e f) = Active e (\t -> g t (f t))

-- | An empty @Active@ value, which is defined nowhere.
emptyActive :: EmptyConstraints f l r => Active f l r t a
emptyActive = Active emptyEra (const undefined)

mkActive :: (Ord t, IsEraType f, EraConstraints f C C) => t -> t -> (t -> a) -> Active f C C t a
mkActive s e f = Active (mkEra s e) f

(..$) :: (Ord t, IsEraType f, EraConstraints f C C) => t -> t -> (t -> a) -> Active f C C t a
(..$) = mkActive

-- | Create a bi-infinite, constant 'Active' value.
pureA :: (IsEraType f, Ord t) => a -> Active f I I t a
pureA a = Active always (pure a)

-- | \"Apply\" a fixed 'Active' function to a fixed 'Active' value, pointwise
--   in time, taking the intersection of their intervals.  This is
--   like '<*>' but with a richer indexed type.
appA :: Ord t
     => Active Fixed l  r  t (a -> b)
     -> Active Fixed l' r' t a
     -> Active Fixed (Isect l  l') (Isect r  r') t b
appA (Active e  f ) (Active e' f') = Active (eraIsect e  e') (f  <*> f')

-- | Parallel composition of fixed 'Active' values.  The 'Era' of the
--   result is the intersection of the 'Era's of the inputs.
parA :: (Semigroup a, Ord t)
     => Active Fixed l  r  t a -> Active Fixed l' r' t a
     -> Active Fixed (Isect l  l') (Isect r  r') t a
parA (Active e  f ) (Active e' f') = Active (eraIsect e  e') (f  <> f')

-- parA p  p' = pureA (<>) `appA` p  `appA` p'
--   for the above to typecheck, would need to introduce a type-level proof
--   that I is a left identity for Isect.  Doable but probably not worth it. =)

instance (Shifty a, Clock t, t ~ ShiftyTime a) => Shifty (Active Fixed l r t a) where
  type ShiftyTime (Active Fixed l r t a) = t

  shift d = (activeFun %~ shift d) . (era %~ shift d)

------------------------------------------------------------
-- Active'
------------------------------------------------------------

-- | An @Active t a@ is a time-varying value of type @a@, over the
--   time type @t@, defined on some particular 'Era'.  @Active@ values
--   may be combined via parallel composition.
--
--   Note this is an existentially quantified version of 'Active',
--   where we do not track the infinite/finite status of the endpoints
--   in the type.  However, this means that 'Active', unlike
--   'Active', can actually be an instance of 'Applicative',
--   'Semigroup', and 'Monoid'.
data Active' f t a where
  Active' :: Active f l r t a -> Active' f t a

withActive :: Active' f t a -> (forall l r. Active f l r t a -> x) -> x
withActive (Active' a) k = k a

onActive' :: (forall l r. Active f l r t a -> Active f l' r' t a) -> Active' f t a -> Active' f t a
onActive' f (Active' a) = Active' (f a)

-- | Apply a function at all times.
instance Functor (Active' f t) where
  fmap f (Active' p) = Active' (fmap f p)

-- | 'pure' creates a bi-infinite, constant 'Active' value.  '<*>'
--   applies a time-varying function to a time-varying value pointwise
--   in time, with the result being defined on the intersection of the
--   'Era's of the inputs.
instance Ord t => Applicative (Active' Fixed t) where
  pure  = Active' . pureA
  Active' p1 <*> Active' p2 = Active' (p1 `appA` p2)

-- | Parallel composition of 'Active' values.  The result is defined
--   on the intersection of the 'Era's of the inputs.
instance (Semigroup a, Ord t) => Semigroup (Active' Fixed t a) where
  Active' p1 <> Active' p2 = Active' (p1 `parA` p2)

-- | The identity is the bi-infinite, constantly 'mempty' value; the
--   combining operation is parallel composition (see the 'Semigroup'
--   instance).
instance (Semigroup a, Monoid a, Ord t) => Monoid (Active' Fixed t a) where
  mempty  = Active' $ pureA mempty
  mappend = (<>)

instance (Shifty a, Clock t, t ~ ShiftyTime a) => Shifty (Active' Fixed t a) where
  type ShiftyTime (Active' Fixed t a) = t

  shift d (Active' a) = Active' (shift d a)



free :: Active Fixed l r t a -> Maybe (Active Free l r t a)
free (Active e f) = Active <$> freeEra e <*> Just f

-- unsafe because this should not be called on an Active with en empty era
-- basically  fromJust . free  with a better error message.
ufree :: Active Fixed l r t a -> Active Free l r t a
ufree a = case free a of
                  Nothing -> error "ufree called on empty era"
                  Just a' -> a'

freeR :: Ord t => Active Fixed l r t a -> Maybe (Active Free l (Open r) t a)
freeR = free >=> openR

ufreeR :: Ord t => Active Fixed l r t a -> Active Free l (Open r) t a
ufreeR a = case freeR a of
                   Nothing -> error "ufreeR on empty era"
                   Just a' -> a'

freeL :: Ord t => Active Fixed l r t a -> Maybe (Active Free (Open l) r t a)
freeL = free >=> openL

ufreeL :: Ord t => Active Fixed l r t a -> Active Free (Open l) r t a
ufreeL a = case freeL a of
                   Nothing -> error "ufreeL on empty era"
                   Just a' -> a'

openR :: Ord t => Active Free l r t a -> Maybe (Active Free l (Open r) t a)
openR (Active e f) = Active <$> openREra e <*> Just f

uopenR :: Ord t => Active Free l r t a -> Active Free l (Open r) t a
uopenR a = case openR a of
                  Nothing -> error "uopenR on empty era"
                  Just a' -> a'

openL :: Ord t => Active Free l r t a -> Maybe (Active Free (Open l) r t a)
openL (Active e f) = Active <$> openLEra e <*> Just f

uopenL :: Ord t => Active Free l r t a -> Active Free (Open l) r t a
uopenL a = case openL a of
                  Nothing -> error "uopenL on empty era"
                  Just a' -> a'

closeR :: (Eq t, Num t) => a -> Active Free l O t a -> Active Free l C t a
closeR a (Active e f) = Active (closeREra e) f'
  where
    f' = case e of
           EmptyEra           -> f
           (Era _ (Finite y)) -> (\t -> if t == y then a else f t)

closeL :: (Eq t, Num t) => a -> Active Free O r t a -> Active Free C r t a
closeL a (Active e f) = Active (closeLEra e) f'
  where
    f' = case e of
           EmptyEra           -> f
           (Era (Finite x) _) -> (\t -> if t == x then a else f t)

(<<>>) :: forall l1 r1 l2 r2 t a.
         (Clock t, Deadline r1 l2 t a)
      => Active Free l1 r1 t a -> Active Free l2 r2 t a
      -> Active Free l1 r2 t a
Active era1@EmptyEra f <<>> Active era2@EmptyEra _ = Active (eraSeq era1 era2) f

Active era1@EmptyEra _ <<>> Active era2@(Era {}) f = Active (eraSeq era1 era2) f

Active era1@(Era {}) f <<>> Active era2@EmptyEra _ = Active (eraSeq era1 era2) f

-- Know e1 and s2 are Finite because of Deadline constraint
Active era1@(Era _ (Finite e1)) f1 <<>> Active era2@(Era (Finite s2) _) f2
  = Active (eraSeq era1 era2)
           (\t -> choose (Proxy :: Proxy r1) (Proxy :: Proxy l2)
                    e1 t (f1 t) (shift (e1 .-. s2) f2 t))

instance Deadline r l t a => Semigroup (Active Free l r t a) where
  (<>) = (<<>>)

instance Deadline r l t a => Monoid (Active Free l r t a) where
  mappend = (<>)
  mempty  = lemma_Compat_sym (Proxy :: Proxy r) (Proxy :: Proxy l)
          $ Active emptyFreeEra (const undefined)
            -- OK to use 'undefined' above since this function can
            -- never be called.

-- this is not unsafe because we restrict the left endpoint to not be
-- open, which is usually fine since in the most common use cases we
-- will have either C or I.
(<>>) :: (Clock t, Ord t, Deadline (Open r1) l2 t a, NotOpen l1)
      => Active Free l1 r1 t a -> Active Free l2 r2 t a
      -> Active Free l1 r2 t a
a1 <>> a2 = uopenR a1 <<>> a2


-- crazy idea: maybe we don't need these at all?  i.e. maybe the way
-- you use the API is to work with free actives, and sometimes you
-- need to construct an active using a fixed time frame and then free
-- it, but you never "un-free" a free down to a fixed?  Well, in
-- any case there's nothing wrong with anchorStart and anchorEnd, but
-- perhaps this means we don't need the elaborate system of anchor
-- points I was originally imagining.

anchorStart
  :: forall l r t a. (IsFinite l, AreNotOpen l r, Clock t)
  => t -> Active Free l r t a -> Active Fixed l r t a
anchorStart t (Active (Era (Finite s) e) f)
  = Active (Era (Finite t) (shift d e)) (shift d f)
  where d = t .-. s

  -- EmptyEra case can't happen because of AreNotOpen l r constraint.
  -- Era Infinity _  case can't happen because of IsFinite l constraint.

anchorEnd
  :: forall l r t a. (IsFinite r, AreNotOpen l r, Clock t)
  => t -> Active Free l r t a -> Active Fixed l r t a
anchorEnd t (Active (Era s (Finite e)) f)
  = Active (Era (shift d s) (Finite t)) (shift d f)
  where d = t .-. e

  -- EmptyEra case can't happen because of AreNotOpen l r constraint.
  -- Era _ Infinity  case can't happen because of IsFinite r constraint.

------------------------------------------------------------
-- Derived API
------------------------------------------------------------

runActive :: Active Fixed l r t a -> t -> a
runActive = view activeFun

interval :: (Ord t, IsEraType f, EraConstraints f C C) => t -> t -> Active f C C t ()
interval s e = Active (mkEra s e) (const ())

(...) :: (Ord t, IsEraType f, EraConstraints f C C) => t -> t -> Active f C C t ()
(...) = interval

ui :: (Num t, Ord t) => Active Fixed C C t t
ui = timeValued (0 ... 1)

timeValued :: Active Fixed l r t a -> Active Fixed l r t t
timeValued = mapT const

-- XXX should check if duration is <= 0?
dur :: (Clock t, Ord t, Num t) => Diff t -> Active Free C C t ()
dur d = fromJust . free $ interval 0 (0 .+^ d)

backwards :: (Clock t, IsEraType f, IsFinite l, IsFinite r)
    => Active f l r t a -> Active f r l t a
backwards (Active EmptyEra f) = Active (reverseEra EmptyEra) f
backwards (Active er@(Era (Finite s) (Finite e)) f) = Active (reverseEra er) f'
  where
    f' t = f (e .+^ (s .-. t))

(*>>) :: (IsFinite l, Clock t) => Active f l r t a -> Rational -> Active f l r t a
(*>>) = flip stretchFromStart

stretchFromStart :: (IsFinite l, Clock t) => Rational -> Active f l r t a -> Active f l r t a
stretchFromStart 0 _ = error "stretchFromStart by 0"  -- XXX ?
stretchFromStart _ a@(Active EmptyEra _) = a
stretchFromStart k (Active e@(Era (Finite s) Infinity) f)
  = Active e (stretchFunFromStart s k f)
stretchFromStart k (Active (Era (Finite s) (Finite e)) f)
  = Active (Era (Finite s) (Finite e')) (stretchFunFromStart s k f)
  where
    e' = s .+^ (fromRational k *^ (e .-. s))

stretchFunFromStart :: (Clock t) => t -> Rational -> (t -> a) -> t -> a
stretchFunFromStart s k f t = f (s .+^ ((t .-. s) ^/ fromRational k))

(<<*) :: (IsFinite r, Clock t) => Rational -> Active f l r t a -> Active f l r t a
(<<*) = stretchFromEnd

stretchFromEnd :: (IsFinite r, Clock t) => Rational -> Active f l r t a -> Active f l r t a
stretchFromEnd 0 _ = error "stretchFromEnd by 0" -- XXX ?
stretchFromEnd _ a@(Active EmptyEra _) = a
stretchFromEnd k (Active er@(Era Infinity (Finite e)) f)
  = Active er (stretchFunFromEnd e k f)
stretchFromEnd k (Active (Era (Finite s) (Finite e)) f)
  = Active (Era (Finite s') (Finite e)) (stretchFunFromEnd e k f)
  where
    s' = e .-^ (fromRational k *^ (e .-. s))

stretchFunFromEnd :: (Clock t) => t -> Rational -> (t -> a) -> t -> a
stretchFunFromEnd e k f t = f (e .-^ ((e .-. t) ^/ fromRational k))

-- stretchTo
-- stretchAs

snapshot :: (IsEraType f, Ord t)
         => t -> Active Fixed l r t a -> Maybe (Active f I I t a)
snapshot t (Active er f)
  | er `eraContains` t = Just $ pureA (f t)
  | otherwise       = Nothing

clamp :: Active f C C t a -> Active f I I t a
clamp (Active (Era (Finite s) (Finite e)) f)
  = undefined
--    Active (Era Infinity Infinity) undefined  -- XXX something to do
                                                -- with Clock or
                                                -- Deadline?

clampBefore :: Active f C r t a -> Active f I r t a
clampBefore = undefined

clampAfter :: Active f l C t a -> Active f l I t a
clampAfter = undefined

-- clampTo
-- clampAs

padActive :: a -> Active f C C t a -> Active f I I t a
padActive = undefined

padBefore :: a -> Active f C r t a -> Active f I r t a
padBefore = undefined

padAfter :: a -> Active f l C t a -> Active f l I t a
padAfter = undefined

-- padTo
-- padAs

-- unionPar

movie :: (Clock t, Ord t, Deadline O C t a) => [Active Free C C t a] -> Active Free C C t a
movie [] = error "empty movie" -- XXX ?
movie xs = foldr1 (<>>) xs
  -- XXX use a balanced fold?

discrete :: (Clock t, Ord t, Num t, FractionalOf t Rational) => [a] -> Active Fixed C C t a
discrete [] = error "Data.Active.discrete must be called with a non-empty list."
discrete xs = f <$> ui
  where
    f t
      | toFractionalOf t <= (0 :: Rational) = arr ! 0
      | toFractionalOf t >= (1 :: Rational) = arr ! (n-1)
      | otherwise = arr ! floor (toFractionalOf t * fromIntegral n :: Rational)
    n   = length xs
    arr = listArray (0, n-1) xs

simulate :: (Clock t, FractionalOf t Rational)
         => Rational -> Active Free C C t a -> [a]
simulate _ (Active EmptyEra _) = []
simulate rate (Active (Era (Finite s) (Finite e)) f)
  = map (f . toTime) [s', s' + (1^/rate) .. e']
  where
    s', e' :: Rational
    s' = fromTime s
    e' = fromTime e
