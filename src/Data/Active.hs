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
    ( -- * Time

      Time, time, Clock(..)
    , Duration, duration, Waiting(..)
    , Shifty(..)

      -- * Endpoints
    , EndpointType(..), Endpoint(..)

      -- * Eras

    , EraType(..), IsEraType(..), Era

      -- ** Constructors
    , emptyEra
    , emptyFixedEra
    , emptyFreeEra
    , always
    , mkEra
    , mkEra'

      -- ** Accessors

    , eraIsEmpty
    , eraContains
    , eraR, eraL

      -- ** Operations

    , eraIsect
    , eraSeq
    , reverseEra

    , freeEra
    , openREra
    , openLEra
    , closeREra
    , closeLEra

      -- * Active

    , Active

      -- ** Constructors

    , emptyActive, pureA
    , interval, mkActive, (...), (..$)
    , timeValued, ui
    , dur
    , snapshot
    , discrete

      -- ** Accessors

    , era, atTime, uatTime
    , atR, atRm, atL, atLm

      -- * Active operations

      -- ** General operations

    , mapT, appA, pairA

      -- ** Converting between fixed and free

    , asFixed, asFree

    , free, ufree
    , freeR, ufreeR
    , freeL, ufreeL
    , anchorL, anchorR

      -- ** Fiddling with endpoints
    , openR, uopenR
    , openL, uopenL
    , closeR, closeL

      -- ** Composition

    , parA
    , (<<>>), (<>>), movie

      -- ** Modification

    , backwards
    , stretchR, (*>>)
    , stretchL, (<<*)
    , syncTo, syncAs
    , clamp, clampL, clampR
    , padActive, padL, padR

      -- ** Discretization

    , simulate

      -- * @Active'@

    , Active'(..), withActive, onActive'

    )
    where

import           Control.Applicative  (Applicative (..), (<$>), (<*>))
import           Control.Lens         (Lens', generateSignatures, lensRules,
                                       makeLensesWith, view, (%~), (&), (.~),
                                       (^.))
import           Control.Monad        (ap, (>=>))
import           Data.AffineSpace     (Diff, (.+^), (.-.), (.-^))
import           Data.Array           (listArray, (!))
import           Data.Maybe           (fromJust, fromMaybe)
import           Data.Proxy           (Proxy (..))
import           Data.Semigroup       (Monoid (..), Semigroup (..))
import           Data.VectorSpace     ((*^), (^/))

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

-- | Like 'fmap', but extended to have access to the time values as
--   well as the values of type @a@.  In other words, 'fmap' enables
--   \"time-independent\" transformations (applying the same
--   transformation uniformly without regard to time), whereas 'mapT'
--   enables \"time-dependent\" transformations (applying a
--   transformation indexed by time).
mapT :: (t -> a -> b) -> Active Fixed l r t a -> Active Fixed l r t b
mapT g (Active e f) = Active e (g `ap` f)

-- | An empty @Active@ value, which is defined nowhere.
emptyActive :: EmptyConstraints f l r => Active f l r t a
emptyActive = Active emptyEra (const undefined)

-- | Create a finite @Active@ with the given start and end times,
-- taking on values according to the given function.
mkActive
  :: (Ord t, IsEraType f, EraConstraints f C C)
  => t -> t -> (t -> a) -> Active f C C t a
mkActive s e f = Active (mkEra s e) f

-- | A synonym for 'mkActive', designed to be used something like
--
--   @
--   (1 ..$ 4) (\\t -> ...)
--   @
--
--   The name is supposed to be reminiscent of a combination between
--   @(...)@ (since it creates a finite interval) and @($)@ (since it
--   is applied to a function of time).
(..$)
  :: (Ord t, IsEraType f, EraConstraints f C C)
  => t -> t -> (t -> a) -> Active f C C t a
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

infixl 4 `appA`

-- | A specialized variant of 'appA'.
pairA :: Ord t
      => Active Fixed l  r  t a
      -> Active Fixed l' r' t b
      -> Active Fixed (Isect l  l') (Isect r  r') t (a,b)
pairA a b = (,) <$> a `appA` b

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

-- | Turn a fixed @Active@ into a free, by \"forgetting\" the concrete
--   location of its era.  Returns @Nothing@ iff given the empty fixed
--   era as input (the empty fixed era has no free counterpart); see
--   also 'ufree'.
free :: Active Fixed l r t a -> Maybe (Active Free l r t a)
free (Active e f) = Active <$> freeEra e <*> Just f

-- | An \"unsafe\" variant of 'free' which throws an error iff given
--   the empty era as input.  Can be more convenient than 'free' if
--   you know that its argument is not empty, since it does not
--   require dealing with @Maybe@.
ufree :: Active Fixed l r t a -> Active Free l r t a
ufree a = case free a of
                  Nothing -> error "ufree called on empty era"
                  Just a' -> a'

-- | Turn a fixed @Active@ into a free with an open right endpoint, by
--   \"forgetting\" both the concrete location of its era and the
--   value at the right endpoint (if it is finite).  Returns @Nothing@
--   iff given the empty era as input; see also 'ufreeR'.
freeR :: Ord t => Active Fixed l r t a -> Maybe (Active Free l (Open r) t a)
freeR = free >=> openR

-- | An \"unsafe\" variant of 'freeR' which throws an error iff given
--   an active with an empty era as input.  Can be more convenient
--   than 'freeR' if you know that its argument is not empty, since it
--   does not require dealing with @Maybe@.
ufreeR :: Ord t => Active Fixed l r t a -> Active Free l (Open r) t a
ufreeR a = case freeR a of
                   Nothing -> error "ufreeR on empty era"
                   Just a' -> a'

-- | Turn a fixed @Active@ into a free with an open left endpoint, by
--   \"forgetting\" both the concrete location of its era and the
--   value at the left endpoint (if it is finite).  Returns @Nothing@
--   iff given the empty era as input; see also 'ufreeL'.
freeL :: Ord t => Active Fixed l r t a -> Maybe (Active Free (Open l) r t a)
freeL = free >=> openL

-- | An \"unsafe\" variant of 'freeL' which throws an error iff given
--   an active with an empty era as input.  Can be more convenient
--   than 'freeL' if you know that its argument is not empty, since it
--   does not require dealing with @Maybe@.
ufreeL :: Ord t => Active Fixed l r t a -> Active Free (Open l) r t a
ufreeL a = case freeL a of
                   Nothing -> error "ufreeL on empty era"
                   Just a' -> a'

-- | Open the right endpoint of a free active, forgetting the value
--   defined there.  Returns @Nothing@ iff its argument has a
--   left-open right-closed empty era (see 'openREra').  See also
--   'uopenR'.
openR :: Ord t => Active Free l r t a -> Maybe (Active Free l (Open r) t a)
openR (Active e f) = Active <$> openREra e <*> Just f

-- | An \"unsafe\" variant of 'openR' which throws an error iff given
--   an active with a left-open right-closed empty era as input.  Can
--   be more convenient than 'openR' if you know that its argument is
--   not of the prohibited shape, since it does not require dealing
--   with @Maybe@.
uopenR :: Ord t => Active Free l r t a -> Active Free l (Open r) t a
uopenR a = case openR a of
                  Nothing -> error "uopenR on empty era"
                  Just a' -> a'

-- | Open the left endpoint of a free active, forgetting the value
--   defined there.  Returns @Nothing@ iff its argument has a
--   right-open left-closed empty era (see 'openLEra').  See also
--   'uopenL'.
openL :: Ord t => Active Free l r t a -> Maybe (Active Free (Open l) r t a)
openL (Active e f) = Active <$> openLEra e <*> Just f

-- | An \"unsafe\" variant of 'openL' which throws an error iff given
--   an active with a left-closed right-open empty era as input.  Can
--   be more convenient than 'openL' if you know that its argument is
--   not of the prohibited shape, since it does not require dealing
--   with @Maybe@.
uopenL :: Ord t => Active Free l r t a -> Active Free (Open l) r t a
uopenL a = case openL a of
                  Nothing -> error "uopenL on empty era"
                  Just a' -> a'

-- | Turn an @Active@ with an open right endpoint into one with a
--   closed right endpoint, by providing a value at the endpoint.
closeR :: (Eq t, Num t) => a -> Active Free l O t a -> Active Free l C t a
closeR a (Active e f) = Active (closeREra e) f'
  where
    f' = case e of
           EmptyEra           -> f
           (Era _ (Finite y)) -> (\t -> if t == y then a else f t)

-- | Turn an @Active@ with an open left endpoint into one with a
--   closed left endpoint, by providing a value at the endpoint.
closeL :: (Eq t, Num t) => a -> Active Free O r t a -> Active Free C r t a
closeL a (Active e f) = Active (closeLEra e) f'
  where
    f' = case e of
           EmptyEra           -> f
           (Era (Finite x) _) -> (\t -> if t == x then a else f t)

-- | Sequential composition of free 'Active' values with compatible
--   endpoint types.
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

-- | Biased sequential composition of free 'Active' values, which
--   throws away the right endpoint of its first argument.
(<>>) :: (Clock t, Ord t, Deadline (Open r1) l2 t a, NotOpen l1)
      => Active Free l1 r1 t a -> Active Free l2 r2 t a
      -> Active Free l1 r2 t a
a1 <>> a2 = uopenR a1 <<>> a2

-- Note, the above is not unsafe because we restrict the left endpoint to not be
-- open, which is usually fine since in the most common use cases we
-- will have either C or I.


-- crazy idea: maybe we don't need these at all?  i.e. maybe the way
-- you use the API is to work with free actives, and sometimes you
-- need to construct an active using a fixed time frame and then free
-- it, but you never "un-free" a free down to a fixed?  Well, in
-- any case there's nothing wrong with anchorStart and anchorEnd, but
-- perhaps this means we don't need the elaborate system of anchor
-- points I was originally imagining.

-- | \"Fix\" a free active by anchoring its (finite) left endpoint to
--   a specific time.
anchorL
  :: forall l r t a. (IsFinite l, AreNotOpen l r, Clock t)
  => t -> Active Free l r t a -> Active Fixed l r t a
anchorL t (Active (Era (Finite s) e) f)
  = Active (Era (Finite t) (shift d e)) (shift d f)
  where d = t .-. s

  -- EmptyEra case can't happen because of AreNotOpen l r constraint.
  -- Era Infinity _  case can't happen because of IsFinite l constraint.

-- | \"Fix\" a free active by anchoring its (finite) right endpoint to
--   a specific time.
anchorR
  :: forall l r t a. (IsFinite r, AreNotOpen l r, Clock t)
  => t -> Active Free l r t a -> Active Fixed l r t a
anchorR t (Active (Era s (Finite e)) f)
  = Active (Era (shift d s) (Finite t)) (shift d f)
  where d = t .-. e

  -- EmptyEra case can't happen because of AreNotOpen l r constraint.
  -- Era _ Infinity  case can't happen because of IsFinite r constraint.

------------------------------------------------------------
-- Derived API
------------------------------------------------------------

-- | \"Run\" a fixed @Active@ value, turning it into a partial
--   function from time.
atTime :: Ord t => Active Fixed l r t a -> t -> Maybe a
atTime a t
  | (a ^. era) `eraContains` t = Just $ (a ^. activeFun) t
  | otherwise                  = Nothing

-- | An \"unsafe\" variant of 'atTime' which does not check whether
--   the input time value lies within the era.
uatTime :: Active Fixed l r t a -> t -> a
uatTime = view activeFun

-- | Get the value at the right end of a closed @Active@, or @Nothing@
--   if it is empty.
atR :: Ord t => Active f l C t a -> Maybe a
atR (Active EmptyEra _)             = Nothing
atR (Active (Era _ (Finite end)) f) = Just $ f end

-- Note, we could implement atR (and similarly atL) in terms of eraR
-- and atTime as
--
--   atR a = eraR (a ^. era) >>= atTime a
--
-- but then the era type would be restricted to only Fixed.  It is
-- safe to provide atR for either era type, but eraR and atTime are
-- only safe for Fixed.

-- | Get the value at the right end of a closed @Active@, converting
--   to 'mempty' if the @Active@ is empty.  This is provided for
--   convenience and is equivalent to @fromMaybe mempty . atR@.
atRm :: (Monoid a, Ord t) => Active f l C t a -> a
atRm = fromMaybe mempty . atR

-- | Get the value at the left end of a closed @Active@, or @Nothing@
--   if it is empty.
atL :: Ord t => Active f C r t a -> Maybe a
atL (Active EmptyEra _) = Nothing
atL (Active (Era (Finite start) _) f) = Just $ f start

-- | Get the value at the left end of a closed @Active@, converting to
--   'mempty' if the @Active@ is empty.  This is provided for
--   convenience and is equivalent to @fromMaybe mempty . atL@.
atLm :: (Monoid a, Ord t) => Active f C r t a -> a
atLm = fromMaybe mempty . atL

-- | Create a finite @Active@ with the constant value @()@.
interval :: (Ord t, IsEraType f, EraConstraints f C C) => t -> t -> Active f C C t ()
interval s e = Active (mkEra s e) (const ())

-- | A synonym for 'interval'.
(...) :: (Ord t, IsEraType f, EraConstraints f C C) => t -> t -> Active f C C t ()
(...) = interval

-- | An @Active@ defined on the unit interval [0,1], taking on the
--   value @t@ at time @t@.  Equivalent to @'timeValued' (0 ... 1)@.
ui :: (Num t, Ord t) => Active Fixed C C t t
ui = timeValued (0 ... 1)

-- | Make an @Active@ which takes on the value @t@ at time @t@.  For
--   example, @timeValued (3 ... 5)@ creates a duration-2 @Active@,
--   starting at time 3 and ending at time 5, which takes on values
--   from 3 to 5 over the course of the interval.
timeValued :: Active Fixed l r t a -> Active Fixed l r t t
timeValued = mapT const

-- | Create a free @Active@ of the given duration, taking on the
--   constant value @()@.  Note that the absolute value of the given
--   duration is used.
dur :: forall t. (Clock t, Ord t, Num t) => Diff t -> Active Free C C t ()
dur d = fromJust . free $ interval 0 t'
  where
    t' | (0 :: t) .+^ d >= 0  = 0 .+^ d
       | otherwise            = 0 .-^ d

-- | Flip around a finite 'Active' value so it runs backwards, with
--   the value at the start time mapped to the end time and vice versa.
backwards :: (Clock t, IsEraType f, IsFinite l, IsFinite r)
    => Active f l r t a -> Active f r l t a
backwards (Active EmptyEra f) = Active (reverseEra EmptyEra) f
backwards (Active er@(Era (Finite s) (Finite e)) f) = Active (reverseEra er) f'
  where
    f' t = f (e .+^ (s .-. t))

-- | Operator synonym for 'stretchR'.
(*>>) :: (IsFinite l, Clock t) => Active f l r t a -> Rational -> Active f l r t a
(*>>) = flip stretchR

-- | Stretch the era of an @Active@ value by the given factor \"to the
--   right\", /i.e./ keeping its left endpoint fixed.
stretchR :: (IsFinite l, Clock t) => Rational -> Active f l r t a -> Active f l r t a
stretchR 0 _ = error "stretchR by 0"  -- XXX ?
stretchR _ a@(Active EmptyEra _) = a
stretchR k (Active e@(Era (Finite s) Infinity) f)
  = Active e (stretchFunR s k f)
stretchR k (Active (Era (Finite s) (Finite e)) f)
  = Active (Era (Finite s) (Finite e')) (stretchFunR s k f)
  where
    e' = s .+^ (fromRational k *^ (e .-. s))

stretchFunR :: (Clock t) => t -> Rational -> (t -> a) -> t -> a
stretchFunR s k f t = f (s .+^ ((t .-. s) ^/ fromRational k))

-- | Operator synonym for 'stretchL'.
(<<*) :: (IsFinite r, Clock t) => Rational -> Active f l r t a -> Active f l r t a
(<<*) = stretchL

-- | Stretch the era of an @Active@ value by the given factor \"to the
--   left\", /i.e./ keeping its right endpoint fixed.
stretchL :: (IsFinite r, Clock t) => Rational -> Active f l r t a -> Active f l r t a
stretchL 0 _ = error "stretchL by 0" -- XXX ?
stretchL _ a@(Active EmptyEra _) = a
stretchL k (Active er@(Era Infinity (Finite e)) f)
  = Active er (stretchFunL e k f)
stretchL k (Active (Era (Finite s) (Finite e)) f)
  = Active (Era (Finite s') (Finite e)) (stretchFunL e k f)
  where
    s' = e .-^ (fromRational k *^ (e .-. s))

stretchFunL :: (Clock t) => t -> Rational -> (t -> a) -> t -> a
stretchFunL e k f t = f (e .-^ ((e .-. t) ^/ fromRational k))

-- stretchTo
-- stretchAs

syncTo :: Era f l r t -> Active f l r t a -> Active f l r t a
syncTo = undefined

syncAs :: Active f l r t a -> Active f l r t a -> Active f l r t a
syncAs = undefined

-- | Take a \"snapshot\", /i.e./ sample an @Active@ at a single point
--   in time and make an infinite @Active@ which is constantly the sampled value.
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

clampL :: Active f C r t a -> Active f I r t a
clampL = undefined

clampR :: Active f l C t a -> Active f l I t a
clampR = undefined

-- clampTo
-- clampAs

padActive :: a -> Active f C C t a -> Active f I I t a
padActive = undefined

padL :: a -> Active f C r t a -> Active f I r t a
padL = undefined

padR :: a -> Active f l C t a -> Active f l I t a
padR = undefined

-- padTo
-- padAs

-- unionPar

-- | Make a \"movie\" out of a sequence of free 'Active' values,
--   composing them with the biased sequential composition operator
--   '<>>'.  The input list must be non-empty.
movie :: (Clock t, Ord t, Deadline O C t a) => [Active Free C C t a] -> Active Free C C t a
movie [] = error "empty movie" -- XXX ?
movie xs = foldr1 (<>>) xs
  -- XXX use a balanced fold?

-- | Make an @Active@ value with evenly spaced discrete transitions
--   between the elements of a given list.  Given a list @as@ of
--   length @n@, it takes on the values
--
--   * @as !! 0@ from time 0 up to but not including time @1\/(n-1)@;
--
--   * @as !! 1@ from time @1\/(n-1)@ up to but not including time @2\/(n-1)@;
--
--   * @as !! k@ from time @k\/(n-1)@ up to but not including time @(k+1)\/(n-1)@;
--
--   * @as !! n@ precisely at time @1@.
--
--   It is an error to provide @discrete@ with an empty list.
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

-- | @simulate rate a@ generates a list of values sampled from @a@, at
--   a granularity of @rate@ samples per unit of time.  The first
--   value is taken precisely at the start time of @a@; subsequent
--   values are taken every @1\/rate@ time units, with the final value
--   taken at or before the end time of @a@.
simulate :: (Clock t, FractionalOf t Rational)
         => Rational -> Active Free C C t a -> [a]
simulate _ (Active EmptyEra _) = []
simulate rate (Active (Era (Finite s) (Finite e)) f)
  = map (f . toTime) . takeWhile (<= e') . iterate (+ (1^/rate)) $ s'
  where
    s', e' :: Rational
    s' = fromTime s
    e' = fromTime e

-- More API ideas
--
--   * get the value at the start or end of a finite fixed
--   * like clamp but extend a certain amount of time
--   * trimTo, which takes something like (1...3)
--     Probably don't need all these functions which take Eras--- just use Active ().
