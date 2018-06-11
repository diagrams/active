{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor  #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}

module Active.Class where

import           Control.Applicative
import           Control.Monad
import           Data.List.NonEmpty  (NonEmpty (..))
import           Data.Ratio
import           Data.Semigroup
import qualified Data.Vector         as V
import           Linear.Vector

import           Active.Duration

type Dur = Duration Rational

------------------------------------------------------------
-- Pairs

-- This type & accompanying instances probably exists in some
-- canonical library but I'm not sure which one off the top of my head.

-- Ah, Tuplanolla on #haskell pointed me to the uniform-pair package
-- by Conal Elliott, but no one seems to use it (and it's not on
-- Stackage despite https://github.com/conal/uniform-pair/issues/4).

-- dmwit suggested  Product Identity Identity.

-- Tuplanolla suggested defining
--   newtype Join f a = Join {getJoin :: f a a}   etc.

-- glguy suggested V2 from linear.

-- jle` suggeted just using (->) Bool.

infix 1 :><:

data Pair a = a :><: a
  deriving (Show, Eq, Ord, Functor, Foldable)

revP :: Pair a -> Pair a
revP (x :><: y) = y :><: x

fstP :: Pair a -> a
fstP (x :><: _) = x

sndP :: Pair a -> a
sndP (_ :><: y) = y

uncurryP :: (a -> a -> b) -> Pair a -> b
uncurryP f (x :><: y) = f x y

instance Semigroup a => Semigroup (Pair a) where
  (l1 :><: r1) <> (l2 :><: r2) = (l1 <> l2) :><: (r1 <> r2)

instance (Semigroup a, Monoid a) => Monoid (Pair a) where
  mappend = (<>)
  mempty  = mempty :><: mempty

instance Applicative Pair where
  pure  = return
  (<*>) = ap

instance Monad Pair where
  return a = a :><: a
  p >>= k = join' (k <$> p)
    where
      join' ((x :><: _) :><: (_ :><: y)) = x :><: y

------------------------------------------------------------
-- The Activated type class (open to better name suggestions)

class Applicative act => Activated act where

  -- This is called 'dur' in the current Active.hs, but I think I like
  -- 'time' better.  It is supposed to represent a bi-infinite value
  -- which always takes on the value t at time t.
  time      :: act Rational

  -- Get the future & past duration of an active value.
  duration  :: act a -> Pair Dur

  -- Snip an active into its past and its future.
  snip      :: act a -> Pair (act a)

  -- Shift time by the given amount.  A positive value means part of
  -- the value that was the future now becomes the past (i.e. "fast
  -- forward").  A negative value is "rewinding", i.e. some of the
  -- past becomes the future.
  shift     :: Rational -> act a -> (Rational, act a)

  -- Stretch time by the given amount
  stretch   :: Rational -> act a -> act a

  -- Switch past and future.
  rev       :: act a -> act a
  stitch    :: Semigroup a => act a -> act a -> act a
  par       :: Semigroup a => act a -> act a -> act a

{-
   For convenience in stating the laws, define

   andThen a b = getLast (stitch (Last <$> a) (Last <$> b))


   Laws:

   duration time = pure Forever
   uncurryP andThen . snip = id
   duration = join . fmap duration . snip

   shift x a = (x', a')  ==>  shift (-x') a' = (-x', a)

   (c >= 0)  ==>  stretch c = map (c*) . duration

   rev . rev = id

   ...other laws...

-}

------------------------------------------------------------
-- Derived combinators

-- Many of these are taken from Active.hs, showing how to reimplement
-- the existing library in terms of this new type class.

futureDuration :: Activated act => act a -> Dur
futureDuration = sndP . duration

pastDuration :: Activated act => act a -> Dur
pastDuration = fstP . duration

future :: Activated act => act a -> act a
future = sndP . snip

past :: Activated act => act a -> act a
past = fstP . snip

activeF :: Activated act => Rational -> (Rational -> a) -> act a
activeF d f = cut d (activeI f)

activeI :: Activated act => (Rational -> a) -> act a
activeI f = f <$> future time

active :: Activated act => Dur -> (Rational -> a) -> act a
active Forever f      = activeI f
active (Duration d) f = activeF d f

instant :: Activated act => a -> act a
instant = lasting 0

lasting :: Activated act => Rational -> a -> act a
lasting d = activeF d . const

ui :: Activated act => act Rational
ui = active 1 id

interval :: Activated act => Rational -> Rational -> act Rational
interval a b
  | a <= b    = active (toDuration (b - a)) (a+)
  | otherwise = active (toDuration (a - b)) (a-)

discreteNE :: Activated act => NonEmpty a -> act a
discreteNE (a :| as) = active 1 f
  where
    f t
      | t == 1    = V.unsafeLast v
      | otherwise = V.unsafeIndex v $ floor (t * fromIntegral (V.length v))
    v = V.fromList (a:as)

-- Convenience variant of shift that throws away the shift amount
shift' :: Activated act => Rational -> act a -> act a
shift' x a = snd (shift x a)

-- Limit the future duration by shifting, forgetting any
-- remaining future, then shifting forward again
cut :: Activated act => Rational -> act a -> act a
cut r a = shift' (-r') (past a')
  where
    (r', a') = shift r a

-- Still not sure what to do with 'omit' and 'slice'

-- 'backwards' combinator which switches start and end.  Note this is
-- not quite the same thing as 'rev': it is rev and a shift.  This
-- version simply acts as 'rev' on an infinite argument.  Could also
-- have a partial version which throws an error.
backwards :: Activated act => act a -> act a
backwards a = case futureDuration a of
  Forever    -> rev a
  Duration d -> rev a

------------------------------------------------------------
-- Simplest possible instance: an interval is just a pair of a future
-- duration and a past duration.
--
-- It would probably make more sense to get rid of the type parameter
-- and then use Const Interval, but dealing with all the Const newtype
-- wrappers would get annoying

newtype Interval a = I { getInterval :: Pair Dur }
  deriving (Show, Functor)

onInterval :: (Pair Dur -> Pair Dur) -> Interval a -> Interval b
onInterval f (I a) = I (f a)

onInterval2 :: (Pair Dur -> Pair Dur -> Pair Dur) -> Interval a -> Interval b -> Interval c
onInterval2 f (I a) (I b) = I (f a b)

inInterval :: Rational -> Interval a -> Bool
inInterval r (I (lo :><: hi)) = Duration (-r) <= lo && Duration r <= hi

-- The semigroup instance just takes a pointwise minimum.
instance Semigroup (Interval a) where
  (<>) = onInterval2 (liftA2 min)

-- Forever :><: Forever is the identity.
instance Monoid (Interval a) where
  mappend = (<>)
  mempty  = I (pure Forever)

-- The Applicative instance is just like the Monoid instance, since
-- the 'a' in 'Interval a' is phantom
instance Applicative Interval where
  pure  = const mempty
  (<*>) = onInterval2 (liftA2 min)

-- The Activated instance for Interval just keeps track of durations; it
-- doesn't care about 'values'.
instance Activated Interval where

  time = I (Forever :><: Forever)
  duration = getInterval

  snip (I (dL :><: dR)) = I (dL :><: 0) :><: I (0 :><: dR)
  stretch c = onInterval (fmap (c*^))

  rev = onInterval revP

  stitch (I (dL1 :><: dR1)) (I (dL2 :><: dR2))
    = I $ max dL1 (dL2 - dR1) :><: dR1 + dR2

  par = onInterval2 (liftA2 max)

  shift x (I (dL :><: dR))
    -- positive shift = foward, i.e. shift the future into the past
    | x >= 0    = (fwd,  I $ dL + fwdD :><: dR - fwdD)
    -- negative shift = backwards, i.e. shift the past into the future
    | otherwise = (-bwd, I $ dL - bwdD :><: dR + bwdD )
    where
      -- max amount we could possibly ffwd is dR
      fwdD@(Duration fwd) = min (Duration x) dR
      -- max amount we could possibly rewind is dL
      bwdD@(Duration bwd) = min (Duration (-x)) dL

------------------------------------------------------------
-- Simple instance giving main reference semantics

-- For now this is copied here from Active.hs; eventually the
-- definition and instance should move there

data Active :: * -> * where
  Active   :: (Rational -> a) -> Interval () -> Active a
  deriving Functor

instance Applicative Active where
  pure a = a <$ time
  Active f1 i1 <*> Active f2 i2 = Active (f1 <*> f2) (i1 <> i2)

instance Activated Active where
  time                    = Active id (() <$ time)
  duration   (Active _ i) = duration i
  snip       (Active f i) = Active f <$> snip i
  stretch  c (Active f i) = Active (f . (/c))   (stretch c i)
  rev        (Active f i) = Active (f . negate) (rev i)

  stitch   a@(Active f1 i1@(I (_ :><: Forever))) _ = a
  stitch     (Active f1 i1@(I (_ :><: Duration hi1))) (Active f2 i2) = Active f (stitch i1 i2)
    where
      f t
        | t `inInterval` i1 && ((t - hi1) `inInterval` i2) = f1 t <> f2 (t - hi1)
        | t `inInterval` i1                                = f1 t
        | otherwise                                        = f2 (t - hi1)

  par        (Active f1 i1) (Active f2 i2) = Active f i
    where
      i = par i1 i2
      f t
        | t `inInterval` i  = (f1 <> f2) t
        | t `inInterval` i1 = f1 t
        | otherwise         = f2 t

  shift    x (Active f i) = (x', Active (f . (+x')) i')
    where
      (x', i') = shift x i

runActive :: Active a -> (Rational -> a)
runActive (Active f i) t
  | t `inInterval` i = f t
  | otherwise = error "runActive: Active value evaluated outside its domain"


-- Sample only from the future.
samples :: Rational -> Active a -> [a]
samples fr _ | fr <= 0   = error "Frame rate can't be <= 0"
samples fr (Active f (I (_ :><: fut)))
  = case fut of
      Forever    -> map f . map (/fr) $ [0 ..]
      Duration d -> map f . takeWhile (<= d) . map (/fr) $ [0 ..]
