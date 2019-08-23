import           Data.MemoTrie
import           Data.Ratio
import           Data.Word
import           System.Random.TF.Gen
import           System.Random.TF.Init

-- Would it be faster/easier to just run each rational through some
-- hash function?

rand :: RandomGen g => g -> Word32
rand = fst . next

left, right, value, subtree :: RandomGen g => g -> g
left  = fst . split
right = snd . split
value   = left
subtree = right

-- Given a seed, assign an independent, pseudorandom 32-bit value to
-- every positive rational using the Calkin-Wilf tree and a splittable
-- PRNG from tf-random.

-- At each node we need to do an extra split: the generator that will
-- make the value for the node on the left, and the generator which
-- will be recursively split to generate the left and right subtrees
-- on the right.

-- This could probably be improved with a bit of memoization.

randomQ :: Int -> (Rational -> Word32)
randomQ seed = memo f
  where
    (g0, g1) = split (mkTFGen seed)
    f 0 = rand g0   -- include a special case for 0 which is not in the C-W tree
    f r = rand . value $ getGen (numerator r) (denominator r)
      -- otherwise find the generator corresponding to r and use it to
      -- generate a value

    -- We recurse up the tree to find the path from a/b to 1/1; on the
    -- way back down we do appropriate splits (two per step) to find
    -- the generator corresponding to a/b.
    getGen 1 1 = g1
    getGen a b
      | a < b     = left  . subtree $ getGen a (b - a)
      | otherwise = right . subtree $ getGen (a - b) b

instance HasTrie a => HasTrie (Ratio a) where
  newtype (:->:) (Ratio a) b = R ((a,a) :->: b)
  trie f = R (trie _)
  untrie (R t) = untrie t . _
  enumerate t = _

------------------------------------------------------------
-- Notes on randomness API

-- randomGen :: RandomGen g => Active g           -- primitive, infinite
-- random, randomRs  ... etc., duplicate RandomGen interface in Active?
--   These are obviously just higher-level things built on top of randomGen.

-- An Active value can be seen as a tree where some of the leaves are
-- instances of randomGen.  Each such leaf stores a seed value (Int).
-- By default, all are 0.

-- Typically if you duplicate an Active that uses randomness the
-- randomness will be fixed, so the two will be identical.  But if you
-- want to duplicate something but use different randomness, you can
-- wrap it in:

-- randomize :: Active a -> Active a

-- Picks new globally unique seeds for all randomGen primitives
-- contained in it.  But note if any of them already have the same
-- seed they should still share the same (new) seed!

-- What if you want to set your own seed explicitly?  Maybe you want
-- to try different seeds and find one that looks good, and then be
-- sure that you will always and forever have that particular fixed
-- seed.  For example iterating 'randomize' a fixed number of times is
-- no good, because randomize might be called elsewhere, and which
-- seed you get depends on the order in which the calls to randomize
-- are evaluated, which is unpredictable.

-- Maybe something like

-- withSeed :: Int -> Active a -> Active a

-- What should its semantics be??
--
-- Alternatively we could duplicate the entire API and make versions
-- that take a seed as an extra parameter.

-- Note we need a global gensym for automatically chosen seeds
-- (i.e. unsafe IORef etc.) but we also need to make sure that
-- user-chosen seeds are disjoint from generated seeds.  Perhaps for
-- each Int seed value we can generate the TFGen for that seed and
-- then split once, to give the root generators for system-generated
-- or user-chosen seed values.

-- Do we need to worry about what happens when you do parallel
-- composition of things that use randomness?
