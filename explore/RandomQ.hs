import           Data.Ratio
import           Data.Word
import           System.Random.TF.Gen
import           System.Random.TF.Init

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
randomQ seed = f
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
