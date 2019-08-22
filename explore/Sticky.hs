{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE DeriveFunctor  #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}

import           Data.Char
import           Data.Monoid

-- | Lists can be sticky or dry (non-sticky).  This type is isomorphic
--   to Bool, except that in the case of sticky lists it carries along
--   an appropriate Semigroup instance to carry out the necessary
--   sticking; that is, pattern-matching on the Sticky constructor
--   will bring a Semigroup instance into scope.  It is also indexed
--   by Bool to be able to link it appropriately to actual lists.
data Stickiness :: Bool -> * -> * where
  Sticky :: Semigroup a => Stickiness True a
  Dry    :: Stickiness False a

-- | A (possibly) sticky list carries Stickiness evidence and a list of
--   values.
data StickyList :: Bool -> * -> * where
  SL :: Stickiness s a -> [a] -> StickyList s a

-- | Extract the list content of a StickyList.
getList :: StickyList s a -> [a]
getList (SL _ as) = as

-- | The empty StickyList (identity element for <!>).
emptySticky :: StickyList False a
emptySticky = SL Dry []

-- | We can map over a sticky list, but we need to know whether the
--   result should be sticky (and provide a suitable Semigroup
--   instance for b if it should be).  Note for technical reasons (see
--   the comment at 'mapGlue') it's convenient to simply discard the
--   stickiness of the input list, even though one might expect it to
--   have the same stickiness as the output.
mapStickyList :: Stickiness s b -> (a -> b) -> StickyList t a -> StickyList s b
mapStickyList Dry    f (SL _ as) = SL Dry    (map f as)
mapStickyList Sticky f (SL _ bs) = SL Sticky (map f bs)

-- | Note we can't actually make 'StickyList' a 'Monoid' instance
--   because we want to combine sticky and non-sticky lists, which
--   have different types.  Fortunately we don't actually need a
--   'Monoid' instance, we can just use this operator.
--
--   Notice how in the SL Sticky xs case, pattern-matching on Sticky
--   brings a Semigroup a instance into scope, which is needed to call
--   (++<>).
(<!>) :: StickyList s a -> StickyList t a -> StickyList t a
SL _      [] <!> ys      = ys
SL Dry    xs <!> SL s ys = SL s (xs ++ ys)    -- normal append for dry list + list
SL Sticky xs <!> SL s ys = SL s (xs ++<> ys)  -- sticky append for sticky list + list

-- | Sticky append.  Like normal append, but combines the last element
--   of the first list with the first element of the second.
(++<>) :: Semigroup a => [a] -> [a] -> [a]
[]     ++<> ys     = ys
[x]    ++<> (y:ys) = (x <> y) : ys
(x:xs) ++<> ys     = x : (xs ++<> ys)

-- | The Cayley representation for StickyList, i.e. the usual trick
--   for optimizing nested appends by turning them into function
--   composition which naturally reassociates all the append
--   operations to the right. Note it takes Dry things, not Sticky:
--   the function should be thought of as taking the remainder of a
--   list and appending it to some initial prefix, and the very end of
--   the ultimately produced list will never be sticky.
newtype Glue a = G { unG :: StickyList False a -> StickyList False a }

-- | Create a Glue value directly from a list, given the desired stickiness.
mkGlue :: Stickiness s a -> [a] -> Glue a
mkGlue s = G . (<!>) . SL s

-- | Extract a list from a Glue value.
runGlue :: Glue a -> [a]
runGlue = getList . ($ emptySticky) . unG

-- | To map a function over a Glue value, we again need to know the
--   desired stickiness of the result (along with a Semigroup instance
--   as appropriate).  Notice that Glue itself is not a Functor,
--   because the type parameter occurs both positively and negatively.
--   To implement 'mapGlue', we convert to a normal Sticky list by
--   applying to the empty list, then calling 'mapStickyList', then
--   converting back to a 'Glue' value.  This incurs the linear cost
--   of actually constructing the entire list --- but a call to map
--   would incur a cost proportional to this anyway.
--
--   Notice that the function embedded in the Glue a value will always
--   result in a non-sticky list, regardless of what the ultimate
--   stickiness of the result is supposed to be.  This is why we need
--   mapStickyList to ignore the stickiness of the input list,
--   i.e. not require it to be the same as the output stickiness.
mapGlue :: Stickiness s b -> (a -> b) -> Glue a -> Glue b
mapGlue s f = G . (<!>) . mapStickyList s f . ($ emptySticky) . unG

-- | Glue values form a semigroup under function composition.
instance Semigroup (Glue a) where
  G s1 <> G s2 = G (s1 . s2)

instance Monoid (Glue a) where
  mempty = G id
  mappend = (<>)

{-

Using Glue to compute a left-nested composition is fast:

>>> length . runGlue $ foldl (<>) mempty (map (mkGlue Sticky) (replicate 1000 (map Sum [1..100])))
99001

-}

-- We can use Glue to interpret a nested AST, even one encoded by a
-- GADT with embedded Fmap (and hence existentially quantified type
-- variables) and embedded Semigroup constraints.

data Expr a where
  Prim :: [a] -> Expr a
  Fmap :: (a -> b) -> Expr a -> Expr b
  App  :: Expr a -> Expr a -> Expr a
  Glue :: Semigroup a => Expr a -> Expr a -> Expr a
  -- Instead of separate App and Glue constructors, we could just as
  -- well have a single constructor with an additional (Stickiness s
  -- a) field.

interp :: Expr a -> [a]
interp = runGlue . go Dry
  where
    go :: Stickiness s a -> Expr a -> Glue a
    go s (Prim xs)    = mkGlue s xs
    go s (Fmap f e)   = mapGlue s f (go Dry e)
    go s (App e1 e2)  = go Dry    e1 <> go s e2
    go s (Glue e1 e2) = go Sticky e1 <> go s e2

example :: [Int]
example = map getSum . interp $ e
  where
    e = App (Fmap Sum (Prim [1,2,3]))
          (Glue
            (Glue (Prim [Sum 5, Sum 7])
                  (Fmap (Sum . ord) (Prim "brent")))
            (Fmap Sum (Prim [10, 22, 35])))

-- >>> example
-- [1, 2, 3, 5, 105, 114, 101, 110, 126, 22, 35]

