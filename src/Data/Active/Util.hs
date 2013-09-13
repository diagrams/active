-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Active.Util
-- Copyright   :  (c) 2013 Andy Gill, Brent Yorgey
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  byorgey@cis.upenn.edu
--
-- Some utility operators that are useful for constructing Active
-- values.
-----------------------------------------------------------------------------

module Data.Active.Util
    ( (<#>), ($>), (<*~>)
    )
    where

import Data.Functor ((<$))

infixl 8 <#>

-- | Backwards 'fmap'. Useful for mapping a poxtfix transformation
--   over a 'Functor' such as @Active@. For example,
--
--   > durValued (dur 5) <#> circle <#> (`atop` square 2)
--
--   Mnemonic: '$' is to '<$>' as '#' is to '<#>'.
(<#>) :: Functor f => f a -> (a -> b) -> f b
(<#>) = flip fmap

infixr 4 $>

-- | Backwards '<$', /i.e./ replace a value inside a functor from
--   the right.  Useful for setting a constant value for the duration
--   of an @Active@, /e.g./
--
--   > dur 4 $> hexagon 1
--
--   creates a constant hexagon with duration 4.
($>) :: Functor f => f b -> a -> f a
($>) = flip (<$)

infixl 4 <*~>

-- | Like '<*>' but where the second argument has been \"demoted\" to
--   a pure value instead of an @f@-context.  The point is that this
--   only requires 'Functor', not 'Applicative', so it can be used to
--   work with @Active Free@ values using an \"@Applicative@-like\"
--   syntax.  For example,
--
--   > translateX <$> durValued (dur 4) <*~> square 1
--
--   is a square which moves along the X-axis for four time units.
(<*~>) :: Functor f => f (a -> b) -> a -> f b
f <*~> a = fmap ($a) f

