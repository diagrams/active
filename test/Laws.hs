module Laws where

-- getDuration laws
getDuration (activeF d x) = d
getDuration (activeI x)   = Forever
getDuration (active d x)  = d
getDuration (instant x)  = 0
getDuration (lasting d x)  = d
getDuration (always x)  = Forever
getDuration (ui)  = 1
getDuration (interval c d)  = abs (d - c)
getDuration (dur)  = Forever
getDuration (discreteNE xs) = 1
getDuration (discrete xs) = 1

getDuration (cut d x)      = min d (getDuration x)
getDuration (omit d x)     = getDuration x - d      {d <= getDuration x}
getDuration (omit d x) + d = getDuration x

-- if we have Monoid a => Active a, we could define:
--   getDuration (omit d x)  = max 0 (getDuration x - d)
--   i.e. omit d x returns instant mempty when d > getDuration x

--   Should there be a total version of omit for Monoid provided?
--   Maybe non-total, non-Monoid version is 'unsafe' version?

getDuration (backwards x) = getDuration x      {x is finite?}
getDuration (always x)    = Forever

getDuration (stretch k x) = |k| * getDuration x  {k /= 0}

getDuration (x ->- y) = getDuration x + getDuration y

cutTo x y = cut (getDuration x) y

cut d x ->- omit d x = x
  if d <= getDuration x

omit (c + d) x = (omit c . omit d) x   {c + d <= getDuration x}

cut c . cut d = cut (min c d)

cut (c + d) x = cut c x ->- cut d (omit c x)    {c <= getDuration x}

slice a b x
  | a <= b    = cut (b - a) (omit a x)
  | otherwise = backwards (slice b a x)

backwards (backwards x) = x    {x is finite}
stretch (-1) x = backwards x

stretch (j*k) = stretch j . stretch k   {j, k /= 0}

snapshot t x = always (runActive t x)
