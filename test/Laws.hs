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

getDuration (cut )
, cutTo, omit, slice


