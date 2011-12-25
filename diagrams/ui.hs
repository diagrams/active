{-# LANGUAGE NoMonomorphismRestriction #-}

import Diagrams.Prelude
import Diagrams.Backend.Cairo.CmdLine

d fun = (square 4 <> ends <> fun # lc red) # lw 0.03 # lineCap LineCapRound # lineJoin LineJoinRound
  where ends = vert <> vert # translateX 1 
               <> rect 1 4 # translateX (0.5) # opacity 0.2 # fc grey
        vert = vrule 4 # lw 0.02 # dashing [0.1,0.1] 0 # lc grey

uiFun = (P (-2,-2) ~~ P (2,2))

backwardsFun = (P (2,-1) ~~ P (-1,2))

clampFun = fromOffsets [(2,0), (1,1), (1,0)] # centerX

trimFun = origin ~~ P (1,1)

ds = map (pad 1.1 . d) [uiFun, clampFun, trimFun, backwardsFun]

main = multiMain (zip ["ui", "clamp", "trim", "backwards"] ds)