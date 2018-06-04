import ActiveDiagrams
as :: Diagram Cairo R2
as = cat' unitY with {sep = 0.5} [a12, a2, a1]
dia = (   vrule (height as) # translateX (-1)
       <> vrule (height as) # translateX 3
      )
      # alignB # translateY (-1.5)
      # lw 0.1 # dashing [0.3,0.2] 0
   <> as
   <> tl
