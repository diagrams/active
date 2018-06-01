import ActiveDiagrams

b1  = activeD' C C (-6) 3 [red]
b2  = activeD' O C (-1) 5 [blue]
b12 = activeD' O C (-1) 3 [red,blue]

bs :: Diagram Cairo R2
bs = cat' unitY with {sep = 0.5} [b12, b2, b1]

b1'  = activeD' C C (-6) 3 [red]
b2'  = activeD' O C (-8) 5 [blue]
b12' = activeD' C C (-6) 3 [red,blue]

bs' = cat' unitY with {sep = 0.5} [b12', b2', b1']

dia = hcat [ bs <> tl , strutX 3, bs' <> tl ]
