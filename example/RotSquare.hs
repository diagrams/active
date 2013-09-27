{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

import           Diagrams.Backend.Cairo.CmdLine
import           Diagrams.Prelude

type Anim a = Active Free C C Time a
type Dia    = Diagram Cairo R2

rot :: Anim T2
rot = (rotation . Turn) <$> durValued (dur 1)

rotSquare :: Anim Dia
rotSquare = transform <$> rot <*~> square 1

canvas :: Dia
canvas = square 3 # fc white

main = animMain (atop <$> rotSquare *>> 5 <*~> canvas)
