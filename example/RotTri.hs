{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

import           Data.Active
import           Data.Active.Endpoint
import           Diagrams.Backend.Cairo.CmdLine
import           Diagrams.Prelude

rotationBy :: Turn -> T2
rotationBy = rotation

($>) :: Functor f => f b -> a -> f a
($>) = flip (<$)

t :: Active Free C C Time T2
t = movie
    [ dur 3     $> mempty
    , (0 ..$ 1) (rotationBy . fromTime) *>> 3
    , dur 3     $> mempty
    ]

anim :: Animation Cairo R2
anim = (\tr -> transform tr (triangle 1 # fc white)) <$> t

-- main = defaultMain mempty
main = animMain anim
