{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeFamilies              #-}

import           Diagrams.Backend.Rasterific.CmdLine
import           Diagrams.Prelude

-- ffmpeg -i frame%03d.png -vcodec mpeg4 out.mov

colors :: Active (Colour Double)
colors = discrete [yellow, blue, red, green, purple] # stretch 3

anim :: Animation B V2 Double
anim = atop
  <$> ( fc
          <$> colors
          <*> (circle <$> (3 + cut 3 sin'))
      )
  <*> pure (square 10 # fc white)

  -- interval' 2 5 :: Active Double
  -- circle :: Double -> Diagram

  -- atop :: Diagram -> Diagram -> Diagram
  -- square :: Double -> Diagram
    -- square 10 # fc white :: Diagram

anim2 :: Animation B V2 Double
anim2 = atop
  <$> (rotateBy <$> cut 3 sin' <*> pure (triangle 3))
  <*> pure (square 10 # fc white)

main = animMain (anim ->> anim2)

