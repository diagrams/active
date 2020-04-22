{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeFamilies              #-}

import           Diagrams.Backend.Rasterific.CmdLine
import           Diagrams.Color.HSV
import           Diagrams.Prelude

crtGrid :: Int -> Int -> Diagram B
crtGrid m n = mconcat
  [ vsep 1 (replicate (m+1) (hrule (fromIntegral n) # alignL # translateX (-0.5)))
    # translateY 0.5
  , hsep 1 (replicate (n+1) (vrule (fromIntegral m) # alignT # translateY 0.5))
    # translateX (-0.5)
  ]
  # lineCap LineCapRound

crt :: Int -> Int -> Animation B V2 Double
crt m n = cut (fromIntegral $ lcm m n) $
  stack
  [ pure (crtGrid m n)
  , stackAt
    [ (fromIntegral k, sqA m n k) | k <- [0 .. lcm m n - 1] ]
  , pure (rect (fromIntegral n + 1) (fromIntegral m + 1) # fc white # lw none
          # alignTL # translate ((-1) ^& 1))
  ]

sqA :: Int -> Int -> Int -> Animation B V2 Double
sqA m n k = (cut 4 s) ->> s
  where
    s = pure (sq m n k)

sq :: Int -> Int -> Int -> Diagram B
sq m n k = mconcat
  [ text (show k) # fontSizeL 0.3
  , square 1 # fc (c k) # lw none
  ]
  # moveTo (fromIntegral (k `mod` n) ^& fromIntegral (-(k `mod` m)))

  where
    c k = hsvBlend (fromIntegral k / fromIntegral (lcm m n)) lightblue yellow

-- TODO: animMain should throw an error if given an infinite animation!
main = animMain (crt 3 5)
