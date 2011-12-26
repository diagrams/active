module Main where

import Control.Applicative
import Control.Monad   (when)
import Data.Semigroup

import System.Exit     (exitFailure)

import Test.QuickCheck
import Text.Printf     (printf)

import Data.Active
import Data.AffineSpace

main :: IO ()
main = do
    results <- mapM (\(s,t) -> printf "%-40s" s >> t) tests
    when (not . all isSuccess $ results) $ exitFailure
  where
    isSuccess (Success{}) = True
    isSuccess _ = False
    qc x = quickCheckWithResult (stdArgs { maxSuccess = 200 }) x
    tests = [ ("era/start",                   qc prop_era_start    )
            , ("era/end",                     qc prop_era_end      )
            , ("duration",                    qc prop_duration     )
            , ("shiftDyn/start",              qc prop_shiftDynamic_start )
            , ("shiftDyn/end",                qc prop_shiftDynamic_end )
            , ("shiftDyn/fun",                qc prop_shiftDynamic_fun )
            , ("active/semi-hom",             qc prop_active_semi_hom )
            ]

instance Arbitrary Any where
  arbitrary = Any <$> arbitrary

instance Arbitrary Time where
  arbitrary = fromRational <$> arbitrary

instance CoArbitrary Time where
  coarbitrary t = coarbitrary (toRational t)

instance Arbitrary Duration where
  arbitrary = fromRational <$> arbitrary

instance Arbitrary a => Arbitrary (Dynamic a) where
  arbitrary = mkDynamic <$> arbitrary <*> arbitrary <*> arbitrary

instance Arbitrary a => Arbitrary (Active a) where
  arbitrary = oneof [ pure <$> arbitrary
                    , fromDynamic <$> arbitrary
                    ]

prop_era_start :: Time -> Time -> Bool
prop_era_start t1 t2 = start (mkEra t1 t2) == t1

prop_era_end :: Time -> Time -> Bool
prop_era_end t1 t2 = end (mkEra t1 t2) == t2

prop_duration :: Time -> Time -> Bool
prop_duration t1 t2 = duration (mkEra t1 t2) == (t2 .-. t1)

prop_shiftDynamic_start :: Duration -> Blind (Dynamic Bool) -> Bool
prop_shiftDynamic_start dur (Blind dyn)
  = (start . era) (shiftDynamic dur dyn) == ((start . era) dyn .+^ dur)

prop_shiftDynamic_end :: Duration -> Blind (Dynamic Bool) -> Bool
prop_shiftDynamic_end dur (Blind dyn)
  = (end . era) (shiftDynamic dur dyn) == ((end . era) dyn .+^ dur)

prop_shiftDynamic_fun :: Duration -> Blind (Dynamic Bool) -> Time -> Bool
prop_shiftDynamic_fun dur (Blind dyn) t
  = runDynamic dyn t == runDynamic (shiftDynamic dur dyn) (t .+^ dur)

prop_active_semi_hom :: Blind (Active Any) -> Blind (Active Any) -> Time -> Bool
prop_active_semi_hom (Blind a1) (Blind a2) t =
  runActive a1 t <> runActive a2 t == runActive (a1 <> a2) t
