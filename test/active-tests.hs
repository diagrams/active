{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Main where

import           Control.Applicative
import           Control.Monad       (when)
import           Data.Semigroup

import           System.Exit         (exitFailure)

import           Test.QuickCheck
import           Text.Printf         (printf)

import           Data.Active
import           Data.AffineSpace
import           Data.VectorSpace

main :: IO ()
main = do
    results <- mapM (\(s,t) -> printf "%-40s" s >> t) tests
    when (not . all isSuccess $ results) $ exitFailure
  where
    isSuccess (Success{}) = True
    isSuccess _ = False
    qc x = quickCheckWithResult (stdArgs { maxSuccess = 200 }) x
    tests = [ ("era/start",                   qc prop_era_start          )
            , ("era/end",                     qc prop_era_end            )
            , ("duration",                    qc prop_duration           )
            , ("shiftDyn/start",              qc prop_shiftDynamic_start )
            , ("shiftDyn/end",                qc prop_shiftDynamic_end   )
            , ("shiftDyn/fun",                qc prop_shiftDynamic_fun   )
            , ("active/semi-hom",             qc prop_active_semi_hom    )
            , ("ui/id",                       qc prop_ui_id              )
            , ("stretch/start",               qc prop_stretch_start      )
            , ("stretch/dur",                 qc prop_stretch_dur        )
            , ("stretchTo/dur",               qc prop_stretchTo_dur      )
            , ("during/const",                qc prop_during_const       )
            , ("during/start",                qc prop_during_start       )
            , ("during/end",                  qc prop_during_end         )
            , ("shift/start",                 qc prop_shift_start        )
            , ("shift/end",                   qc prop_shift_end          )
--            , ("backwards",                   qc prop_backwards          )
            , ("atTime/start",                qc prop_atTime_start       )
            , ("atTime/fun",                  qc prop_atTime_fun         )
            ]

instance Arbitrary Any where
  arbitrary = Any <$> arbitrary

instance Arbitrary Time where
  arbitrary = fromRational <$> arbitrary

instance CoArbitrary Time where
  coarbitrary t = coarbitrary (toRational t)

instance Arbitrary Duration where
  arbitrary = (fromRational . abs) <$> arbitrary

instance (Clock t, Arbitrary (Diff t), CoArbitrary t, Arbitrary t, Arbitrary a) => Arbitrary (Dynamic t a) where
  arbitrary = do
    s <- arbitrary
    d <- arbitrary
    mkDynamic <$> pure s <*> pure (s .+^ d) <*> arbitrary

instance Show t => Show (Dynamic t a) where
  show (Dynamic e _) = "<" ++ show e ++ ">"

instance (Clock t, Arbitrary (Diff t), CoArbitrary t, Arbitrary t, Arbitrary a) => Arbitrary (Active t a) where
  arbitrary = oneof [ pure <$> arbitrary
                    , fromDynamic <$> arbitrary
                    ]

instance (Show t, Show a) => Show (Active t a) where
  show = onActive (\c -> "<<" ++ show c ++ ">>")
                  (\d -> show d)

prop_era_start :: Time -> Time -> Bool
prop_era_start t1 t2 = start (mkEra t1 t2) == t1

prop_era_end :: Time -> Time -> Bool
prop_era_end t1 t2 = end (mkEra t1 t2) == t2

prop_duration :: Time -> Time -> Bool
prop_duration t1 t2 = duration (mkEra t1 t2) == (t2 .-. t1)

prop_shiftDynamic_start :: Duration -> Dynamic Time Bool -> Bool
prop_shiftDynamic_start dur dyn
  = (start . era) (shiftDynamic dur dyn) == ((start . era) dyn .+^ dur)

prop_shiftDynamic_end :: Duration -> Dynamic Time Bool -> Bool
prop_shiftDynamic_end dur dyn
  = (end . era) (shiftDynamic dur dyn) == ((end . era) dyn .+^ dur)

prop_shiftDynamic_fun :: Duration -> Dynamic Time Bool -> Time -> Bool
prop_shiftDynamic_fun dur dyn t
  = runDynamic dyn t == runDynamic (shiftDynamic dur dyn) (t .+^ dur)

prop_active_semi_hom :: Active Time Any -> Active Time Any -> Time -> Bool
prop_active_semi_hom a1 a2 t =
  runActive a1 t <> runActive a2 t == runActive (a1 <> a2) t

prop_ui_id :: Time -> Bool
prop_ui_id t = runActive (ui :: Active Time Time) t == t

prop_stretch_start :: Rational -> Active Time Bool -> Bool
prop_stretch_start r a
  = (start <$> activeEra a) == (start <$> activeEra (stretch r a))

prop_stretch_dur :: Rational -> Active Time Bool -> Bool
prop_stretch_dur r a
  = (((r *^) . duration) <$> activeEra a) == (duration <$> activeEra (stretch r a))

{-
prop_stretch_fun :: Rational -> Blind (Active Bool) -> Time -> Bool
prop_stretch_fun r (Blind a) t
  = runActive a t    runActive (stretch r t)
-}

prop_stretchTo_dur :: Positive Duration -> Active Time Bool -> Property
prop_stretchTo_dur (Positive dur) a
  = isDynamic a && ((duration <$> activeEra a) /= Just 0)
    ==> (duration <$> activeEra (stretchTo dur a)) == Just dur

prop_during_const :: Active Time Bool -> Active Time Bool -> Property
prop_during_const a1 a2 =
  (isConstant a1 || isConstant a2) ==> (start <$> activeEra (a1 `during` a2)) == (start <$> activeEra a1)

prop_during_start :: Dynamic Time Bool -> Dynamic Time Bool -> Bool
prop_during_start d1 d2 =
  (start <$> activeEra (a1 `during` a2)) == (start <$> activeEra a2)
 where a1 = fromDynamic d1
       a2 = fromDynamic d2

prop_during_end :: Dynamic Time Bool -> Dynamic Time Bool -> Bool
prop_during_end d1 d2 =
  (end <$> activeEra (a1 `during` a2)) == (end <$> activeEra a2)
 where a1 = fromDynamic d1
       a2 = fromDynamic d2

prop_shift_start :: Duration -> Active Time Bool -> Bool
prop_shift_start d a =
  ((.+^ d) . start <$> activeEra a) == (start <$> activeEra (shift d a))

prop_shift_end :: Duration -> Active Time Bool -> Bool
prop_shift_end d a =
  ((.+^ d) . end <$> activeEra a) == (end <$> activeEra (shift d a))

prop_atTime_start :: Time -> Dynamic Time Bool -> Bool
prop_atTime_start t dyn =
    (start <$> activeEra (atTime t a)) == Just t
  where a = fromDynamic dyn

prop_atTime_fun :: Time -> Dynamic Time Bool -> Duration -> Bool
prop_atTime_fun t dyn d =
    runActive (atTime t a) (t .+^ d) == runActive a (s .+^ d)
  where a = fromDynamic dyn
        s = start (era dyn)
