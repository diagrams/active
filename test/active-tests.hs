{-# LANGUAGE CPP              #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Main where

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative
#endif

import           Control.Monad       (unless)
import           Data.Semigroup

import           System.Exit         (exitFailure)

import           Test.QuickCheck
import           Text.Printf         (printf)

import           Data.Active

import           Linear.Affine
import           Linear.Vector

main :: IO ()
main = do
  results <- mapM (\(s,t) -> printf "%-40s" s >> t) tests
  unless (all isSuccess results) exitFailure
  where
    isSuccess (Success{}) = True
    isSuccess _           = False
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
{-# ANN main ("HLint: ignore Eta reduce" :: String) #-}
-- eta reducing qc breaks it

instance Arbitrary Any where
  arbitrary = Any <$> arbitrary

instance (Arbitrary n, Fractional n, Real n) => Arbitrary (Time n) where
  arbitrary = fromRational <$> arbitrary

instance (CoArbitrary n, Real n) => CoArbitrary (Time n) where
  coarbitrary t = coarbitrary (toRational t)

instance (Arbitrary n, Fractional n, Real n) => Arbitrary (Duration n) where
  arbitrary = (fromRational . abs) <$> arbitrary

instance Arbitrary a => Arbitrary (Dynamic a) where
  arbitrary = do
    s <- arbitrary
    d <- arbitrary
    mkDynamic <$> pure s <*> pure (s .+^ d) <*> arbitrary

instance Show (Dynamic a) where
  show (Dynamic e _) = "<" ++ show e ++ ">"

instance Arbitrary a => Arbitrary (Active a) where
  arbitrary = oneof [ pure <$> arbitrary
                    , fromDynamic <$> arbitrary
                    ]

instance Show a => Show (Active a) where
  show = onActive (\c -> "<<" ++ show c ++ ">>")
                  show

prop_era_start :: Time Rational -> Time Rational -> Bool
prop_era_start t1 t2 = start (mkEra t1 t2) == t1

prop_era_end :: Time Rational -> Time Rational -> Bool
prop_era_end t1 t2 = end (mkEra t1 t2) == t2

prop_duration :: Time Rational -> Time Rational -> Bool
prop_duration t1 t2 = duration (mkEra t1 t2) == (t2 .-. t1)

prop_shiftDynamic_start :: Duration Rational -> Dynamic Bool -> Bool
prop_shiftDynamic_start dur dyn
  = (start . era) (shiftDynamic dur dyn) == ((start . era) dyn .+^ dur)

prop_shiftDynamic_end :: Duration Rational -> Dynamic Bool -> Bool
prop_shiftDynamic_end dur dyn
  = (end . era) (shiftDynamic dur dyn) == ((end . era) dyn .+^ dur)

prop_shiftDynamic_fun :: Duration Rational -> Dynamic Bool -> Time Rational -> Bool
prop_shiftDynamic_fun dur dyn t
  = runDynamic dyn t == runDynamic (shiftDynamic dur dyn) (t .+^ dur)

prop_active_semi_hom :: Active Any -> Active Any -> Time Rational -> Bool
prop_active_semi_hom a1 a2 t =
  runActive a1 t <> runActive a2 t == runActive (a1 <> a2) t

prop_ui_id :: Time Rational -> Bool
prop_ui_id t = runActive (ui :: Active (Time Rational)) t == t

prop_stretch_start :: Rational -> Active Bool -> Bool
prop_stretch_start r a
  = (start <$> activeEra a) == (start <$> activeEra (stretch r a))

prop_stretch_dur :: Rational -> Active Bool -> Bool
prop_stretch_dur r a
  = (((r *^) . duration) <$> activeEra a) == (duration <$> activeEra (stretch r a))

{-
prop_stretch_fun :: Rational -> Blind (Active Bool) -> Time -> Bool
prop_stretch_fun r (Blind a) t
  = runActive a t    runActive (stretch r t)
-}

prop_stretchTo_dur :: Positive (Duration Rational) -> Active Bool -> Property
prop_stretchTo_dur (Positive dur) a
  = isDynamic a && ((duration <$> activeEra a) /= Just 0)
    ==> (duration <$> activeEra (stretchTo dur a)) == Just dur

prop_during_const :: Active Bool -> Active Bool -> Property
prop_during_const a1 a2 =
  (isConstant a1 || isConstant a2) ==> (start <$> activeEra (a1 `during` a2)) == (start <$> activeEra a1)

prop_during_start :: Dynamic Bool -> Dynamic Bool -> Bool
prop_during_start d1 d2 =
  (start <$> activeEra (a1 `during` a2)) == (start <$> activeEra a2)
 where a1 = fromDynamic d1
       a2 = fromDynamic d2

prop_during_end :: Dynamic Bool -> Dynamic Bool -> Bool
prop_during_end d1 d2 =
  (end <$> activeEra (a1 `during` a2)) == (end <$> activeEra a2)
 where a1 = fromDynamic d1
       a2 = fromDynamic d2

prop_shift_start :: Duration Rational -> Active Bool -> Bool
prop_shift_start d a =
  ((.+^ d) . start <$> activeEra a) == (start <$> activeEra (shift d a))

prop_shift_end :: Duration Rational -> Active Bool -> Bool
prop_shift_end d a =
  ((.+^ d) . end <$> activeEra a) == (end <$> activeEra (shift d a))

prop_atTime_start :: Time Rational -> Dynamic Bool -> Bool
prop_atTime_start t dyn =
    (start <$> activeEra (atTime t a)) == Just t
  where a = fromDynamic dyn

prop_atTime_fun :: Time Rational -> Dynamic Bool -> Duration Rational -> Bool
prop_atTime_fun t dyn d =
    runActive (atTime t a) (t .+^ d) == runActive a (s .+^ d)
  where a = fromDynamic dyn
        s = start (era dyn)
