module Main where

import Build_doctests (flags, pkgs, module_sources)
import Data.Foldable (traverse_)
import System.Environment (unsetEnv)
import Test.DocTest (doctest)

main :: IO ()
main = do
    traverse_ putStrLn args
    -- This variable is set automatically by Stack, and read by GHC when
    -- executed by doctest; we don't want that.
    unsetEnv "GHC_ENVIRONMENT"
    doctest args
  where
    args = flags ++ pkgs ++ module_sources
