import           System.Directory
import           Test.DocTest

main :: IO ()
main = withCurrentDirectory "src" $ doctest ["Active.hs"]
