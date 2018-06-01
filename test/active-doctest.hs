import           Control.Exception (bracket)
import           System.Directory
import           Test.DocTest

main :: IO ()
main = withCurrentDir "src" $ doctest ["Active.hs"]

-- Copy 'withCurrentDirectory' implementation here from the directory
-- package, so it will still work with pre-1.2.3.0 versions of the
-- package
withCurrentDir :: FilePath  -- ^ Directory to execute in
               -> IO a      -- ^ Action to be executed
               -> IO a
withCurrentDir dir action =
  bracket getCurrentDirectory setCurrentDirectory $ \ _ -> do
    setCurrentDirectory dir
    action
