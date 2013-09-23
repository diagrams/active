import           ActiveDiagrams
import           Diagrams.Backend.Cairo.CmdLine
import           Diagrams.Prelude

main = defaultMain (timeline (-10) 10 <> wiggle (-3) 6)
