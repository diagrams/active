import           Development.Shake
import           Development.Shake.FilePath

lhs2TeX, pdflatex, bibtex :: String
lhs2TeX  = "lhs2TeX"
pdflatex = "pdflatex"
bibtex   = "bibtex"

main :: IO ()
main = shake shakeOptions $ do

    want ["active-FARM18.pdf"]

    "*.tex" %> \output -> do
        let input = replaceExtension output "lhs"
        need [input]
        cmd lhs2TeX $ ["-o", output] ++ [input]

    "*.bbl" %> \output -> do
      let input = output -<.> "bib"
      need [input]
      cmd bibtex [dropExtension input]

    "*.pdf" %> \output -> do
        let input = replaceExtension output "tex"
        need [input]

        () <- cmd pdflatex $ ["--enable-write18", input]
        cmd pdflatex $ ["--enable-write18", input]
