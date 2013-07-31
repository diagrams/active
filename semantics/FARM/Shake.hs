import           Development.Shake
import           Development.Shake.FilePath

lhs2TeX  = "lhs2TeX"
pdflatex = "pdflatex"
bibtex   = "bibtex"

main :: IO ()
main = shake shakeOptions $ do
  want ["abstract.pdf"]

  "*.tex" *> \output -> do
      let input = replaceExtension output "lhs"
      need [input]
      system' lhs2TeX $ ["-o", output] ++ [input]

  "*.pdf" *> \output -> do
      let input = replaceExtension output "tex"
      need [input]
      system' pdflatex $ ["--enable-write18", input]

      need [replaceExtension input "bib"]
      system' bibtex $ [dropExtension input]
      system' pdflatex $ ["--enable-write18", input]
