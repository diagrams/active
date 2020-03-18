To build the examples:

- Make sure you have the master branch of `active` checked out and up-to-date.
- `cd example/`
- `stack ghc --package diagrams-lib --package diagrams-rasterific --package diagrams-contrib -- --make Animation.hs && ./Animation -w 300 -h 300 -o Animation.gif`
  (or replace `Animation` with whichever example you want to build)
