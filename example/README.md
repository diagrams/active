To build the examples:

- Make sure you have the master branch of `active` checked out and up-to-date.
- `stack build diagrams-rasterific`
- `cd example/`
- `stack ghc -- --make Animation.hs && ./Animation -w 300 -h 300 -o Animation.gif`
  (or replace `Animation` with whichever example you want to build)
