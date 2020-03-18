#!/bin/sh

stack build diagrams diagrams-pgf diagrams-builder palette shake &&\
  stack runghc --package shake --package diagrams-builder Shake.hs
