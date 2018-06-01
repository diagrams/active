#!/bin/sh

stack build diagrams diagrams-pgf diagrams-builder palette shake
stack runghc Shake.hs
