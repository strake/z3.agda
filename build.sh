#!/bin/sh
exec agda --ghc --ghc-flag=-XLambdaCase --ghc-flag=-package=z3 --no-main Z3/Base.agda
