#!/bin/sh
mkdir -p trace
ulimit -v 50000000
# for more recent TLC:
#tlc MC -workers auto -noGenerateSpecTEBin "$@" -teSpecOutDir trace -dump dot,colorize,actionlabels model
tlc MC -workers auto "$@" -teSpecOutDir trace -dump dot,colorize,actionlabels model
dot -Grankdir=LR -Tpdf model.dot > model.pdf
skill -HUP llpp
