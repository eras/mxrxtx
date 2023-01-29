#!/bin/sh
mkdir -p trace
ulimit -v 50000000
tlc MC -difftrace -noGenerateSpecTEBin "$@" -teSpecOutDir trace -dump dot,colorize,actionlabels model
#tlc MC -noGenerateSpecTEBin "$@" -teSpecOutDir trace
dot -Grankdir=LR -Tpdf model.dot > model.pdf
skill -HUP llpp
