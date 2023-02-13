#!/bin/sh
mkdir -p trace
ulimit -v 50000000
# for more recent TLC:
#tlc MC -workers auto -noGenerateSpecTEBin "$@" -teSpecOutDir trace -dump dot,colorize,actionlabels model
tlc MC -workers auto "$@" -teSpecOutDir trace -dump dot,colorize,actionlabels model
# only dot models smaller than x bytes
if du -b model.dot | awk '$1 > 1000000 { exit(1) }'; then
    dot -Grankdir=LR -Tpdf model.dot > model.pdf
    skill -HUP llpp
else
    echo "Skipped processing large dot file"
fi
