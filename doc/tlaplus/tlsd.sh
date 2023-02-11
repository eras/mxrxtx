#!/bin/zsh
trap 'rm "$tmpcfg"' EXIT
tmpcfg="$(mktemp --suffix=.cfg)"
model="$1"
if [ -z "$model" ]; then
    model=MC
fi
orig_config="$(basename "$model" .tla).cfg"
(pcregrep -Mv '^ *ALIAS[ \n]*[a-zA-Z_[0-9]]*' $orig_config; echo; echo ALIAS AliasMessages) > "$tmpcfg"
tlc "$model" -workers auto -teSpecOutDir trace -deadlock -config "$tmpcfg" |
    tee tlsd.output |
    tlsd &&
    inkscape --export-type=pdf -o sequence.pdf sequence.svg
