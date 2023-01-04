#!/bin/sh
version="$1"
if [ -z "$version" ]; then
   version="$(git describe --tags | sed 's/^.//')"
fi
sed -i 's/^\(version =\).*/\1 "'"$version"'"/' Cargo.toml
