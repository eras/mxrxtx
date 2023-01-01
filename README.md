# Usage
## `mxrxtx --setup`
Run the initial setup. You may provide an alternative config file with
`--config`; otherwise config file location relevant to your system is
used.
## `mxrxtx --offer '#room' hello.txt hello.png`
Offers a file to a room mxrxtx is a member of and matches uniquely to
the given name. You may also use room ids. The command outputs the
matrix.to url for the shared files, which is shared as a single
collection.

The offer is withdrawn when mxrxtx exits.
## `mxrxtx --download 'matrix:roomid/rCWNvpCTZHQkiRYUDE:matrix.org/$uPjb5qzQ0FmyQX5j0tXjCjdwKp_es00vNn_tePPzYpA'`
Accepts also: `https://matrix.to/#/!rCWNvpCTZHQkiRYUDE:matrix.org/$uPjb5qzQ0FmyQX5j0tXjCjdwKp_es00vNn_tePPzYpA?via=hacklab.fi&via=matrix.org&via=kapsi.fi`

Starts download of a particular file being offered. As the file names
are defined by the original event, it may be advisable to use the
`--output-dir` switch to create a new directory.

