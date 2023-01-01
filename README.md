This tool is licensed under the [MIT license](LICENSE.MIT).

Copyright: Erkki Seppälä <erkki.seppala@vincit.fi> 2022-2023

You can contact me also [via
Matrix](https://matrix.to/#/@flux:matrix.org).

[![Build](https://github.com/eras/mxrxtx/actions/workflows/build.yaml/badge.svg)](https://github.com/eras/mxrxtx/actions/workflows/build.yaml)

# `mxrxtx`—Matrix Receive and Transmit

`mxrxtx` is a tool for transferring files with
[WebRTC](https://webrtc.org) using [Matrix](https://matrix.org) as the
signaling medium. It's like
[DCC](https://en.wikipedia.org/wiki/Direct_Client-to-Client) for
Matrix.

Compared to using the normal file upload/download functionality this
approach doesn't have file size limitations (as configured by the
homeserver admin) and naturally it doesn't consume almost any server
resources nor will the data remain around in the homeserver once it
has been removed.

On the other hand, to transfer the files the source must remain
connected to the Internet for the complete duration of the transfer
and each peer will download the file again from the original provider.

The intent of this tool is to work as a prototype for eventually
specifying _solid_ WebRTC file transfer functionality for the Matrix
spec.

__Note: `mxrxtx` does not yet support encryption.__

# Usage
## `mxrxtx --setup`
Run the initial setup. You may provide an alternative config file with
`--config`; otherwise config file location relevant to your system is
used.
## `mxrxtx --offer '#room' hello.txt hello.png`
Offers a file to a room `mxrxtx` is a member of and matches uniquely to
the given name. You may also use room ids. The command outputs the
matrix.to url for the shared files, which is shared as a single
collection.

The offer is withdrawn when `mxrxtx` exits.
## `mxrxtx --download 'matrix:roomid/rCWNvpCTZHQkiRYUDE:matrix.org/$uPjb5qzQ0FmyQX5j0tXjCjdwKp_es00vNn_tePPzYpA'`
Accepts also: `https://matrix.to/#/!rCWNvpCTZHQkiRYUDE:matrix.org/$uPjb5qzQ0FmyQX5j0tXjCjdwKp_es00vNn_tePPzYpA?via=hacklab.fi&via=matrix.org&via=kapsi.fi`

Starts download of a particular file being offered. As the file names
are defined by the original event, it may be advisable to use the
`--output-dir` switch to create a new directory.

