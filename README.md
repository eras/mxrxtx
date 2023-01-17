This tool is licensed under the [MIT license](LICENSE.MIT).

Copyright: Erkki Seppälä <erkki.seppala@vincit.fi> 2022-2023

You can contact me also [via
Matrix](https://matrix.to/#/@flux:matrix.org) or at
[#mxrxtx:matrix.org](https://matrix.to/#/#mxrxtx:matrix.org).

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
has been removed (but metadata might).

On the other hand, to transfer the files the source must remain
connected to the Internet for the complete duration of the transfer
and each peer will download the file again from the original provider.

The intent of this tool is to work as a prototype for eventually
specifying _solid_ WebRTC file transfer functionality for the Matrix
spec.

`mxrxtx` supports end-to-end encryption, __however the WebRTC
handshake is vulnerable to a Man-in-the-Middle attack__, at least
[until Matrix Rust SDK is able to send encrypted ToDevice
messages](https://github.com/matrix-org/matrix-rust-sdk/issues/814),
the offer is modified to provide some sort of signing data, or we make
use of some other encryption material available to the Client object
to establish peer identity over the WebRTC connection. The metadata
and the data are safe (but not confidential) because the file data and
their SHA512 is shared in the original message encrypted, __but only
if__ the message was shared in an encrypted room.

You may do the emoji verification at the end of the `setup`, or
separately with the `verify` sub-command. (Verification is not
possible in other modes of operation.) __Note that `mxrxtx` will
automatically accept whichever emojis it gets to show__: if you notice
any discrepancy here while doing the verification, you should remove
the state store and maybe weed out those hackers from the homeserver..

## Features

- Available for Linux and Windows
- Setup mode easy configuration; supports single signon
- Offer can contain multiple files and directories
- Supports E2EE and emoji cross-signing verification
- Monitor mode for downloading all received offers
- The offered content can be downloaded many times, and concurrently by multiple clients
- Supports a room to send log data to (relevant in particular to monitor mode)
- Redacts offers when offering client terminates

## Known issues

- Offers consisting of only zero-byte files probably won't work..
- Mac build, if enabled on CI, would crash during the unit tests
- Protocol is not final at all
- Does not use [MSC1767 extensible events](https://github.com/matrix-org/matrix-spec-proposals/pull/1767) yet
- My todo list for `mxrxtx` has 100+ entries

# Usage
## Install

Binaries for Ubuntu Windows are available in the [GitHub releases
page](../../releases/latest/). Download a binary, extract it and run
it from a terminal.

You may also use Cargo to install it from the sources:

`cargo install --git https://github.com/eras/mxrxtx`

If you don't have Rust and Cargo set up, you can use
[rustup](https://rustup.rs/) to set it with ease.

## Setting up
Run the initial setup with `mxrxtx setup`. You may provide an alternative config file with
`--config`; otherwise config file location relevant to your system is
used.

The idea is to use this tool with the credentials of the account you
use instead of creating new bot credentials for it. It does not
have the ability to e.g. join rooms.
## Offer a file
Offer a file with `mxrxtx offer '#roomalias:example.com' hello.txt
hello.png`. You may also use the room name (case insensitive) or the room
id and the client needs to be present in that room. The command
outputs the matrix.to URL for the shared files, which is shared as a
single collection.

Because few clients are able to show the events, you may choose to
copy paste that URL to a room. Most notably to see these events in
[Element](https://element.io/), you need to have "Show hidden events
in timeline" enabled from the developer settings, which you can access
via the `/devtools` commands—and even then you need to click the event
open to see its contents (situation does not seem better even with
[MSC1767 extensible
events](https://github.com/matrix-org/matrix-spec-proposals/pull/1767)
support enabled even if `mxrxtx` did support them).

The offer is redacted when `mxrxtx` exits.
## Download a file
You can download a file with `mxrxtx download 'matrix:roomid/rCWNvpCTZHQkiRYUDE:matrix.org/$uPjb5qzQ0FmyQX5j0tXjCjdwKp_es00vNn_tePPzYpA'`. Accepts also matrix.to-URLs.

Starts download of a particular file being offered. As the file names
are defined by the original event, it may be advisable to use the
`--output-dir` switch before the `download` sub-command to create a new
directory.
## Keep downloading any offers
To download any offered files, you can use `mxrxtx
monitor`. (`--output-dir` is advisable here as well.) It will only
consider new events synced after starting the tool.

# FAQ
## How to spell the name?
It should be spelled as follows: _äm äks är äks tee äks_.
## How does it work?

Theory operation is as follows:

- Client A sends a custom message to a room describing which files it wants to offer and some metadata about them
- Client B is informed about the URI for this event and retrieves the contents of the event
- Client B sends a custom ToDevice message to A to start the WebRTC handshake (ice servers may be consulted)
- Client A responds to client B to continue the WebRTC handshake
- Clients A and B have now formed a WebRTC datachannel connection
- Client A starts sending the contents of the offer from start to end (no framing so far)
- Client B received the contents and writes them to a file
- Once Client B has received the final byte it sends "ok" to A and terminates
- Client A reads two bytes from B and the session A-B is finished; other concurrent or future sessions may continue
- Client A is finally explicitly terminated
