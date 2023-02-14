# Basic protocol specification

This will not be an interesting protocol :), but it will work for the basis spec for the more
interesting version, hopefully.

List of modules:
- [Protocol.tla](Protocol.tla): Describes the basic data message flow from protocol persepective
- [HS.tla](HS.tla): HS specification; a general abstract homeserver specification
- [Device.tla](Device.tla): Device specification, including Monitor and Offer submodules

Note: before running the [`check.sh`](../check.sh), you may want to comment out `-dump
dot,colorize,actionlabels model` if you have two monitors. Otherwise the resulting dot files will be
unwieldly large and in particular the liveness dot file can become quite large (e.g. 35 gigabytes)
and slow down the process.
