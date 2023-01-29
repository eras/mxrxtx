---- MODULE DataChannel --------------------------------------------------------
EXTENDS Constants
(* Documentation *)
--------------------------------------------------------------------------------
LOCAL INSTANCE Common

CONSTANT Data

VARIABLES datachannel

A(from, to, label) ==
   INSTANCE MChannel WITH
      Id       <- <<from, to, label>>
    , Data     <- Data
    , channels <- datachannel

B(from, to, label) ==
   INSTANCE MChannel WITH
      Id       <- <<to, from, label>>
    , Data     <- Data
    , channels <- datachannel

TypeOK(data_channel_id) ==
   LET from  == data_channel_id[1] IN
   LET to    == data_channel_id[2] IN
   LET label == data_channel_id[3] IN
   /\ A(from, to, label)!TypeOK
   /\ B(from, to, label)!TypeOK

Init ==
   /\ datachannel = [<<from, to, label>> \in DataChannelId |-> <<>>]
================================================================================
