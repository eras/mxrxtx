------------------------------ MODULE MChannel ------------------------------

(* MChannel is an asynchronous channel between with a buffer of at most
   one message.

   The state is stored in the channels function. Channels maps via Id to the
   actual channels.

   Copyright 2022 Erkki Seppälä <erkki.seppala@vincit.fi>
*)

----------------------------------------------------------------------------
LOCAL INSTANCE TLC              (* Assert *)

CONSTANT Id                     (* Id is used to find this instance from channels *)
CONSTANT Data                   (* Data constrains the kind of messages this module processes*)

VARIABLE channels               (* A function of channels: [Id -> Channel] *)

(* When a channel is not busy, it has this value. *)
Null == <<>>

TypeOK == channels[Id] \in (Data \cup {Null})

Busy ==
   channels[Id] # Null

Send(data) ==
   /\ \lnot Busy
   /\ channels' = [channels EXCEPT ![Id] = data]
   (* /\ Assert(data \in Data, <<"Sending invalid data", data, "while expecting", Data>>) *)

Recv(data) ==
   /\ Busy
   /\ data = channels[Id]
   /\ channels' = [channels EXCEPT ![Id] = Null]
   (* /\ Assert(data \in Data, <<"Receiving invalid data", data, "while expecting", Data>>) *)

Get == channels[Id]

Discard ==
   /\ Busy
   /\ channels' = [channels EXCEPT ![Id] = Null]

Sending ==
   IF Busy
   THEN {channels[Id]}
   ELSE {}

InitValue == Null

=============================================================================
