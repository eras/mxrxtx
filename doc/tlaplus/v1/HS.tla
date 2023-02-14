---- MODULE HS -----------------------------------------------------------------
(*
  Homeserver has two kinds of ways to pass messages: rooms and ToDevice events.  To keep track of
  which events have been sent to clients there are two variables:

   - hs_room that contains the list of all messages sent to the one room
   - hs_todevice[DeviceId] that contains the list of ToDevice messages not received by a Device

  SyncToken contains the index which indicates which message the device has not yet seen; e.g. value
  [ room: 1 ] indicates that the device has not seen any messages in the room and once there is a
  message at index 1, it will be delivered to the device when the device is syncing. These syncing
  tokens are tracked by the variable hs_device_sync_token which is updated with the sync token when
  a Sync request comes in and similarly reset when a sync response is sent out.

  Sync mesages are handled similarly with ToDevice events, except in that case there is a
  separate entry in hs_todevice for each Device. When a ToDevice message is received by HS
  it will add the message either to the hs_todevice[DeviceId] for the device, or in case of
  sending a message to device id 0 = all devices, it will be put to all the devices shared
  by the same MxId.

*)

EXTENDS Base
--------------------------------------------------------------------------------

LOCAL INSTANCE TLC
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
LOCAL INSTANCE DeviceHSChannels
LOCAL INSTANCE Util

Protocol == INSTANCE Protocol

HSDeviceMxId == UNION {
     {InvalidId},   (* InvalidId means this device is not logged in *)
     MxId
   }

HSDeviceSyncSyncToken == UNION {
     {NoSyncToken},         (* NoSyncToken means this device is not syncing *)
     SyncToken
   }

HSRoomMessage ==
   [sender: MxId,
    contents: Protocol!RoomMessageContents]

HSToDeviceMessage ==
   [sender: MxId,
    contents: Protocol!ToDeviceContents]

IsDeviceLoggedIn(device_id) == hs_device_mx_id[device_id] # InvalidId

IsDeviceSyncing(device_id) == hs_device_sync_token[device_id] # NoSyncToken

TypeOK ==
   /\ CheckTRUE("hs_device_mx_id", \A device_id \in DeviceId: hs_device_mx_id[device_id] \in HSDeviceMxId)
   /\ CheckTRUE("hs_device_sync_token", \A device_id \in DeviceId: hs_device_sync_token[device_id] \in HSDeviceSyncSyncToken)
   /\ CheckTRUE("hs_todevice", \A device_id \in DeviceId: \A message_id \in DOMAIN(hs_todevice[device_id]): hs_todevice[device_id][message_id] \in UNION {HSToDeviceMessage, [synced: {{}}]})
   /\ CheckTRUE("hs_room", \A message_id \in DOMAIN(hs_room): hs_room[message_id] \in HSRoomMessage)

Init ==
   /\ hs_room = <<>>
   /\ hs_todevice = [device_id \in DeviceId |-> <<>>]
   /\ hs_device_mx_id = [device_id \in DeviceId |-> InvalidId]
   /\ hs_device_sync_token = [device_id \in DeviceId |-> NoSyncToken]

ProcessLogin ==
   \E device_id \in DeviceId:
   LET event == DeviceToHS(device_id)!Get IN
   /\ ~IsDeviceLoggedIn(device_id)
   /\ DeviceToHS(device_id)!Discard
   /\ event.message = "Login"
   /\ hs_device_mx_id' = [hs_device_mx_id EXCEPT ![device_id] = event.contents.mx_id]
   /\ HSToDevice(device_id)!Send([message |-> "LoginOK",
                                  token   |-> [room     |-> Len(hs_room) + 1,
                                               todevice |-> Len(hs_todevice[device_id]) + 1]])
   /\ UNCHANGED<<hs_device_sync_token, hs_room, hs_todevice>>

ProcessSync ==
   \E device_id \in DeviceId:
   LET event == DeviceToHS(device_id)!Get IN
   /\ DeviceToHS(device_id)!Discard
   /\ event.message = "Sync"
   /\ Assert(hs_device_sync_token[device_id] = NoSyncToken, <<"Device", device_id, "tried to sync while it was already syncing">>)
   /\ hs_device_sync_token' = [hs_device_sync_token EXCEPT ![device_id] = event.contents]
   /\ UNCHANGED<<hs_to_device, hs_room, hs_todevice, hs_device_mx_id>>

ProcessRoomMessage ==
   \E device_id \in DeviceId:
   LET message == DeviceToHS(device_id)!Get IN
   /\ DeviceToHS(device_id)!Discard
   /\ message.message = "RoomMessage"
   /\ hs_room' = hs_room \o <<[sender   |-> hs_device_mx_id[device_id],
                               contents |-> message.contents]>>
   /\ UNCHANGED<<hs_device_sync_token, hs_to_device, hs_todevice, hs_device_mx_id>>

ProcessToDevice ==
   \E from_device_id \in DeviceId:
   LET event == DeviceToHS(from_device_id)!Get IN
   /\ DeviceToHS(from_device_id)!Discard
   /\ event.message = "ToDevice"
   /\ hs_todevice' = [device_id \in DeviceId |->
                      IF /\ hs_device_mx_id[device_id] = event.mx_id
                         /\ event.device_id \in {0, device_id} THEN
                         Append(hs_todevice[device_id],
                                [ sender   |-> hs_device_mx_id[from_device_id]
                                , contents |-> event.contents ])
                      ELSE
                         hs_todevice[device_id]
                      ]
   /\ UNCHANGED<<hs_device_sync_token, hs_to_device, hs_device_mx_id, hs_room>>

SendSyncResponses ==
   \E device_id \in DeviceId:
   LET token == Check(SyncToken, hs_device_sync_token[device_id]) IN
   /\ token # NoSyncToken
   /\ \/ Len(hs_room) >= token.room
      \/ Len(hs_todevice[device_id]) >= token.todevice
   /\ hs_device_sync_token' = [hs_device_sync_token EXCEPT ![device_id] = NoSyncToken]
   /\ IF Len(hs_room) >= token.room THEN
         /\ HSToDevice(device_id)!Send([message  |-> "RoomMessage",
                                        sender   |-> hs_room[token.room].sender,
                                        contents |-> hs_room[token.room].contents,
                                        token    |-> Check(SyncToken, [token EXCEPT !.room = @ + 1])])
         /\ UNCHANGED<<hs_todevice>>
      ELSE
         /\ HSToDevice(device_id)!Send([message  |-> "ToDevice",
                                        sender   |-> hs_todevice[device_id][token.todevice].sender,
                                        contents |-> hs_todevice[device_id][token.todevice].contents,
                                        token    |-> Check(SyncToken, [token EXCEPT !.todevice = @ + 1])])
         (* easier to see synced messages.. *)
         /\ hs_todevice' = [hs_todevice EXCEPT ![device_id][token.todevice] = [synced |-> {}]]
   /\ UNCHANGED<<hs_device_mx_id, device_to_hs, hs_room>>

(* An invariant that a HS is always able to receive input *)
(* Defined here as it's rather closely related to spec *)
NeverBlocks ==
   \A device_id \in DeviceId:
      DeviceToHS(device_id)!Busy =>
         \/ ENABLED(ProcessLogin)
         \/ ENABLED(ProcessSync)
         \/ ENABLED(ProcessToDevice)
         \/ ENABLED(ProcessRoomMessage)
         \/ ENABLED(ProcessToDevice)

Next ==
   \/ ProcessLogin
   \/ ProcessSync
   \/ ProcessRoomMessage
   \/ ProcessToDevice
   \/ SendSyncResponses

Liveness ==
   /\ WF_<<hs_vars, hs_to_device, device_to_hs>>(Next)
================================================================================
