---- MODULE HS -----------------------------------------------------------------
EXTENDS Constants
(* Documentation *)
--------------------------------------------------------------------------------

VARIABLES
   hs_room
 , hs_todevice
 , hs_to_device
 , hs_device_mx_id
 , hs_device_sync_token
 , device_to_hs

LOCAL INSTANCE TLC
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
LOCAL INSTANCE Common
LOCAL INSTANCE DeviceHSChannels
LOCAL INSTANCE Util

Protocol == INSTANCE Protocol

HSDeviceMxId == UNION {
     {InvalidId},   (* InvalidId means this device is not logged in *)
     MxId
   }

HSDeviceSyncToken == UNION {
     {NoToken},         (* NoToken means this device is not syncing *)
     Token
   }

HSRoomMessage ==
   [sender: MxId,
    contents: Protocol!RoomMessageContents]

HSToDeviceMessage ==
   [sender: MxId,
    contents: Protocol!ToDeviceContents]

IsDeviceLoggedIn(device_id) == hs_device_mx_id[device_id] # InvalidId

IsDeviceSyncing(device_id) == hs_device_sync_token[device_id] # NoToken

TypeOK ==
   /\ CheckTRUE("hs_device_mx_id", \A device_id \in DeviceId: hs_device_mx_id[device_id] \in HSDeviceMxId)
   /\ CheckTRUE("hs_device_sync_token", \A device_id \in DeviceId: hs_device_sync_token[device_id] \in HSDeviceSyncToken)
   /\ CheckTRUE("hs_todevice", \A device_id \in DeviceId: \A message_id \in DOMAIN(hs_todevice[device_id]): hs_todevice[device_id][message_id] \in UNION {HSToDeviceMessage, [synced: {{}}]})
   /\ CheckTRUE("hs_room", \A message_id \in DOMAIN(hs_room): hs_room[message_id] \in HSRoomMessage)

Init ==
   /\ hs_room = <<>>
   /\ hs_todevice = [device_id \in DeviceId |-> <<>>]
   /\ hs_device_mx_id = [device_id \in DeviceId |-> InvalidId]
   /\ hs_device_sync_token = [device_id \in DeviceId |-> NoToken]

ProcessLogin(unchanged_others) ==
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
   /\ unchanged_others

ProcessSync(unchanged_others) ==
   \E device_id \in DeviceId:
   LET event == DeviceToHS(device_id)!Get IN
   /\ DeviceToHS(device_id)!Discard
   /\ event.message = "Sync"
   /\ Assert(hs_device_sync_token[device_id] = NoToken, <<"Device", device_id, "tried to sync while it was already syncing">>)
   /\ hs_device_sync_token' = [hs_device_sync_token EXCEPT ![device_id] = event.contents]
   /\ UNCHANGED<<hs_to_device, hs_room, hs_todevice, hs_device_mx_id>>
   /\ unchanged_others

ProcessRoomMessage(unchanged_others) ==
   \E device_id \in DeviceId:
   LET message == DeviceToHS(device_id)!Get IN
   /\ DeviceToHS(device_id)!Discard
   /\ message.message = "RoomMessage"
   /\ hs_room' = hs_room \o <<[sender   |-> hs_device_mx_id[device_id],
                               contents |-> message.contents]>>
   /\ UNCHANGED<<hs_device_sync_token, hs_to_device, hs_todevice, hs_device_mx_id>>
   /\ unchanged_others

ProcessToDevice(unchanged_others) ==
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
   /\ unchanged_others

SendSyncResponses(unchanged_others) ==
   \E device_id \in DeviceId:
   LET token == Check(Token, hs_device_sync_token[device_id]) IN
   /\ token # NoToken
   /\ \/ Len(hs_room) >= token.room
      \/ Len(hs_todevice[device_id]) >= token.todevice
   /\ hs_device_sync_token' = [hs_device_sync_token EXCEPT ![device_id] = NoToken]
   /\ IF Len(hs_room) >= token.room THEN
         /\ HSToDevice(device_id)!Send([message  |-> "RoomMessage",
                                        sender   |-> hs_room[token.room].sender,
                                        contents |-> hs_room[token.room].contents,
                                        token    |-> Check(Token, [token EXCEPT !.room = @ + 1])])
         /\ UNCHANGED<<hs_todevice>>
      ELSE
         /\ HSToDevice(device_id)!Send([message  |-> "ToDevice",
                                        sender   |-> hs_todevice[device_id][token.todevice].sender,
                                        contents |-> hs_todevice[device_id][token.todevice].contents,
                                        token    |-> Check(Token, [token EXCEPT !.todevice = @ + 1])])
         (* easier to see synced messages.. *)
         /\ hs_todevice' = [hs_todevice EXCEPT ![device_id][token.todevice] = [synced |-> {}]]
   /\ UNCHANGED<<hs_device_mx_id, device_to_hs, hs_room>>
   /\ unchanged_others

Next(unchanged_others) ==
   \/ ProcessLogin(unchanged_others)
   \/ ProcessSync(unchanged_others)
   \/ ProcessRoomMessage(unchanged_others)
   \/ ProcessToDevice(unchanged_others)
   \/ SendSyncResponses(unchanged_others)
================================================================================
