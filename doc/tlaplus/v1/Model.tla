---- MODULE Model --------------------------------------------------------------
EXTENDS Base
(* Documentation *)
--------------------------------------------------------------------------------
LOCAL INSTANCE Util

Device(device_id) == INSTANCE Device WITH Id <- device_id

INSTANCE DeviceHSChannels
INSTANCE DataChannels
LOCAL INSTANCE Json
LOCAL INSTANCE TLC
LOCAL INSTANCE Sequences

HS == INSTANCE HS

TypeOK ==
   /\ CheckTRUE("HS", HS!TypeOK)
   /\ CheckTRUE("Device", \A device_id \in DeviceId: Device(device_id)!TypeOK)
   /\ CheckTRUE("DeviceToHS", \A device_id \in DeviceId: DeviceToHS(device_id)!TypeOK)
   /\ CheckTRUE("HSToDevice", \A device_id \in DeviceId: HSToDevice(device_id)!TypeOK)
   /\ CheckTRUE("DataChannel", \A data_channel_id \in DataChannelId: DataChannel!TypeOK(data_channel_id))

Next ==
   \/ HS!Next /\ UNCHANGED<<device_vars>>
   \/ (\E device_id \in DeviceId: Device(device_id)!Next /\ UNCHANGED<<hs_vars>>)

Liveness ==
  /\ HS!Liveness
  /\ \A device_id \in DeviceId: Device(device_id)!Liveness

Init ==
   /\ HS!Init
   /\ monitor = [device_id \in DeviceId |-> Device(device_id)!Monitor!InitValue]
   /\ offer = [device_id \in DeviceId |-> Device(device_id)!Offer!InitValue]
   /\ \A device_id \in DeviceId: Device(device_id)!Init
   /\ InitDeviceHSChannels
   /\ InitDataChannels

Spec == Init /\ [][Next]_all_vars /\ Liveness

(* Useful messages we want to visualize with TLSD *)
AllMessages ==
   UNION {
      UNION {
         UNION {
           {{<<"server", 1>>} \X {<<"device", device_id>>} \X HSToDevice(device_id)!Sending}
         , {{<<"device", device_id>>} \X {<<"server", 1>>} \X DeviceToHS(device_id)!Sending}
         } : device_id \in DeviceId
      },
      UNION {
         UNION {
           {{<<"device", a>>} \X {<<"device", b>>} \X DataChannel!A(a, b, label)!Sending}
         , {{<<"device", b>>} \X {<<"device", a>>} \X DataChannel!A(b, a, label)!Sending}
         } : <<a, b, label>> \in DataChannelId
      }
   }

(* Useful state we want to visualize with TLSD *)
State ==
   [ server |-> <<[room |-> Len(hs_room),
                   todevice |-> [device_id \in DeviceId |-> hs_todevice[device_id]],
                   syncing |-> [device_id \in {device_id \in DeviceId: hs_device_sync_token[device_id] # NoSyncToken} |->
                                hs_device_sync_token[device_id]]]>>
   , device |-> [id \in DeviceId |-> Device(id)!State]
   ]

(* Useful data we want to visualize with TLSD *)
AliasMessages ==
   [
     (* lane_order_json |-> ToJson(<<"client", "server">>) *)
     messages_json |-> ToJson(AllMessages)
   , state_json |-> ToJson(State)
   ]
================================================================================
