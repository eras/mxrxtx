---- MODULE Model --------------------------------------------------------------
EXTENDS Base
(* Documentation *)
--------------------------------------------------------------------------------
LOCAL INSTANCE Util

Device(device_id) == INSTANCE Device WITH Id <- device_id

INSTANCE DeviceHSChannels
INSTANCE DataChannels


HS == INSTANCE HS

TypeOK ==
   /\ CheckTRUE("HS", HS!TypeOK)
   /\ CheckTRUE("Device", \A device_id \in DeviceId: Device(device_id)!TypeOK)
   /\ CheckTRUE("DeviceToHS", \A device_id \in DeviceId: DeviceToHS(device_id)!TypeOK)
   /\ CheckTRUE("HSToDevice", \A device_id \in DeviceId: HSToDevice(device_id)!TypeOK)
   /\ CheckTRUE("DataChannel", \A data_channel_id \in DataChannelId: DataChannel!TypeOK(data_channel_id))

Next ==
   \/ HS!Next(UNCHANGED<<device_vars>>)
   \/ \E device_id \in DeviceId: Device(device_id)!Next(UNCHANGED<<hs_vars>>)

Init ==
   /\ HS!Init
   /\ monitor = [device_id \in DeviceId |-> Device(device_id)!Monitor!InitValue]
   /\ offer = [device_id \in DeviceId |-> Device(device_id)!Offer!InitValue]
   /\ \A device_id \in DeviceId: Device(device_id)!Init
   /\ InitDeviceHSChannels
   /\ InitDataChannels

Spec == Init /\ [][Next]_all_vars

================================================================================
