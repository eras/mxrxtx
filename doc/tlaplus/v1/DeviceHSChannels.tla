---- MODULE DeviceHSChannels ---------------------------------------------------
(* Documentation *)
--------------------------------------------------------------------------------
CONSTANT
   DeviceId
 , MxId
 , NumBaseTokens
 , FileData
 , FileSize
 , OfferFileSize
 , NumOfferFiles

VARIABLES
   device_to_hs
 , hs_to_device

LOCAL INSTANCE Common
LOCAL INSTANCE Protocol

(* Messages from device to HS *)
DeviceToHS(device_id) ==
   INSTANCE MChannel WITH
      Id       <- device_id
    , Data     <- DeviceToHSMessages
    , channels <- device_to_hs

(* Messages from HS to device *)
HSToDevice(device_id) ==
   INSTANCE MChannel WITH
      Id       <- device_id
    , Data     <- HSToDeviceMessages
    , channels <- hs_to_device

InitDeviceHSChannels ==
   /\ device_to_hs = [device_id \in DeviceId |-> DeviceToHS(device_id)!InitValue]
   /\ hs_to_device = [device_id \in DeviceId |-> HSToDevice(device_id)!InitValue]

================================================================================
