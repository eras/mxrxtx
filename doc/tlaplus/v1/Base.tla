---- MODULE Base ---------------------------------------------------------------
EXTENDS Constants
(* Variables shared by Model and the Model Checking files *)
--------------------------------------------------------------------------------
VARIABLES
   device                       (* refer to Device.tla *)
 , hs_room                      (* HS.tla: Messages in a room *)
 , hs_todevice                  (* HS.tla: todevice-messages (indexed by <<device_id, device_id>>) *)
 , hs_device_mx_id              (* HS.tla: mapping from device id to mx id *)
 , hs_device_sync_token         (* HS.tla: for each device id, its curent sync token, if it's syncing *)
 , hs_to_device                 (* channel hs->device *)
 , device_to_hs                 (* channel device->hs *)
 , monitor                      (* device monitor state *)
 , offer                        (* device offer state *)
 , datachannel                  (* device to device webrtc datachannel *)

INSTANCE Common

hs_vars == <<hs_room, hs_todevice, hs_device_mx_id, hs_device_sync_token>>

device_vars == <<device, monitor, offer, datachannel>>

all_vars == <<
   device_vars
 , hs_vars
 , hs_to_device, device_to_hs
>>

================================================================================
