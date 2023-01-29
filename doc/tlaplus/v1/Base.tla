---- MODULE Base ---------------------------------------------------------------
EXTENDS Constants
(* Variables shared by Model and the Model Checking files *)
--------------------------------------------------------------------------------
VARIABLES
   devices                      (* refer to Device.tla *)
 , hs_room                      (* refer to HS.tla *)
 , hs_todevice
 , hs_device_mx_id
 , hs_device_sync_token
 , hs_to_device                 (* channel hs->device *)
 , device_to_hs                 (* channel device->hs *)
 , monitor                      (* device monitor state *)
 , offer                        (* device offer state *)
 , datachannel                  (* device to device webrtc datachannel *)

INSTANCE Common

hs_vars == <<hs_room, hs_todevice, hs_device_mx_id, hs_device_sync_token>>

device_vars == <<devices, monitor, offer, datachannel>>

all_vars == <<
   device_vars
 , hs_vars
 , hs_to_device, device_to_hs
>>

================================================================================
