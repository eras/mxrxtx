---- MODULE Protocol -----------------------------------------------------------
(* Documentation *)
--------------------------------------------------------------------------------
CONSTANT
   DeviceId
 , MxId
 , SessionId
 , NumBaseTokens
 , FileData
 , FileSize
 , OfferFileSize
 , NumOfferFiles

LOCAL INSTANCE Sequences
LOCAL INSTANCE Common
LOCAL INSTANCE Naturals
LOCAL INSTANCE Util
LOCAL INSTANCE TLC

(* Login *)
LoginMessageContents ==
   [ mx_id: MxId
   ]

LoginMessage ==
   [ message: {"Login"}
   , contents: LoginMessageContents
   ]

FileName == {"a", "b", "c"}

OfferFile ==
   UNION
   {{[ name     |-> name
     , size     |-> size
     , checksum |-> cksum]:
      cksum \in {"CK"} \X SeqsOfLength(FileData, {size})}:
    name \in FileName,
    size \in OfferFileSize}

MakeOfferFile(name, data) ==
   [ name     |-> name
   , size     |-> Len(data)
   , checksum |-> <<"CK", data>> ]

OfferFiles == SeqsOfLength(OfferFile, NumOfferFiles)

Offer ==
   [ offer: OfferFiles ]

(* Send a message to a room *)
RoomMessageContents == Offer

RoomMessage ==
   [ message  : {"RoomMessage"}
   , contents : RoomMessageContents]

(* Request sync *)
Sync ==
   [ message  : {"Sync"}
   , contents : Token]

(* Send a message to a device *)
ToDeviceContentsWebRTC ==
   [ message   : {"WebRTC"}
   , webrtc    : {"offer", "answer", "established"}
   , session_id: SessionId
   , device_id : {0} \cup DeviceId
   ]

ToDeviceContents ==
   UNION { ToDeviceContentsWebRTC }

ToDevice ==
   [ message   : {"ToDevice"}
   , mx_id     : MxId
   , device_id : {0} \cup DeviceId (* 0 means "all device" *)
   , contents  : ToDeviceContents]

(* Messages device can send to homeserver *)
DeviceToHSMessages == UNION {
      LoginMessage
    , RoomMessage
    , Sync
    , ToDevice
   }

(* Messages homeserver can send to device *)
LoginOK ==
   [ message  : {"LoginOK"}
   , token    : Token]

RoomEvent ==
   [ message  : {"RoomMessage"}
   , sender   : MxId
   , contents : RoomMessageContents
   , token    : Token]

ToDeviceEvent ==
   [ message  : {"ToDevice"}
   , sender   : MxId
   , contents : ToDeviceContents
   , token    : Token]

HSToDeviceMessages == UNION {
      LoginOK
    , RoomEvent
    , ToDeviceEvent
   }

================================================================================
