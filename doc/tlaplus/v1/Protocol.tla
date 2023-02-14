---- MODULE Protocol -----------------------------------------------------------
(*
  Protocol v1 for mxrxtx works as follows:

  - Device A sends a custom message to a room describing which files it wants to offer and some
    metadata about them
  - Device B is informed about the URI for this event and retrieves the contents of the event.
    In this model this part is handled by Device B actively monitoring the room and is able
    to retriev the offer contents that way.
  - Device B sends a custom ToDevice message to A to start the WebRTC handshake (ice servers may be
    consulted)
  - Device A responds to client B to continue the WebRTC handshake
  - Clients A and B have now formed a WebRTC data channel connection
  - Device A starts sending the contents of the offer from start to end (no framing so far)
  - Device B received the contents and writes them to a file
  - Once Device B has received the final chunk it sends acknowledgement to A and terminates
  - Device A reads the acknowledgement from B and the session A-B is finished; other concurrent or
    future sessions may continue
  - Device A is finally explicitly terminated

  In terms of protocol messages here the flow goes with:
  - A->HS : Login
  - HS->A: LoginOK
  - B->HS : Login
  - HS->B: LoginOK
  - A->HS: Sync
  - B->HS: Sync
  - A->HS: Offer
  - HS->A: Sync: Offer
  - A->HS: Sync
  - B->HS: Sync
  - HS->B: Sync: Offer
  - A->HS: ToDevice(to: b_mxid, to_device: 0, WebRTCOffer(..from_device: A, session_id: 1))
  - HS->B: ToDevice(from: a_mxid, WebRTCOffer(..))
  - B->HS: Sync
  - B->HS: ToDevice(to: a_mxid, to_device: A,
  - HS->B: ToDevice(from: B_mxid, WebRTCAnswer(..from_device: B, session_id: 1))

  There's also an established message from A to B in the model which we ignore here.

  Actual WebRTC messages are specified in DataChannels!DataChannelMessage
  - B->A: Data(data_at_index(0))
  - B->A: Data(data_at_index(1))
  - B->A: Data(data_at_index(2))
  - A->B: Data(ack)

  Fin.

*)
EXTENDS Constants
--------------------------------------------------------------------------------
LOCAL INSTANCE Sequences
LOCAL INSTANCE Common
LOCAL INSTANCE Naturals
LOCAL INSTANCE Util
LOCAL INSTANCE TLC

(* Login gives the MxId of the device *)
LoginMessageContents ==
   [ mx_id: MxId
   ]

LoginMessage ==
   [ message: {"Login"}
   , contents: LoginMessageContents
   ]

(* Set of legal file names *)
FileName == {"a", "b", "c"}

(* Offers contain file name, file size, and a checksum.
   Checksum is just <<"CK", <<contents of the file>>>> to make it simple to compare
   against the actual file contents. *)
OfferFile ==
   UNION
   {{[ name     |-> name
     , size     |-> size
     , checksum |-> cksum]:
      cksum \in {"CK"} \X SeqsOfLength(FileData, {size})}:
    name \in FileName,
    size \in OfferFileSize}

(* Given a file name and its contents, return an OfferFile *)
MakeOfferFile(name, data) ==
   [ name     |-> name
   , size     |-> Len(data)
   , checksum |-> <<"CK", data>> ]

(* Valid sets of files to offer *)
OfferFiles == SeqsOfLength(OfferFile, NumOfferFiles)

(* Valid Offer *)
Offer ==
   [ offer: OfferFiles ]

(* Send a message to a room *)
RoomMessageContents == Offer    (* So far only Offers can be sent to a room *)

RoomMessage ==
   [ message  : {"RoomMessage"}
   , contents : RoomMessageContents]

(* Request from Device to sync room contents starting from the given SyncToken *)
Sync ==
   [ message  : {"Sync"}
   , contents : SyncToken]

(* Valid WebRTC handshake messages sent to a device *)
ToDeviceContentsWebRTC ==
   [ message   : {"WebRTC"}
   , webrtc    : {"offer", "answer", "established"}
   , session_id: SessionId
   , device_id : {0} \cup DeviceId
   ]

(* Only WebRTC handshakes are sent with ToDevice *)
ToDeviceContents ==
   UNION { ToDeviceContentsWebRTC }

(* Messages sent directly (well via HS) to one or multiple destination devices of a single MxId *)
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

(* Login was ok; here's a sync token Device can use to get new messages *)
LoginOK ==
   [ message  : {"LoginOK"}
   , token    : SyncToken]

(* Room event we can read from HSToDevice *)
RoomEvent ==
   [ message  : {"RoomMessage"}
   , sender   : MxId
   , contents : RoomMessageContents
   , token    : SyncToken]

(* ToDevice event we can read from HSToDevice *)
ToDeviceEvent ==
   [ message  : {"ToDevice"}
   , sender   : MxId
   , contents : ToDeviceContents
   , token    : SyncToken]

(* Set of valid messages from HS to Device *)
HSToDeviceMessages == UNION {
      LoginOK
    , RoomEvent
    , ToDeviceEvent
   }

================================================================================
