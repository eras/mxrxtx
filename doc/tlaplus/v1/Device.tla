---- MODULE Device -------------------------------------------------------------
(*
  Devices are the clients of the homeserver. Their basic function is to:

  - Login
  - Start syncing messages
  - If Id \in CanOffer: Send an offer to the room
  - If Id \in CanMonitor: Upon receiving an offer in the room, start transferring it

  Actual data exchange is set up by using ToDevice messages. Monitor always initiates these
  exchanges by sending a WebRTC offer to all devices of the sender (device_id=0) with a new unique
  session id.

  The unique session id is to handle the case where a Monitor might crash (not yet modeled by this
  model) and would restart and try to do the transfer again. In this case it would seem to the Offer
  that the messages might relate to the previous session, but with the help of the session id the
  Offer can determine that the messagse are indeed part of a separate session (and may also discard
  the old session).

  Once the WebRTC exchange has been established, Offer starts sending the contents of the offer one
  chunk (FileData) at a time, in the same order as the files are presented in the offer contents.
  Once the Monitor of the Session has received all the chunks it will respond with [ack: TRUE] and
  the Offer will enter a complete state, shortly after which it resets back to the
  "waiting-webrtc-offer" state.

  Offer is able to handle Session concurrent downloads.
*)

EXTENDS Base
--------------------------------------------------------------------------------
CONSTANT
   Id                           (* Assigned DeviceId *)

LOCAL INSTANCE TLC              (* Assert, Print *)
LOCAL INSTANCE Util             (* Check, SeqsOfLength *)
LOCAL INSTANCE DeviceHSChannels (* Device--HS channels *)
LOCAL INSTANCE DataChannels     (* Device--Device channels *)
LOCAL INSTANCE Naturals         (* + *)
LOCAL INSTANCE Sequences        (* Append *)
LOCAL INSTANCE SequencesExt     (* FoldSeq *)

Protocol == INSTANCE Protocol

Self == device[Id]              (* Shorthand *)

(* for more recent TLC, more recent SequencesExt? *)
(* TotalSizeOfOffer(offer_files) == FoldSeq(LAMBDA a, b: a.size + b, 0, offer_files) *)
TotalSizeOfOffer(offer_files) == FoldLeft(LAMBDA b, a: a.size + b, 0, offer_files)

(* Returns a sequence of tuples <<index, begin_offset, end_offset>> *)
CumulativeOfferFileSizes(offer_files) ==
   Tail(
      FoldLeft(LAMBDA sizes, offer2:
                  Append(sizes,
                         <<Len(sizes),
                           sizes[Len(sizes)][3],
                           offer2.size + sizes[Len(sizes)][3]>>),
               <<<<0, 0, 0>>>>,
               offer_files)
   )

(* Given an offset and the files of an offer, return a record [ offset: Nat, index: Nat ] that
   indicates which file index and which offset in it is the next to process*)
CurrentOfferFileIndexOffset(offset, offer_files) ==
   LET file_ofs1_ofs2 ==
      SelectSeq(CumulativeOfferFileSizes(offer_files),
                LAMBDA file_size:
                   /\ offset >= file_size[2]
                   /\ offset < file_size[3])
         [1] (* pick the first element of the presumably 1-element array *)
   IN
     [ offset |-> offset - file_ofs1_ofs2[2]
     , index  |-> file_ofs1_ofs2[1] ] (* pick the index of the file in the offer_files and receive *)

(* List of session ids used globally; used for emulating UUIDs *)
UsedSessionIds ==
   { session_id \in SessionId:
     \E device_id \in DeviceId:
        \/ monitor[device_id].session_id = session_id
        \/ offer[device_id].session[session_id].state \notin {"", "waiting-webrtc-offer"}
   }

(* Available session ids are the set of all session ids without the used ones *)
AvailableSessionIds ==
   SessionId \ UsedSessionIds

---- MODULE Monitor ------------------------------------------------------------
--------------------------------------------------------------------------------
Monitor ==
   [ \* The offer Monitor has received
     offer          : {<<>>} \cup Protocol!OfferFiles
     \* The MxId we're currently downloading an offer from
   , peer_mx_id     : {0} \cup MxId
     \* The Device we're currently downloading an offer from
   , peer_device_id : {0} \cup DeviceId
     \* The data we have downloaded, indexed by the file names in offer
   , received       : SeqsOfLength(SeqsOfLength(FileData, FileSize), {0} \cup NumOfferFiles)
   , state          : { "disabled"           (* This Monitor is not configured to be in use *)
                      , "wait-mxrxtx-offer"  (* Waiting to receive an offer in the room *)
                      , "has-mxrxtx-offer"   (* An offer has been received; start handshake *)
                      , "sent-webrtc-offer"  (* The handshake has been initiated, waiting response *)
                      , "downloading"        (* Downloading is in progress *)
                      , "complete"           (* Downloading is complete *)
                      }
     \* SessionId to distinguish retries
   , session_id     : {0} \cup SessionId
   ]

TypeOK ==
   /\ CheckTRUE(<<Monitor>>, monitor[Id] \in Monitor)

(* Process a room event (used by Client!ProcessRoomEvent) *)
ProcessRoomEvent(room_event) ==
   IF /\ monitor[Id].state = "wait-mxrxtx-offer"
   THEN
      /\ monitor' = [monitor EXCEPT
                      ![Id].offer      = room_event.contents.offer
                    , ![Id].peer_mx_id = room_event.sender
                    , ![Id].state      = "has-mxrxtx-offer"
                    , ![Id].received   = [index \in DOMAIN(room_event.contents.offer) |-> <<>>]
                    ]
      /\ UNCHANGED<<datachannel, device_to_hs>>
   ELSE
      UNCHANGED<<datachannel, device_to_hs, monitor>>

(* An offer has been read: establish a session with the MxId that created the offer *)
EstablishSession ==
   /\ monitor[Id].state = "has-mxrxtx-offer"
   \* Select a free session id
   /\ LET session_id == CHOOSE session_id \in AvailableSessionIds: TRUE IN
      \* Send the offer to device_id 0=all devices as we don't know the device id yet
      /\ DeviceToHS(Id)!Send([ message   |-> "ToDevice"
                             , mx_id     |-> monitor[Id].peer_mx_id
                             , device_id |-> 0
                             , contents  |-> [ message    |-> "WebRTC"
                                             , session_id |-> session_id
                                             , webrtc     |-> "offer"
                                             , device_id  |-> Id ]
                             ])
      /\ monitor' = [monitor EXCEPT
                      ![Id].state      = "sent-webrtc-offer"
                    , ![Id].session_id = session_id
                    ]
      /\ UNCHANGED<<datachannel, offer, device, hs_to_device>>

TotalSizeOfReceived ==
   (* FoldSeq(LAMBDA a, b: Len(a) + b, 0, monitor[Id].received) *)
   FoldLeft(LAMBDA b, a: Len(a) + b, 0, monitor[Id].received)

(* When downloading and not everything has been received, download a data fragment from peer via DataChannel *)
DoDownload ==
   /\ monitor[Id].state = "downloading"
   /\ TotalSizeOfReceived < TotalSizeOfOffer(monitor[Id].offer)
   /\ \E peer_device_id \in DeviceId:
      \E message \in DataChannelMessage:
      /\ peer_device_id = monitor[Id].peer_device_id
      /\ DataChannel!A(peer_device_id, Id, "data")!Recv(message)
      /\ monitor' = [monitor EXCEPT ![Id].received[CurrentOfferFileIndexOffset(TotalSizeOfReceived, monitor[Id].offer).index] = Append(@, message.data)]
      /\ UNCHANGED<<offer, device, hs_to_device, device_to_hs>>

(* TRUE iff downloaded file contents match the checksum of the offer *)
ValidateChecksum ==
   FoldLeft(LAMBDA ok, index:
              /\ ok
              /\ monitor[Id].offer[index].checksum = <<"CK", monitor[Id].received[index] >>
           , TRUE
           , [n \in 1..Len(monitor[Id].received) |-> n]
           )

(* Once the download is finished, send an "ack" to the peer so it knows everything went fine and it can terminate *)
DoSendAck ==
   /\ monitor[Id].state = "downloading"
   /\ TotalSizeOfReceived = TotalSizeOfOffer(monitor[Id].offer)
   /\ \E peer_device_id \in DeviceId:
      /\ peer_device_id = monitor[Id].peer_device_id
      /\ DataChannel!A(Id, peer_device_id, "data")!Send([ack |-> TRUE])
      /\ monitor' = [monitor EXCEPT ![Id].state = "complete"]
      /\ Assert(ValidateChecksum, "Checksum validation failed")
      /\ UNCHANGED<<offer, device, hs_to_device, device_to_hs>>

(* Process a ToDevice -event is used by Client!Process. Handles the WebRTC answer. *)
ProcessToDeviceEvent(event) ==
   /\ monitor[Id].state = "sent-webrtc-offer"
   /\ Assert(event.sender = monitor[Id].peer_mx_id, "Peer mx id is unexpected")
   /\ Assert(event.contents.message = "WebRTC", "Unexpected todevice message")
   /\ Assert(event.contents.webrtc = "answer", "Unexpected todevice message")
   /\ monitor' = [monitor EXCEPT
                   ![Id].state = "downloading"
                 , ![Id].peer_device_id = event.contents.device_id
                 ]
   /\ DeviceToHS(Id)!Send([ message   |-> "ToDevice"
                          , mx_id     |-> monitor[Id].peer_mx_id
                          , device_id |-> event.contents.device_id
                          , contents  |-> [ message    |-> "WebRTC"
                                          , session_id |-> monitor[Id].session_id
                                          , webrtc     |-> "established"
                                          , device_id  |-> 0 ]
                          ])
   /\ UNCHANGED<<datachannel>>

InitValue ==
   [ offer          |-> <<>>
   , peer_mx_id     |-> 0
   , peer_device_id |-> 0
   , received       |-> <<>>
   , state          |-> IF Id \in CanMonitor THEN "wait-mxrxtx-offer" ELSE "disabled"
   , session_id     |-> 0
   ]

(* Actual initialization is handled by e.g. MC *)
Init ==
   /\ monitor[Id] = InitValue

Next ==
   \/ EstablishSession
   \/ DoDownload
   \/ DoSendAck

State == monitor[Id].state

================================================================================

---- MODULE Offer --------------------------------------------------------------
--------------------------------------------------------------------------------
UploadSession ==
   [ peer_mx_id     : {0} \cup MxId
   , peer_device_id : {0} \cup DeviceId
   , state          : { \* state before the mxrxtx offer has been sent
                        ""
                      \* Waiting for WebRTC offer
                      , "waiting-webrtc-offer"
                      \* Waiting for WebRTC establishment acknowledgement
                      , "waiting-webrtc-establish"
                      \* Uploading offer contents
                      , "uploading"
                      \* Upload done; will be soon reset to waiting-webrtc-offer
                      , "complete"
                      }
   , sent           : Nat
   ]

Offer ==
   [ offer          : Protocol!OfferFiles
   , state          : { \* This Device is not configured to do offers
                        "disabled"
                      \* An mxrxtx offer is going to be sent
                      , "send-mxrxtx-offer"
                      \* An mxrxtx offer has been sent; now waiting for WebRTC offers
                      , "sent-mxrxtx-offer"
                      }
   , session        : [SessionId -> UploadSession]
   ]


TypeOK ==
   /\ CheckTRUE("offer", offer[Id] \in Offer)

(* Send an mxrxtx offer to the room *)
DoOffer ==
   /\ Id \in CanOffer
   /\ Self.logged_in = "yes"
   /\ offer[Id].state = "send-mxrxtx-offer"
   /\ ~Self.offering
   /\ DeviceToHS(Id)!Send([message  |-> "RoomMessage",
                           contents |-> [ offer |-> offer[Id].offer]])
   /\ device' = [device EXCEPT ![Id].offering = TRUE]
   /\ offer' = [offer EXCEPT
                 ![Id].state = "sent-mxrxtx-offer"
                 (* All sessions are set to "waiting-webrtc-offer" *)
               , ![Id].session = [ session_id \in SessionId |->
                                   [offer[Id].session[session_id] EXCEPT
                                    !.state = "waiting-webrtc-offer"] ]
               ]
   /\ UNCHANGED<<datachannel, monitor, hs_to_device>>

(* How many chunks of data we have sent during the Session? *)
TotalSizeOfSent(session_id) == offer[Id].session[session_id].sent

(* We model data storage via the checksum, which already contain the
  original data for modeling purposes :) *)
FileContents(index_offset) ==
  offer[Id].offer[index_offset.index].checksum[2][index_offset.offset + 1]

(* If we haven't uploaded everything this session, then upload the next chunk *)
DoUpload ==
   \E session_id \in SessionId:
   /\ offer[Id].session[session_id].state = "uploading"
   /\ Assert(Self.logged_in = "yes", "Must be logged in by this point")
   /\ TotalSizeOfSent(session_id) < TotalSizeOfOffer(offer[Id].offer)
   /\ \E peer_device_id \in DeviceId:
      /\ peer_device_id = offer[Id].session[session_id].peer_device_id
      /\ LET index_offset == CurrentOfferFileIndexOffset(TotalSizeOfSent(session_id), offer[Id].offer) IN
         /\ DataChannel!A(Id, peer_device_id, "data")!Send([data |-> FileContents(index_offset)])
         /\ offer' = [offer EXCEPT ![Id].session[session_id].state = "uploading"
                                 , ![Id].session[session_id].sent = @ + 1]
         /\ UNCHANGED<<monitor, device, hs_to_device, device_to_hs>>

(* After uploading everything we wait for an acknowledgement from the
   peer, before ending up "complete" *)
DoWaitAck ==
   \E session_id \in SessionId:
   /\ offer[Id].session[session_id].state = "uploading"
   /\ Assert(Self.logged_in = "yes", "Must be logged in by this point")
   /\ TotalSizeOfSent(session_id) = TotalSizeOfOffer(offer[Id].offer)
   /\ \E peer_device_id \in DeviceId:
      /\ peer_device_id = offer[Id].session[session_id].peer_device_id
      /\ DataChannel!A(peer_device_id, Id, "data")!Recv([ack |-> TRUE])
      /\ offer' = [offer EXCEPT ![Id].session[session_id].state = "complete"]
      /\ UNCHANGED<<monitor, device, hs_to_device, device_to_hs>>

(* This state handler is just to make it simpler to see when one session is complete *)
DoReset ==
   \E session_id \in SessionId:
   /\ offer[Id].session[session_id].state = "complete"
   /\ offer' = [offer EXCEPT ![Id].session[session_id].state = "waiting-webrtc-offer"]
   /\ UNCHANGED<<monitor, device, hs_to_device, device_to_hs, datachannel>>

(* Process ToDevice events, used by Client!ProcessToDeviceEvent. Responds to an incoming
   WebRTC offer and reacts to the "established" acknowledgement *)
ProcessToDeviceEvent(event) ==
   \E session_id \in SessionId:
   /\ Assert(Self.logged_in = "yes", "Must be logged in by this point")
   /\ event.contents.session_id = session_id
   /\ event.contents.message = "WebRTC"
   /\ \/ /\ offer[Id].session[session_id].state = "waiting-webrtc-offer"
         /\ event.contents.webrtc = "offer"
         /\ DeviceToHS(Id)!Send([ message   |-> "ToDevice"
                                , mx_id     |-> event.sender
                                , device_id |-> event.contents.device_id
                                , contents  |-> [ message    |-> "WebRTC"
                                                , session_id |-> session_id
                                                , webrtc     |-> "answer"
                                                , device_id  |-> Id ]
                                ])
         /\ offer' = [offer EXCEPT
                        ![Id].session = [@ EXCEPT
                           ![session_id].state = "waiting-webrtc-establish"
                         , ![session_id].peer_mx_id = event.sender
                         , ![session_id].peer_device_id = event.contents.device_id
                         ]
                      ]
      \/ /\ offer[Id].session[session_id].state = "waiting-webrtc-establish"
         /\ event.contents.webrtc = "established"
         /\ Assert(offer[Id].session[session_id].peer_mx_id = event.sender, "Something's broken in multisession transfers")
         /\ offer' = [offer EXCEPT ![Id].session[session_id].state = "uploading"]
         /\ UNCHANGED <<device_to_hs>>

InitUploadSession ==
   [ peer_mx_id     |-> 0
   , peer_device_id |-> 0
   , sent           |-> 0
   , state          |-> ""
   ]

InitValue ==
   [ offer          |-> << Protocol!MakeOfferFile("a", <<0>>)
                         (* , Protocol!MakeOfferFile("b", <<>>) *)
                         , Protocol!MakeOfferFile("c", <<1, 0>>)
                         >>
   , state          |-> IF Id \in CanOffer THEN "send-mxrxtx-offer" ELSE "disabled"
   , session        |-> [ session_id \in SessionId |-> InitUploadSession ]
   ]

Init ==
   /\ offer[Id] = InitValue

Next ==
   \/ DoOffer
   \/ DoUpload
   \/ DoWaitAck
   \/ DoReset

State ==
   [ state    |-> offer[Id].state
   , sessions |-> [ session_id \in SessionId |-> offer[Id].session[session_id].state ]
   ]

================================================================================

Monitor == INSTANCE Monitor
Offer == INSTANCE Offer

LoginState == { "no", "inprogress", "yes" }

Type ==
   [logged_in : LoginState,
    syncing   : BOOLEAN,
    offering  : BOOLEAN,
    token     : SyncToken]

TypeOK ==
   /\ CheckTRUE("Device", Self \in Type)
   /\ Monitor!TypeOK
   /\ Offer!TypeOK

Init ==
   /\ Self \in Type
   /\ Monitor!Init
   /\ Offer!Init

InitValue ==
   [logged_in |-> "no",
    syncing   |-> FALSE,
    offering  |-> FALSE,
    token     |-> NoSyncToken]

(* Log in to the homeserver; in our model this also defines after which moment we start
   to see new messages (sync origin) *)
Login1 ==
   /\ Self.logged_in = "no"
   /\ DeviceToHS(Id)!Send([message |-> "Login",
                           contents |-> [ mx_id |-> Id ]]) (* TODO: implement better device_id <=> mx_id mapping? *)
   /\ device' = [device EXCEPT ![Id] = [@ EXCEPT !.logged_in = "inprogress"]]
   /\ UNCHANGED<<datachannel, offer, monitor, hs_to_device>>

(* Handle the LoginOK message from HS *)
Login2 ==
   LET response == HSToDevice(Id)!Get IN
   /\ Self.logged_in = "inprogress"
   /\ HSToDevice(Id)!Discard
   /\ response.message = "LoginOK"
   /\ device' = [device EXCEPT ![Id] = [@ EXCEPT !.logged_in = "yes", !.token = response.token]]
   /\ UNCHANGED<<datachannel, offer, monitor, device_to_hs>>

(* If the Device is not syncing, send a Sync request with the known sync token *)
Sync ==
   /\ Self.logged_in = "yes"
   /\ ~Self.syncing
   /\ DeviceToHS(Id)!Send([message |-> "Sync",
                           contents |-> Self.token])
   /\ device' = [device EXCEPT ![Id] = [@ EXCEPT !.syncing = TRUE]]
   /\ UNCHANGED<<datachannel, offer, monitor, hs_to_device>>

(* Used by ReceiveSync to process room events; dispatch to Monitor *)
ProcessRoomEvent(room_event) ==
   /\ Monitor!ProcessRoomEvent(room_event)
   /\ UNCHANGED<<datachannel, offer>>

(* Used by ReceiveSync to process ToDevice events; dispatch either to Monitor or Offer *)
ProcessToDeviceEvent(todevice_event) ==
   \/ /\ Monitor!ProcessToDeviceEvent(todevice_event)
      /\ UNCHANGED<<datachannel, offer>>
   \/ /\ Offer!ProcessToDeviceEvent(todevice_event)
      /\ UNCHANGED<<datachannel, monitor>>

(* Process Sync responses from the HS; restarting syncing is handled by Sync *)
ReceiveSync ==
   /\ Self.logged_in = "yes"
   /\ Self.syncing
   /\ LET event == HSToDevice(Id)!Get IN
      /\ HSToDevice(Id)!Discard
      /\ IF event \in Protocol!RoomEvent THEN
            /\ ProcessRoomEvent(event)
         ELSE
            /\ ProcessToDeviceEvent(event)
      /\ device' = [device EXCEPT ![Id] = [@ EXCEPT !.syncing = FALSE,
                                                    !.token = event.token]]

State ==
   [ offer   |-> Offer!State,
     monitor |-> Monitor!State ]

(* An invariant that a Device is always able to receive input *)
(* Defined here as it's rather closely related to spec *)
NeverBlocks ==
   HSToDevice(Id)!Busy =>
      \/ ENABLED(Login2)
      \/ ENABLED(ReceiveSync)

Next ==
   \/ Login1                    (* Send login request *)
   \/ Login2                    (* Receive login response *)
   \/ Sync                      (* Send sync request *)
   \/ Offer!Next                (* Offers progress *)
   \/ Monitor!Next              (* Monitor progresses *)
   \/ ReceiveSync               (* Handle incoming sync response *)

Liveness ==
   /\ WF_<<device_vars, hs_to_device, device_to_hs>>(Next)
================================================================================
