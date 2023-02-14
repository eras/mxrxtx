---- MODULE Device -------------------------------------------------------------
EXTENDS Base
--------------------------------------------------------------------------------
CONSTANT
   Id

LOCAL INSTANCE TLC
LOCAL INSTANCE Util
LOCAL INSTANCE DeviceHSChannels
LOCAL INSTANCE DataChannels
LOCAL INSTANCE Naturals         (* + *)
LOCAL INSTANCE Sequences        (* Append *)
LOCAL INSTANCE SequencesExt     (* FoldSeq *)
LOCAL INSTANCE Functions

Protocol == INSTANCE Protocol

Self == device[Id]

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
   }

AvailableSessionIds ==
   SessionId \ UsedSessionIds

---- MODULE Monitor ------------------------------------------------------------
--------------------------------------------------------------------------------
Monitor ==
   [ offer          : {<<>>} \cup Protocol!OfferFiles
   , peer_mx_id     : {0} \cup MxId
   , peer_device_id : {0} \cup DeviceId
   , received       : SeqsOfLength(SeqsOfLength(FileData, FileSize), {0} \cup NumOfferFiles)
   , state          : { "disabled"
                      , "wait-mxrxtx-offer"
                      , "has-mxrxtx-offer"
                      , "sent-webrtc-offer"
                      , "downloading"
                      , "complete"
                      }
   , session_id     : {0} \cup SessionId
   ]

TypeOK ==
   /\ CheckTRUE(<<Monitor>>, monitor[Id] \in Monitor)

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

EstablishSession ==
   /\ monitor[Id].state = "has-mxrxtx-offer"
   /\ LET session_id == CHOOSE session_id \in AvailableSessionIds: TRUE IN
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

DoDownload ==
   /\ monitor[Id].state = "downloading"
   /\ TotalSizeOfReceived < TotalSizeOfOffer(monitor[Id].offer)
   /\ \E peer_device_id \in DeviceId:
      \E message \in DataChannelMessage:
      /\ peer_device_id = monitor[Id].peer_device_id
      /\ DataChannel!A(peer_device_id, Id, "data")!Recv(message)
      /\ monitor' = [monitor EXCEPT ![Id].received[CurrentOfferFileIndexOffset(TotalSizeOfReceived, monitor[Id].offer).index] = Append(@, message.data)]
      /\ UNCHANGED<<offer, device, hs_to_device, device_to_hs>>

ValidateChecksum ==
   (* TODO *)
   TRUE

DoSendAck ==
   /\ monitor[Id].state = "downloading"
   /\ TotalSizeOfReceived = TotalSizeOfOffer(monitor[Id].offer)
   /\ \E peer_device_id \in DeviceId:
      /\ peer_device_id = monitor[Id].peer_device_id
      /\ DataChannel!A(Id, peer_device_id, "data")!Send([ack |-> TRUE])
      /\ monitor' = [monitor EXCEPT ![Id].state = "complete"]
      /\ Assert(ValidateChecksum, "Checksum validation failed")
      /\ UNCHANGED<<offer, device, hs_to_device, device_to_hs>>

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
   , state          : { ""
                      , "waiting-webrtc-offer"
                      , "waiting-webrtc-establish"
                      , "uploading"
                      , "complete"
                      }
   , sent           : Nat
   ]

Offer ==
   [ offer          : Protocol!OfferFiles
   , state          : { "disabled"
                      , "send-mxrxtx-offer"
                      , "sent-mxrxtx-offer"
                      }
   , session        : [SessionId -> UploadSession]
   ]


TypeOK ==
   /\ CheckTRUE("offer", offer[Id] \in Offer)

DoOffer ==
   /\ Id \in CanOffer
   /\ Self.logged_in = "yes"
   /\ offer[Id].state = "send-mxrxtx-offer"
   /\ ~Self.offering
   (* /\ \E offer_file \in Protocol!OfferFile: *)
      (* /\ DeviceToHS(Id)!Send([message  |-> "RoomMessage", *)
      (*                         contents |-> << offer_file >>]) *)
      (* /\ DeviceToHS(Id)!Send([message  |-> "RoomMessage", *)
      (*                         contents |-> << RandomElement(Protocol!OfferFile) >>]) *)
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

TotalSizeOfSent(session_id) == offer[Id].session[session_id].sent

DoUpload ==
   \E session_id \in SessionId:
   /\ offer[Id].session[session_id].state = "uploading"
   /\ Assert(Self.logged_in = "yes", "Must be logged in by this point")
   /\ TotalSizeOfSent(session_id) < TotalSizeOfOffer(offer[Id].offer)
   /\ \E peer_device_id \in DeviceId:
      /\ peer_device_id = offer[Id].session[session_id].peer_device_id
      /\ LET index_offset == CurrentOfferFileIndexOffset(TotalSizeOfSent(session_id), offer[Id].offer) IN
         /\ DataChannel!A(Id, peer_device_id, "data")!Send([data |-> offer[Id].offer[index_offset.index].checksum[2][index_offset.offset + 1]])
         /\ offer' = [offer EXCEPT ![Id].session = [@ EXCEPT ![session_id].state = "uploading"
                                                           , ![session_id].sent = @ + 1]
                     ]
         /\ UNCHANGED<<monitor, device, hs_to_device, device_to_hs>>

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

Login1 ==
   /\ Self.logged_in = "no"
   /\ DeviceToHS(Id)!Send([message |-> "Login",
                           contents |-> [ mx_id |-> Id ]]) (* TODO: simple device_id <=> mx_id mapping *)
   /\ device' = [device EXCEPT ![Id] = [@ EXCEPT !.logged_in = "inprogress"]]
   /\ UNCHANGED<<datachannel, offer, monitor, hs_to_device>>

Login2 ==
   LET response == HSToDevice(Id)!Get IN
   /\ Self.logged_in = "inprogress"
   /\ HSToDevice(Id)!Discard
   /\ response.message = "LoginOK"
   /\ device' = [device EXCEPT ![Id] = [@ EXCEPT !.logged_in = "yes", !.token = response.token]]
   /\ UNCHANGED<<datachannel, offer, monitor, device_to_hs>>

Sync ==
   /\ Self.logged_in = "yes"
   /\ ~Self.syncing
   /\ DeviceToHS(Id)!Send([message |-> "Sync",
                           contents |-> Self.token])
   /\ device' = [device EXCEPT ![Id] = [@ EXCEPT !.syncing = TRUE]]
   /\ UNCHANGED<<datachannel, offer, monitor, hs_to_device>>

ProcessRoomEvent(room_event) ==
   /\ Monitor!ProcessRoomEvent(room_event)
   /\ UNCHANGED<<datachannel, offer>>

ProcessToDeviceEvent(todevice_event) ==
   \/ /\ Monitor!ProcessToDeviceEvent(todevice_event)
      /\ UNCHANGED<<datachannel, offer>>
   \/ /\ Offer!ProcessToDeviceEvent(todevice_event)
      /\ UNCHANGED<<datachannel, monitor>>

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
   [ offer |-> Offer!State,
     monitor |-> Monitor!State ]

(* An invariant that a Device is always able to receive input *)
(* Defined here as it's rather closely related to spec *)
NeverBlocks ==
   HSToDevice(Id)!Busy =>
      \/ ENABLED(Login2)
      \/ ENABLED(ReceiveSync)

Next ==
   \/ Login1
   \/ Login2
   \/ Sync
   \/ Offer!Next
   \/ Monitor!Next
   \/ ReceiveSync

Liveness ==
   /\ WF_<<device_vars, hs_to_device, device_to_hs>>(Next)
================================================================================
