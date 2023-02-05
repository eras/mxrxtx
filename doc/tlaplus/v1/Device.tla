---- MODULE Device -------------------------------------------------------------
EXTENDS Constants
--------------------------------------------------------------------------------
CONSTANT
   Id

VARIABLES
   device
 , hs_to_device
 , device_to_hs
 , monitor
 , offer
 , datachannel

LOCAL INSTANCE Common
LOCAL INSTANCE TLC
LOCAL INSTANCE Util
LOCAL INSTANCE DeviceHSChannels
LOCAL INSTANCE DataChannels
LOCAL INSTANCE Naturals         (* + *)
LOCAL INSTANCE Sequences        (* Append *)
LOCAL INSTANCE SequencesExt     (* FoldSeq *)

Protocol == INSTANCE Protocol

Self == device[Id]

TotalSizeOfOffer(offer_files) == FoldSeq(LAMBDA a, b: a.size + b, 0, offer_files)

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

EstablishSession(unchanged_others) ==
   /\ monitor[Id].state = "has-mxrxtx-offer"
   /\ DeviceToHS(Id)!Send([ message   |-> "ToDevice"
                          , mx_id     |-> monitor[Id].peer_mx_id
                          , device_id |-> 0
                          , contents  |-> [ message   |-> "WebRTC"
                                          , webrtc    |-> "offer"
                                          , device_id |-> Id ]
                          ])
   /\ monitor' = [monitor EXCEPT
                   ![Id].state = "sent-webrtc-offer"
                 ]
   /\ UNCHANGED<<datachannel, offer, device, hs_to_device>>
   /\ unchanged_others

TotalSizeOfReceived ==
   FoldSeq(LAMBDA a, b: Len(a) + b, 0, monitor[Id].received)

DoDownload(unchanged_others) ==
   /\ monitor[Id].state = "downloading"
   /\ TotalSizeOfReceived < TotalSizeOfOffer(monitor[Id].offer)
   /\ \E peer_device_id \in DeviceId:
      \E message \in DataChannelMessage:
      /\ peer_device_id = monitor[Id].peer_device_id
      /\ DataChannel!A(peer_device_id, Id, "data")!Recv(message)
      /\ monitor' = [monitor EXCEPT ![Id].received[CurrentOfferFileIndexOffset(TotalSizeOfReceived, monitor[Id].offer).index] = Append(@, message.data)]
      /\ UNCHANGED<<offer, device, hs_to_device, device_to_hs>>
      /\ unchanged_others

ValidateChecksum ==
   (* TODO *)
   TRUE

DoSendAck(unchanged_others) ==
   /\ monitor[Id].state = "downloading"
   /\ TotalSizeOfReceived = TotalSizeOfOffer(monitor[Id].offer)
   /\ \E peer_device_id \in DeviceId:
      /\ peer_device_id = monitor[Id].peer_device_id
      /\ DataChannel!B(Id, peer_device_id, "data")!Send([ack |-> TRUE])
      /\ monitor' = [monitor EXCEPT ![Id].state = "complete"]
      /\ Assert(ValidateChecksum, "Checksum validation failed")
      /\ UNCHANGED<<offer, device, hs_to_device, device_to_hs>>
      /\ unchanged_others

ProcessToDeviceEvent(event) ==
   /\ monitor[Id].state = "sent-webrtc-offer"
   /\ Assert(event.sender = monitor[Id].peer_mx_id, "Peer mx id is unexpected")
   /\ monitor' = [monitor EXCEPT
                   ![Id].state = "downloading"
                 , ![Id].peer_device_id = event.contents.device_id
                 ]
   /\ UNCHANGED<<datachannel, device_to_hs>>

InitValue ==
   [ offer          |-> <<>>
   , peer_mx_id     |-> 0
   , peer_device_id |-> 0
   , received       |-> <<>>
   , state          |-> IF Id \in CanMonitor THEN "wait-mxrxtx-offer" ELSE "disabled"
   ]

Init ==
   /\ monitor[Id] = InitValue

Next(unchanged_others) ==
   \/ EstablishSession(unchanged_others)
   \/ DoDownload(unchanged_others)
   \/ DoSendAck(unchanged_others)

================================================================================

---- MODULE Offer --------------------------------------------------------------
--------------------------------------------------------------------------------
Offer ==
   [ peer_mx_id     : {0} \cup MxId
   , peer_device_id : {0} \cup DeviceId
   , sent           : Nat
   , offer          : Protocol!OfferFiles
   , state          : { "disabled"
                      , "send-mxrxtx-offer"
                      , "sent-mxrxtx-offer"
                      , "uploading"
                      , "complete"
                      }
   ]

TypeOK ==
   /\ CheckTRUE("offer", offer[Id] \in Offer)

DoOffer(unchanged_others) ==
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
      /\ device' = [device EXCEPT ![Id] = [@ EXCEPT !.offering = TRUE]]
      /\ offer' = [offer EXCEPT ![Id].state = "sent-mxrxtx-offer"]
      /\ UNCHANGED<<datachannel, monitor, hs_to_device>>
      /\ unchanged_others

TotalSizeOfSent == offer[Id].sent

DoUpload(unchanged_others) ==
   /\ offer[Id].state = "uploading"
   /\ TotalSizeOfSent < TotalSizeOfOffer(offer[Id].offer)
   /\ \E peer_device_id \in DeviceId:
      /\ peer_device_id = offer[Id].peer_device_id
      /\ LET index_offset == CurrentOfferFileIndexOffset(TotalSizeOfSent, offer[Id].offer) IN
         /\ DataChannel!A(Id, peer_device_id, "data")!Send([data |-> offer[Id].offer[index_offset.index].checksum[2][index_offset.offset + 1]])
         /\ offer' = [offer EXCEPT ![Id].state = "uploading"
                                 , ![Id].sent = @ + 1]
         /\ UNCHANGED<<monitor, device, hs_to_device, device_to_hs>>
         /\ unchanged_others

DoWaitAck(unchanged_others) ==
   /\ offer[Id].state = "uploading"
   /\ TotalSizeOfSent = TotalSizeOfOffer(offer[Id].offer)
   /\ \E peer_device_id \in DeviceId:
      /\ peer_device_id = offer[Id].peer_device_id
      /\ DataChannel!B(peer_device_id, Id, "data")!Recv([ack |-> TRUE])
      /\ offer' = [offer EXCEPT ![Id].state = "complete"]
      /\ UNCHANGED<<monitor, device, hs_to_device, device_to_hs>>
      /\ unchanged_others

ProcessToDeviceEvent(event) ==
   /\ offer[Id].state = "sent-mxrxtx-offer"
   /\ DeviceToHS(Id)!Send([ message   |-> "ToDevice"
                          , mx_id     |-> event.sender
                          , device_id |-> event.contents.device_id
                          , contents  |-> [ message   |-> "WebRTC"
                                          , webrtc    |-> "answer"
                                          , device_id |-> Id ]
                          ])
   /\ offer' = [offer EXCEPT
                  ![Id].state = "uploading"
                , ![Id].peer_mx_id = event.sender
                , ![Id].peer_device_id = event.contents.device_id
                ]

InitValue ==
   [ peer_mx_id     |-> 0
   , peer_device_id |-> 0
   , offer          |-> << Protocol!MakeOfferFile("a", <<0>>)
                         (* , Protocol!MakeOfferFile("b", <<>>) *)
                         , Protocol!MakeOfferFile("c", <<1, 0>>)
                         >>
   , sent           |-> 0
   , state          |-> IF Id \in CanOffer THEN "send-mxrxtx-offer" ELSE "disabled"
   ]

Init ==
   /\ offer[Id] = InitValue

Next(unchanged_others) ==
   \/ DoOffer(unchanged_others)
   \/ DoUpload(unchanged_others)
   \/ DoWaitAck(unchanged_others)

================================================================================

Monitor == INSTANCE Monitor
Offer == INSTANCE Offer

LoginState == { "no", "inprogress", "yes" }

Type ==
   [logged_in : LoginState,
    syncing   : BOOLEAN,
    offering  : BOOLEAN,
    token     : Token]

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
    token     |-> NoToken]

Login1(unchanged_others) ==
   /\ Self.logged_in = "no"
   /\ DeviceToHS(Id)!Send([message |-> "Login",
                           contents |-> [ mx_id |-> Id ]]) (* TODO: simple device_id <=> mx_id mapping *)
   /\ device' = [device EXCEPT ![Id] = [@ EXCEPT !.logged_in = "inprogress"]]
   /\ UNCHANGED<<datachannel, offer, monitor, hs_to_device>>
   /\ unchanged_others

Login2(unchanged_others) ==
   LET response == HSToDevice(Id)!Get IN
   /\ Self.logged_in = "inprogress"
   /\ HSToDevice(Id)!Discard
   /\ response.message = "LoginOK"
   /\ device' = [device EXCEPT ![Id] = [@ EXCEPT !.logged_in = "yes", !.token = response.token]]
   /\ UNCHANGED<<datachannel, offer, monitor, device_to_hs>>
   /\ unchanged_others

Sync(unchanged_others) ==
   /\ Self.logged_in = "yes"
   /\ ~Self.syncing
   /\ DeviceToHS(Id)!Send([message |-> "Sync",
                           contents |-> Self.token])
   /\ device' = [device EXCEPT ![Id] = [@ EXCEPT !.syncing = TRUE]]
   /\ UNCHANGED<<datachannel, offer, monitor, hs_to_device>>
   /\ unchanged_others

ProcessRoomEvent(room_event) ==
   /\ Monitor!ProcessRoomEvent(room_event)
   /\ UNCHANGED<<datachannel, offer>>

ProcessToDeviceEvent(todevice_event) ==
   \/ /\ Monitor!ProcessToDeviceEvent(todevice_event)
      /\ UNCHANGED<<datachannel, offer>>
   \/ /\ Offer!ProcessToDeviceEvent(todevice_event)
      /\ UNCHANGED<<datachannel, monitor>>

ReceiveSync(unchanged_others) ==
   /\ Self.logged_in = "yes"
   /\ Self.syncing
   /\ LET event == HSToDevice(Id)!Get IN
      /\ HSToDevice(Id)!Discard
      /\ IF event \in Protocol!RoomEvent THEN
            /\ device' = [device EXCEPT ![Id] = [@ EXCEPT !.syncing = FALSE,
                                                          !.token = event.token]]
            /\ ProcessRoomEvent(event)
         ELSE
            /\ device' = [device EXCEPT ![Id] = [@ EXCEPT !.syncing = FALSE,
                                                          !.token = event.token]]
            /\ ProcessToDeviceEvent(event)
      /\ unchanged_others

Next(unchanged_others) ==
   \/ Login1(unchanged_others)
   \/ Login2(unchanged_others)
   \/ Sync(unchanged_others)
   \/ Offer!Next(unchanged_others)
   \/ Monitor!Next(unchanged_others)
   \/ ReceiveSync(unchanged_others)
================================================================================
