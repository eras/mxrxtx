---- MODULE MC -----------------------------------------------------------------
EXTENDS Model
--------------------------------------------------------------------------------
LOCAL INSTANCE Util
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
LOCAL INSTANCE FiniteSets

Protocol == INSTANCE Protocol

MCInit ==
   /\ device = [ device_id \in DeviceId |->
                 Check(Device(device_id)!Type,
                       Device(device_id)!InitValue) ]

MCSpec == MCInit /\ Init /\ [][Next]_all_vars /\ Liveness

(* Eventually all offering nodes will be offering, if there is nothing else the state machine can do *)
EventuallyOffer ==
   \A device_id \in CanOffer: <>[](~ENABLED(Next) => device[device_id].offering)

(* Has an offer message been sent to the server? *)
AnOfferIsMade ==
   \E device_id \in CanOffer: device_to_hs[device_id] \in Protocol!RoomMessage

EventuallyAnOfferIsMade ==
   <>AnOfferIsMade

(* Eventually all monitoring nodes have an offer, if there is nothing else the state machine can do *)
EventuallyMonitorHasOffer ==
   \A device_id \in CanMonitor: <>(AnOfferIsMade ~> <>[](~ENABLED(Next) => monitor[device_id].offer # <<>>))

(* Eventually it will always be the case that if there is no next state, all channels will be empty *)
EventuallyChannelsAreEmpty ==
   /\ \A device_id \in DeviceId:
         <>[](~ENABLED(Next) =>
              /\ ~HSToDevice(device_id)!Busy
              /\ ~DeviceToHS(device_id)!Busy)
   /\ \A data_channel_id \in DataChannelId:
         <>[](~ENABLED(Next) =>
              datachannel[data_channel_id] = <<>>)

(* Used as a negative property for getting traces *)
EventuallyChannelsAreNotEmpty == ~EventuallyChannelsAreEmpty

(* Eventually it is the case that offers offers will be complete, if the offer has been sent
   and all monitors are syncing starting from the first message of the room *)
EventuallyAllOffersComplete ==
   \A device_id_ofr \in CanOffer:
      <>[](
         /\ offer[device_id_ofr].state = "sent-mxrxtx-offer"
         /\ <>(\* Consider only the case where monitors are able to see the first message
               \A device_id_mon \in CanMonitor:
               device[device_id_mon].token.room = 1 ~>
                  \E session_id \in SessionId:
                  offer[device_id_ofr].session[session_id].state = "complete")
      )

(* Every client synced the first message of the room *)
SyncsStartFromBeginning ==
   \A device_id \in DeviceId: <>(device[device_id].token.room = 1)

(* If every client is syncing from the beginning, then all monitors in the end (on deadlock) will be in "complete" state *)
EventuallyAllMonitorsHaveDownloaded ==
   <> /\ AnOfferIsMade
      /\ \A device_id \in CanMonitor:
         device[device_id].token.room = 1 ~> (monitor[device_id].state = "complete")

(* If every client is syncing from the beginning, then some monitors in the end (on deadlock) will not be in "complete" state *)
(* Not sure if this works.. *)
EventuallyAllMonitorsHaveNotDownloaded ==
   SyncsStartFromBeginning => \E device_id \in CanMonitor: <>(AnOfferIsMade ~> (ENABLED(Next) \/ ~(monitor[device_id].state = "complete")))

(* Used for getting traces: there will be monitors that will not complete *)
NotAllMonitorsAreComplete ==
   Cardinality({device_id \in CanMonitor: monitor[device_id].state = "complete"}) < Cardinality(CanMonitor)

(* For each monitor that is complete the offer with the same peer_device_id has the same content (in its data
   portion of the checksum) *)
DownloadedFilesAreCorrect ==
   \A monitor_id \in CanMonitor:
      /\ monitor[monitor_id].state = "complete" =>
         \E offer_id \in CanOffer:
            /\ offer_id = monitor[monitor_id].peer_device_id
            /\ monitor[monitor_id].received =
                  [index \in DOMAIN(offer[offer_id].offer) |->
                   offer[offer_id].offer[index].checksum[2]]

(* These imply we don't need buffered channels for this model, as reading MChannel never blocks *)
HSNeverBlocks == HS!NeverBlocks
DeviceNeverBlocks == \A device_id \in DeviceId: Device(device_id)!NeverBlocks

================================================================================
