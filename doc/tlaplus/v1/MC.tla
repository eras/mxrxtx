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

EventuallyChannelsAreEmpty ==
   /\ \A device_id \in DeviceId:
         <>[](~ENABLED(Next) =>
              /\ ~HSToDevice(device_id)!Busy
              /\ ~DeviceToHS(device_id)!Busy)
   /\ \A data_channel_id \in DataChannelId:
         <>[](~ENABLED(Next) =>
              datachannel[data_channel_id] = <<>>)

EventuallyChannelsAreNotEmpty == ~EventuallyChannelsAreEmpty

(* Every client synced the first message of the room *)
SyncsStartFromBeginning ==
   \A device_id \in DeviceId: <>(device[device_id].token.room = 1)

(* If every client is syncing from the beginning, then all monitors in the end (on deadlock) will be in "complete" state *)
EventuallyAllMonitorsHaveDownloaded ==
   <> /\ AnOfferIsMade
      /\ \A device_id \in CanMonitor:
         device[device_id].token.room = 1 ~> (monitor[device_id].state = "complete")

(* If every client is syncing from the beginning, then some monitors in the end (on deadlock) will not be in "complete" state *)
(* Not sure if this works *)
EventuallyAllMonitorHaveNotDownloaded ==
   SyncsStartFromBeginning => \E device_id \in CanMonitor: <>(AnOfferIsMade ~> (ENABLED(Next) \/ ~(monitor[device_id].state = "complete")))

NotAllMonitorsAreComplete ==
   Cardinality({device_id \in CanMonitor: monitor[device_id].state = "complete"}) < Cardinality(CanMonitor)

OfferHasUploadedDownloads ==
   \A device_id \in CanOffer: <>[](monitor[device_id].state = "complete" => offer[device_id].state = "complete")

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
