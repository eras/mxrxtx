---- MODULE MC -----------------------------------------------------------------
EXTENDS Model
--------------------------------------------------------------------------------
LOCAL INSTANCE Util
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences

Protocol == INSTANCE Protocol

MCInit ==
   /\ device = [ device_id \in DeviceId |->
                 Check(Device(device_id)!Type,
                       Device(device_id)!InitValue) ]

MCSpec == MCInit /\ Init /\ [][Next]_all_vars

(* Eventually all offering nodes will be offering, if there is nothing else the state machine can do *)
EventuallyOffer ==
   \A device_id \in CanOffer: <>[](~ENABLED(Next) => device[device_id].offering)

(* Has an offer message been sent to the server? *)
AnOfferIsMade ==
   \E device_id \in CanOffer: device_to_hs[device_id] \in Protocol!RoomMessage

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

EventuallyMonitorHasDownloaded ==
   \A device_id \in CanMonitor: <>(AnOfferIsMade ~> <>[](~ENABLED(Next) => monitor[device_id].state = "complete"))
(* Every client synced the first message of the room *)
SyncsStartFromBeginning ==
   \A device_id \in DeviceId: <>(device[device_id].token.room = 1)

(* If every client is syncing from the beginning, then all monitors in the end (on deadlock) will be in "complete" state *)
EventuallyAllMonitorHaveDownloaded ==
   SyncsStartFromBeginning => \A device_id \in CanMonitor: <>(AnOfferIsMade ~> (ENABLED(Next) \/ <>[](monitor[device_id].state = "complete")))


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
================================================================================
