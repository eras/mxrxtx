---- MODULE DataChannels -------------------------------------------------------
EXTENDS Constants
(* Documentation *)
--------------------------------------------------------------------------------
VARIABLES datachannel

DataChannelMessage ==
   UNION {
      [ data: FileData ]        (* from offer->monitor *)
    , [ ack: {TRUE} ]           (* from monitor->offer *)
   }

DataChannel == INSTANCE DataChannel WITH Data <- DataChannelMessage

InitDataChannels == DataChannel!Init

================================================================================
