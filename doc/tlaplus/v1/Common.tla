---- MODULE Common -------------------------------------------------------------
(* Documentation *)
--------------------------------------------------------------------------------
LOCAL INSTANCE Naturals
LOCAL INSTANCE Util

CONSTANT
   DeviceId
 , MxId
 , NumBaseTokens
 , FileData
 , FileSize

NoToken == [room |-> 0, dm |-> 0]
Token   ==
  UNION {
    {NoToken}
  , [ room     : (1..NumBaseTokens)
    , todevice : (1..NumBaseTokens)]
  }

Checksum == {"CK"} \X SeqsOfLength(FileData, FileSize)

DataChannelLabel == {"data"}

(* Identifiers for datachannels *)
DataChannelId == {<<from, to, label>> \in DeviceId \X DeviceId \X DataChannelLabel: from # to}

================================================================================
