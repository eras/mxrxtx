---- MODULE Common -------------------------------------------------------------
(* Documentation *)
--------------------------------------------------------------------------------
LOCAL INSTANCE Naturals
LOCAL INSTANCE Util

CONSTANT
   DeviceId
 , MxId
 , NumBaseSyncTokens
 , FileData
 , FileSize

NoSyncToken == [room |-> 0, dm |-> 0]
SyncToken   ==
  UNION {
    {NoSyncToken}
  , [ room     : (1..NumBaseSyncTokens) (* The index of the first non-received room message *)
    , todevice : (1..NumBaseSyncTokens)] (* The index of the first non-received device message *)
  }

(* Checksums are simply <<"CK", <<contents..>>>> *)
Checksum == {"CK"} \X SeqsOfLength(FileData, FileSize)

(* Currently we only have one data channel per a device pair per direction *)
DataChannelLabel == {"data"}

(* Identifiers for datachannels *)
DataChannelId == {<<from, to, label>> \in DeviceId \X DeviceId \X DataChannelLabel: from # to}

================================================================================
