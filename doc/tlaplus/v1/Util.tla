---- MODULE Util ---------------------------------------------------------------
(* Utility functions *)
--------------------------------------------------------------------------------
LOCAL INSTANCE TLC
LOCAL INSTANCE Naturals

(* Easy way to replace PrintT with a silent action *)
NoPrint(ignore, x) == x

(* Assert that value conforms to specification S (e.g. message follows protocol) *)
Conforms(S, value) ==
  Assert(value \in S, <<"Value", value, "did not satisfy", S>>)

(* Assert that value conforms to specification S (e.g. message follows protocol)
   with custom error message *)
ConformsMsg(msg, S, value) ==
  Assert(value \in S, <<msg, "Value", value, "did not satisfy", S>>)

(* Wrapper for Conforms that can be used in an expression, as it returns the original value *)
Check(S, value) ==
  IF Conforms(S, value)
  THEN value
  ELSE Assert(FALSE, "Impossible")

(* Wrapper for ConformsMsg that can be used in an expression, as it returns the original value *)
CheckMsg(msg, S, value) ==
  IF ConformsMsg(msg, S, value)
  THEN value
  ELSE Assert(FALSE, "Impossible")

(* Easy way to disable a Check *)
NoCheck(S, value) ==
  value

(* Variant of Check that produces less diagnostics (it doesn't output the original spec S) *)
QuieterCheck(S, value) ==
  IF Assert(value \in S, <<"Value", value, "did not satisfy criteria">>)
  THEN value
  ELSE Any

(* Checks that the parameter provided is true; useful in TypeOK *)
CheckTRUE(msg, value) ==
  IF Assert(value, msg)
  THEN value
  ELSE Any

(* Produce the set of sequences of S of at most length elements *)
(* Use e.g. SeqsOfLength(BOOLEAN, (0..2)) *)
SeqsOfLength(S, Lens) ==
  UNION {[1..n -> S] : n \in Lens}

(* Easy way to dump a value while debugging *)
Trace(x) ==
  IF Print(x, TRUE) THEN x ELSE Assert(FALSE, "aiee")

================================================================================
