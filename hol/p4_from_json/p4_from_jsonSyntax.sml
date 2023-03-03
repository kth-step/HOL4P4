structure p4_from_jsonSyntax :> p4_from_jsonSyntax =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

open stringSyntax optionSyntax pairSyntax listSyntax
     wordsSyntax numSyntax bitstringSyntax;
open p4_from_jsonTheory;

val (SOME_msg_tm, mk_SOME_msg, dest_SOME_msg, is_SOME_msg) =
  syntax_fns1 "p4_from_json" "SOME_msg";

val (NONE_msg_tm, mk_NONE_msg, dest_NONE_msg, is_NONE_msg) =
  syntax_fns1 "p4_from_json" "NONE_msg";

end
