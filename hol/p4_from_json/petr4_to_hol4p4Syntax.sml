structure petr4_to_hol4p4Syntax :> petr4_to_hol4p4Syntax =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

open stringSyntax optionSyntax pairSyntax listSyntax
     wordsSyntax numSyntax bitstringSyntax;
open petr4_to_hol4p4Theory;

val (SOME_msg_tm, mk_SOME_msg, dest_SOME_msg, is_SOME_msg) =
  syntax_fns1 "petr4_to_hol4p4" "SOME_msg";

val (NONE_msg_tm, mk_NONE_msg, dest_NONE_msg, is_NONE_msg) =
  syntax_fns1 "petr4_to_hol4p4" "NONE_msg";

end
