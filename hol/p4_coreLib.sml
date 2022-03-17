structure p4_coreLib :> p4_coreLib = struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

open p4Syntax;

open p4Theory p4_coreTheory;

(* Below are some terms containing stuff that is defined in core.p4. See also p4_coreScript.sml *)

val no_action_fun = ``("NoAction", stmt_empty, []:(string # d) list)``;

val core_func_map = ``FEMPTY |+ (^no_action_fun)``;

end
