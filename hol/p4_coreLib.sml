structure p4_coreLib :> p4_coreLib = struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

open p4Syntax;

open p4Theory p4_coreTheory;

(* Below are some terms containing stuff that is defined in core.p4. See also p4_coreScript.sml *)

val no_action_fun = ``("NoAction", stmt_empty, []:(string # d) list)``;

val core_func_map = ``FEMPTY |+ (^no_action_fun)``;

val core_ext_map = ``FEMPTY |+ ("extract", (extract, [("this", d_inout); ("hdr", d_out)]))
                            |+ ("isValid", (is_valid, [("this", d_inout)]))
                            |+ ("emit", (emit, [("this", d_inout); ("data", d_in)]))``;

end
