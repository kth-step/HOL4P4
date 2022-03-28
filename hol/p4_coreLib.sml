structure p4_coreLib :> p4_coreLib = struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

open p4Syntax;

open p4Theory p4_coreTheory;

(* Below are some terms containing stuff that is defined in core.p4. See also p4_coreScript.sml *)

val no_action_fun = ``("NoAction", stmt_empty, []:(string # d) list)``;

val core_func_map = ``FEMPTY |+ (^no_action_fun)``;

val core_header_map =
 ``(FEMPTY
    |+ ("isValid", (stmt_seq (stmt_ext header_is_valid) (stmt_ret (e_var varn_ext_ret)), [("this", d_inout)]))):ext_fun_map``;

val core_packet_in_map =
 ``(FEMPTY |+ ("extract", (stmt_ext packet_in_extract, [("this", d_inout); ("hdr", d_out)]))):ext_fun_map``;

val core_packet_out_map =
 ``(FEMPTY |+ ("emit", (stmt_ext packet_out_emit, [("this", d_inout); ("data", d_in)]))):ext_fun_map``;

val core_ext_map =
 ``(FEMPTY |+ ("header", (NONE, (^core_header_map)))
           |+ ("packet_in", (NONE, (^core_packet_in_map)))
           |+ ("packet_out", (NONE, (^core_packet_out_map)))):ext_map``;

end
