structure p4_coreLib :> p4_coreLib = struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

open p4Syntax;

open p4Theory p4_coreTheory;

(* Below are some terms containing stuff that is defined in core.p4.
 * See also p4_coreScript.sml, which contains the HOL4 functions
 * implementing the semantics ofthe externs *)

val no_action_fun = ``("NoAction", stmt_ret (e_v v_bot), []:(string # d) list)``;

val core_func_map = ``[(^no_action_fun)]:func_map``;

(* TODO: Should isValid be an expression instead? *)
val core_header_map =
 ``[("isValid", (stmt_seq stmt_ext (stmt_ret (e_var varn_ext_ret)), [("this", d_in)], (header_is_valid:'a ext_fun)))]:'a ext_fun_map``;

val core_packet_in_map =
 ``[("extract", (stmt_seq stmt_ext (stmt_ret (e_v v_bot)), [("this", d_in); ("hdr", d_out)], packet_in_extract))]:'a ext_fun_map``;

val core_packet_out_map =
 ``[("emit", (stmt_seq stmt_ext (stmt_ret (e_v v_bot)), [("this", d_in); ("data", d_in)], packet_out_emit))]:'a ext_fun_map``;

val core_ext_map =
 ``[("header", (NONE, (^core_header_map)));
    ("packet_in", (NONE, (^core_packet_in_map)));
    ("packet_out", (NONE, (^core_packet_out_map)))]:'a ext_map``;

end
