structure p4_coreLib :> p4_coreLib = struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

open p4Syntax;

open p4Theory p4_coreTheory;

(* Below are some terms containing stuff that is defined in core.p4. See also p4_coreScript.sml *)
(* TODO: Update this *)

val no_action_fun = ``("NoAction", stmt_ret (e_v v_bot), []:(string # d) list)``;

val core_func_map = ``(FEMPTY |+ (^no_action_fun)):func_map``;

val core_header_map =
 ``(FEMPTY
    |+ ("isValid", (stmt_seq stmt_ext (stmt_ret (e_var varn_ext_ret)), [("this", d_in)], (header_is_valid:'a ext_fun)))):'a ext_fun_map``;

val core_packet_in_map =
 ``(FEMPTY |+ ("extract", (stmt_seq stmt_ext (stmt_ret (e_v v_bot)), [("this", d_in); ("hdr", d_out)], packet_in_extract))):'a ext_fun_map``;

val core_packet_out_map =
 ``(FEMPTY |+ ("emit", (stmt_seq stmt_ext (stmt_ret (e_v v_bot)), [("this", d_in); ("data", d_in)], packet_out_emit))):'a ext_fun_map``;

val core_ext_map =
 ``(FEMPTY |+ ("header", (NONE, (^core_header_map)))
           |+ ("packet_in", (NONE, (^core_packet_in_map)))
           |+ ("packet_out", (NONE, (^core_packet_out_map)))):'a ext_map``;

end
