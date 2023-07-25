structure p4_coreLib :> p4_coreLib = struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

open p4Syntax;

open p4Theory p4_coreTheory;

(* Below are some terms containing stuff that is defined in core.p4.
 * See also p4_coreScript.sml, which contains the HOL4 functions
 * implementing the semantics of the externs *)

val no_action_fun = ``("NoAction", stmt_ret (e_v v_bot), []:(string # d) list)``;

val core_func_map = ``[(^no_action_fun)]:func_map``;

(* TODO: Should isValid be an expression instead? *)
val core_header_map =
 ``[("isValid", ([("this", d_in)], (header_is_valid:'a ext_fun)));
    ("setValid", ([("this", d_inout)], (header_set_valid:'a ext_fun)));
    ("setInvalid", ([("this", d_inout)], (header_set_invalid:'a ext_fun)))]:'a ext_fun_map``;

(* Note: packet_in and packet_out extern function maps are found in specific architecture files *)

val core_ext_map =
 ``[("header", (NONE, (^core_header_map)))]:'a ext_map``;

(* parseError is needed for all architectures.
 * In the architecture-specific files, all parameters of programmable blocks
 * should be added to this, as well as any architecture-specific variables. *)
val core_init_v_map = ``[("parseError", v_err "NoError")]:(string, v) alist``;

end
