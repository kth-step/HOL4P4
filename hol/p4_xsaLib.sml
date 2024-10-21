structure p4_xsaLib :> p4_xsaLib = struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

open listSyntax numSyntax pairSyntax;

open p4Syntax p4_coreLib;

open p4Theory p4_coreTheory p4_xsaTheory;

val xsa_arch_ty = ``:xsa_ascope``;

(* Architectural constants *)
(* TODO: Nothing other than enumeration types? *)
val xsa_init_global_scope = ``[]:scope``;

val xsa_init_ext_obj_map = “[]:(num, xsa_sum_v_ext) alist”;

val xsa_init_counter = rhs $ concl $ EVAL “LENGTH ^xsa_init_ext_obj_map”;

val xsa_init_v_map = ``^core_init_v_map:(string, v) alist``;

(*******************************************)
(* Architectural context (generic externs) *)

val xsa_objectless_map =
 ``[("mark_to_drop", ([("standard_metadata", d_inout)], xsa_mark_to_drop));
    ("verify", ([("condition", d_in); ("err", d_in)], xsa_verify))]``;

val xsa_packet_in_map =
 ``[("extract", ([("this", d_in); ("headerLvalue", d_out)], xsa_packet_in_extract));
    ("lookahead", ([("this", d_in); ("targ1", d_in)], xsa_packet_in_lookahead));
    ("advance", ([("this", d_in); ("bits", d_in)], xsa_packet_in_advance))]``;

val xsa_packet_out_map =
 ``[("emit", ([("this", d_in); ("data", d_in)], xsa_packet_out_emit))]``;

(*************************)
(* Architectural context *)

(* Input function term *)
val xsa_input_f = ``xsa_input_f``;

(* Output function term *)
val xsa_output_f = ``xsa_output_f``;
val xsa_is_drop_port = ``xsa_is_drop_port``;

(* Programmable block input function term *)
val xsa_copyin_pbl = ``xsa_copyin_pbl``;

(* Programmable block output function term *)
val xsa_copyout_pbl = ``xsa_copyout_pbl``;

(* Programmable block output function term *)
val xsa_apply_table_f = ``xsa_apply_table_f``;

(* Fixed-function block map *)
val xsa_ffblock_map = ``[("postparser", ffblock_ff xsa_postparser)]``;

(* Extern (object) function map *)
val xsa_ext_map =
 ``((^(inst [``:'a`` |-> xsa_arch_ty] core_ext_map))
    ++ [("", (NONE, (^xsa_objectless_map)));
        ("packet_in", (NONE, (^xsa_packet_in_map)));
        ("packet_out", (NONE, (^xsa_packet_out_map)))])``;

(* Function map *)
val xsa_func_map = core_func_map;

(*****************)
(* Miscellaneous *)

fun dest_xsa_ascope xsa_ascope =
 let
  val (ext_counter, xsa_ascope') = dest_pair xsa_ascope
  val (ext_obj_map, xsa_ascope'') = dest_pair xsa_ascope'
  val (v_map, ctrl) = dest_pair xsa_ascope''
 in
  (ext_counter, ext_obj_map, v_map, ctrl)
 end
;

end
