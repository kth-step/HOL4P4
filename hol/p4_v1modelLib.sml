structure p4_v1modelLib :> p4_v1modelLib = struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

open listSyntax numSyntax;

open p4Syntax p4_coreLib;

open p4Theory p4_coreTheory p4_v1modelTheory;

val v1model_arch_ty = ``:v1model_ascope``;

(* Architectural constants *)
(* TODO: Nothing other than enumeration types? *)
val v1model_init_global_scope = ``[]:scope``;

val v1model_init_ext_obj_map = “[]:(num, v1model_sum_v_ext) alist”;

val v1model_init_counter = rhs $ concl $ EVAL “LENGTH ^v1model_init_ext_obj_map”;

val v1model_init_v_map = ``^core_init_v_map:(string, v) alist``;

(*******************************************)
(* Architectural context (generic externs) *)

val v1model_objectless_map =
 ``[("mark_to_drop", ([("standard_metadata", d_inout)], v1model_mark_to_drop));
    ("verify", ([("condition", d_in); ("err", d_in)], v1model_verify));
    ("verify_checksum", ([("condition", d_in); ("data", d_in); ("checksum", d_in); ("algo", d_none)], v1model_verify_checksum));
    ("update_checksum", ([("condition", d_in); ("data", d_in); ("checksum", d_inout); ("algo", d_none)], v1model_update_checksum))]``;

val v1model_packet_in_map =
 ``[("extract", ([("this", d_in); ("headerLvalue", d_out)], v1model_packet_in_extract));
    ("lookahead", ([("this", d_in); ("targ1", d_in)], v1model_packet_in_lookahead));
    ("advance", ([("this", d_in); ("bits", d_in)], v1model_packet_in_advance))]``;

val v1model_packet_out_map =
 ``[("emit", ([("this", d_in); ("data", d_in)], v1model_packet_out_emit))]``;

(*************************)
(* Architectural context *)

(* Input function term *)
val v1model_input_f = ``v1model_input_f``;

(* Output function term *)
val v1model_output_f = ``v1model_output_f``;

(* Programmable block input function term *)
val v1model_copyin_pbl = ``v1model_copyin_pbl``;

(* Programmable block output function term *)
val v1model_copyout_pbl = ``v1model_copyout_pbl``;

(* Programmable block output function term *)
val v1model_apply_table_f = ``v1model_apply_table_f``;

(* Fixed-function block map *)
val v1model_ffblock_map = ``[("postparser", ffblock_ff v1model_postparser)]``;

val v1model_register_map =
 ``[("read", ([("this", d_in); ("result", d_out); ("index", d_in)], register_read));
    ("write", ([("this", d_in); ("index", d_in); ("value", d_in)], register_write))]``;

(* Extern (object) function map *)
val v1model_ext_map =
 ``((^(inst [``:'a`` |-> ``:v1model_ascope``] core_ext_map))
    ++ [("", (NONE, (^v1model_objectless_map)));
        ("packet_in", (NONE, (^v1model_packet_in_map)));
        ("packet_out", (NONE, (^v1model_packet_out_map)));
        ("register", SOME ([("this", d_out); ("size", d_none); ("targ1", d_in)], register_construct), (^v1model_register_map))])``;

(* Function map *)
val v1model_func_map = core_func_map;

end
