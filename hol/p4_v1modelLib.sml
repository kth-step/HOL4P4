structure p4_v1modelLib :> p4_v1modelLib = struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

open listSyntax numSyntax;

open p4Syntax p4_coreLib;

open p4Theory p4_coreTheory p4_v1modelTheory;

val v1model_arch_ty = ``:v1model_ascope``;

(* Architectural constants *)
(* TODO: Nothing other than enumeration types? *)
val v1model_init_global_scope = ``[]:scope``;

(*******************************************)
(* Architectural context (generic externs) *)

val v1model_packet_in_map =
 ``[("extract", (stmt_ext, [("this", d_in); ("headerLvalue", d_out)], v1model_packet_in_extract))]``;

val v1model_packet_out_map =
 ``[("emit", (stmt_ext, [("this", d_in); ("data", d_in)], v1model_packet_out_emit))]``;

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
val v1model_ffblock_map = ``[("parser_runtime", ffblock_ff v1model_parser_runtime)]``;

(* Extern (object) function map *)
val v1model_ext_map =
 ``((^(inst [``:'a`` |-> ``:v1model_ascope``] core_ext_map))
    ++ [("packet_in", (NONE, (^v1model_packet_in_map)));
        ("packet_out", (NONE, (^v1model_packet_out_map)))])``;

(* Function map *)
val v1model_func_map = core_func_map;

(***********************)
(* Architectural state *)

val v1model_init_counter = term_of_int 2;

val v1model_init_ext_obj_map = ``[(0, INL (core_v_ext_packet_in []));
			          (1, INL (core_v_ext_packet_out []))]:(num, v_ext) alist``;

val v1model_standard_metadata_uninit =
 mk_v_struct_list [(``"ingress_port"``, mk_v_biti_arb 9),
                   (``"egress_spec"``, mk_v_biti_arb 9),
                   (``"egress_port"``, mk_v_biti_arb 9),
                   (``"instance_type"``, mk_v_biti_arb 32),
                   (``"packet_length"``, mk_v_biti_arb 32),
                   (``"enq_timestamp"``, mk_v_biti_arb 32),
                   (``"enq_qdepth"``, mk_v_biti_arb 19),
                   (``"deq_timedelta"``, mk_v_biti_arb 32),
                   (``"deq_qdepth"``, mk_v_biti_arb 19),
                   (``"ingress_global_timestamp"``, mk_v_biti_arb 48),
                   (``"egress_global_timestamp"``, mk_v_biti_arb 48),
                   (``"mcast_grp"``, mk_v_biti_arb 16),
                   (``"egress_rid"``, mk_v_biti_arb 16),
                   (``"checksum_error"``, mk_v_biti_arb 1),
                   (``"parser_error"``, ``v_err "NoError"``),
                   (``"priority"``, mk_v_biti_arb 3)];

val v1model_meta_uninit =
 mk_v_struct_list [];

val v1model_init_v_map = ``^core_init_v_map ++
                           [("b_in", v_ext_ref 0);
			    ("b_out", v_ext_ref 1);
			    ("standard_metadata", (^v1model_standard_metadata_uninit));
                            ("meta", (^v1model_meta_uninit))]:(string, v) alist``;

end
