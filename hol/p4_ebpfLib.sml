structure p4_ebpfLib :> p4_ebpfLib = struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

open listSyntax numSyntax;

open p4Syntax p4_coreLib;

open p4Theory p4_coreTheory p4_ebpfTheory;

val ebpf_arch_ty = ``:ebpf_ascope``;

val ebpf_init_global_scope =
 ``[]:scope``;

(*******************************************)
(* Architectural context (generic externs) *)

val ebpf_objectless_map =
 ``[("verify", ([("condition", d_in); ("err", d_in)], ebpf_verify))]``;

val ebpf_packet_in_map =
 ``[("extract", ([("this", d_in); ("headerLvalue", d_out)], ebpf_packet_in_extract));
    ("lookahead", ([("this", d_in); ("dummy_T", d_in)], ebpf_packet_in_lookahead));
    ("advance", ([("this", d_in); ("bits", d_in)], ebpf_packet_in_advance));]``;

val ebpf_packet_out_map =
 ``[("emit", ([("this", d_in); ("data", d_in)], ebpf_packet_out_emit))]``;

(*************************)
(* Architectural context *)

(* Input function term *)
val ebpf_input_f = ``ebpf_input_f``;

(* Output function term *)
val ebpf_output_f = ``ebpf_output_f``;

(* Programmable block input function term *)
val ebpf_copyin_pbl = ``ebpf_copyin_pbl``;

(* Programmable block output function term *)
val ebpf_copyout_pbl = ``ebpf_copyout_pbl``;

(* Programmable block output function term *)
val ebpf_apply_table_f = ``ebpf_apply_table_f``;

(* Fixed-function block map *)
val ebpf_ffblock_map = ``[]``;

val ebpf_CounterArray_map =
 ``[("increment", ([("this", d_in); ("index", d_in)], CounterArray_increment));
    ("add", ([("this", d_in); ("index", d_in); ("value", d_in)], CounterArray_add))]:ebpf_ascope ext_fun_map``;

val ebpf_ext_map =
 ``((^(inst [``:'a`` |-> ``:ebpf_ascope``] core_ext_map))
    ++ [("", (NONE, ^ebpf_objectless_map));
        ("packet_in", (NONE, (^ebpf_packet_in_map)));
        ("packet_out", (NONE, (^ebpf_packet_out_map)));
        ("CounterArray", SOME ([("this", d_out); ("max_index", d_none); ("sparse", d_none)], CounterArray_construct), (^ebpf_CounterArray_map))])``;

val ebpf_func_map = core_func_map;

(***********************)
(* Architectural state *)

val ebpf_init_counter = term_of_int 2;

val ebpf_init_ext_obj_map = ``[(0, INL (core_v_ext_packet []));
                               (1, INL (core_v_ext_packet []))]:(num, ebpf_sum_v_ext) alist``;

val ebpf_init_v_map = ``^core_init_v_map ++
                        [("packet", v_ext_ref 0);
			 ("packet_copy", v_ext_ref 1);
                         (* accept is an out-directed parameter of the final block, only
                          * read after it is finished.
                          * This can be concretized initially without ambiguity. *)
			 ("accept", v_bool F)]:(string, v) alist``;

end
