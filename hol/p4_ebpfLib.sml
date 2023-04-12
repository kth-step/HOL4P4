structure p4_ebpfLib :> p4_ebpfLib = struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

open listSyntax;

open p4Syntax p4_coreLib;

open p4Theory p4_coreTheory p4_ebpfTheory;

val ebpf_arch_ty = ``:ebpf_ascope``;

val ebpf_init_global_scope =
 ``[]:scope``;

(*******************************************)
(* Architectural context (generic externs) *)

val ebpf_packet_in_map =
 ``[("extract", ([("this", d_in); ("hdr", d_out)], ebpf_packet_in_extract))]``;

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

val ebpf_ext_map =
 ``((^(inst [``:'a`` |-> ``:ebpf_ascope``] core_ext_map))
    ++ [("packet_in", (NONE, (^ebpf_packet_in_map)));
        ("packet_out", (NONE, (^ebpf_packet_out_map)))])``;

val ebpf_func_map = core_func_map;

end
