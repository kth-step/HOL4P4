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

val ebpf_packet_in_map =
 ``[("extract", ([("this", d_in); ("headerLvalue", d_out)], ebpf_packet_in_extract))]``;

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

(***********************)
(* Architectural state *)

val ebpf_init_counter = term_of_int 2;

val ebpf_init_ext_obj_map = ``[(0, INL (core_v_ext_packet []));
                               (1, INL (core_v_ext_packet []))]:(num, ebpf_sum_v_ext) alist``;

(*
val ipv4_header_uninit =
 mk_v_header_list F 
                  [(``"version"``, mk_v_biti_arb 4),
                   (``"ihl"``, mk_v_biti_arb 4),
                   (``"diffserv"``, mk_v_biti_arb 8),
                   (``"totalLen"``, mk_v_biti_arb 16),
                   (``"identification"``, mk_v_biti_arb 16),
                   (``"flags"``, mk_v_biti_arb 3),
                   (``"fragOffset"``, mk_v_biti_arb 13),
                   (``"ttl"``, mk_v_biti_arb 8),
                   (``"protocol"``, mk_v_biti_arb 8),
                   (``"hdrChecksum"``, mk_v_biti_arb 16),
                   (``"srcAddr"``, mk_v_biti_arb 32),
                   (``"dstAddr"``, mk_v_biti_arb 32)];
val ethernet_header_uninit =
 mk_v_header_list F
                  [(``"dstAddr"``, mk_v_biti_arb 48),
                   (``"srcAddr"``, mk_v_biti_arb 48),
                   (``"etherType"``, mk_v_biti_arb 16)];
val ebpf_parsed_packet_struct_uninit =
 mk_v_struct_list [(``"ethernet"``, ethernet_header_uninit), (``"ipv4"``, ipv4_header_uninit)];
*)

val ebpf_init_v_map = ``^core_init_v_map ++
                        [("packet", v_ext_ref 0);
			 ("packet_copy", v_ext_ref 1);
			 ("accept", v_bool ARB)]:(string, v) alist``;

end
