structure p4_vssLib :> p4_vssLib = struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

open listSyntax numSyntax;

open p4Syntax p4_coreLib;

open p4Theory p4_coreTheory p4_vssTheory;

val vss_arch_ty = ``:vss_ascope``;

(* Architectural constants *)
val REAL_PORT_COUNT_tm = mk_v_bitii (8, 4);

val RECIRCULATE_IN_PORT_tm = mk_v_bitii (13, 4);
val CPU_IN_PORT_tm = mk_v_bitii (14, 4);

val DROP_PORT_tm = mk_v_bitii (15, 4);
val CPU_OUT_PORT_tm = mk_v_bitii (14, 4);
val RECIRCULATE_OUT_PORT_tm = mk_v_bitii (13, 4);

val vss_init_global_scope =
 ``[(varn_name "REAL_PORT_COUNT", (^REAL_PORT_COUNT_tm, NONE) );
    (varn_name "RECIRCULATE_IN_PORT", (^RECIRCULATE_IN_PORT_tm, NONE) );
    (varn_name "CPU_IN_PORT", (^CPU_IN_PORT_tm, NONE) );
    (varn_name "DROP_PORT", (^DROP_PORT_tm, NONE) );
    (varn_name "CPU_OUT_PORT", (^CPU_OUT_PORT_tm, NONE) );
    (varn_name "RECIRCULATE_OUT_PORT", (^RECIRCULATE_OUT_PORT_tm, NONE) )
   ]:scope``;

(*******************************************)
(* Architectural context (generic externs) *)

val vss_packet_in_map =
 ``[("extract", ([("this", d_in); ("headerLvalue", d_out)], vss_packet_in_extract))]:vss_ascope ext_fun_map``;

val vss_packet_out_map =
 ``[("emit", ([("this", d_in); ("data", d_in)], vss_packet_out_emit))]:vss_ascope ext_fun_map``;

(*************************)
(* Architectural context *)

(* Input function term *)
val vss_input_f = ``vss_input_f``;

(* Output function term *)
val vss_output_f = ``vss_output_f``;

(* Programmable block input function term *)
val vss_copyin_pbl = ``vss_copyin_pbl``;

(* Programmable block output function term *)
val vss_copyout_pbl = ``vss_copyout_pbl``;

(* Programmable block output function term *)
val vss_apply_table_f = ``vss_apply_table_f``;

(* Fixed-function block map *)
val vss_ffblock_map = ``[("parser_runtime", ffblock_ff vss_parser_runtime);
                         ("pre_deparser", ffblock_ff vss_pre_deparser)]:vss_ascope ffblock_map``;

val vss_Checksum16_map =
 ``[("clear", ([("this", d_in)], Checksum16_clear));
    ("update", ([("this", d_in); ("data", d_in)], Checksum16_update));
    ("get", ([("this", d_in)], Checksum16_get))]:vss_ascope ext_fun_map``;

val vss_ext_map =
 ``((^(inst [``:'a`` |-> ``:vss_ascope``] core_ext_map))
    ++ [("packet_in", (NONE, (^vss_packet_in_map)));
        ("packet_out", (NONE, (^vss_packet_out_map)));
("Checksum16", SOME ([("this", d_out)], Checksum16_construct), (^vss_Checksum16_map))]):vss_ascope ext_map``;

val vss_func_map = core_func_map;

(***********************)
(* Architectural state *)

val vss_init_counter = term_of_int 3;

val vss_init_ext_obj_map = ``[(0, INL (core_v_ext_packet []));
			      (1, INL (core_v_ext_packet []));
			      (2, INL (core_v_ext_packet []))]:(num, vss_sum_v_ext) alist``;
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
val vss_parsed_packet_struct_uninit =
 mk_v_struct_list [(``"ethernet"``, ethernet_header_uninit), (``"ip"``, ipv4_header_uninit)];
*)
val vss_init_v_map = ``^core_init_v_map ++
                       [("inCtrl", v_struct [("inputPort", ^(mk_v_biti_arb 4))]);
			("outCtrl", v_struct [("outputPort", ^(mk_v_biti_arb 4))]);
			("b_in", v_ext_ref 0);
			("b_out", v_ext_ref 1);
			("data_crc", v_ext_ref 2)]:(string, v) alist``;

end
