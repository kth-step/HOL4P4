structure p4_vssLib :> p4_vssLib = struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

open listSyntax;

open p4Syntax p4_coreLib;

open p4Theory p4_coreTheory p4_vssTheory;

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

val packet_in_map =
 ``[("extract", (stmt_seq stmt_ext (stmt_ret (e_v v_bot)), [("this", d_in); ("hdr", d_out)], packet_in_extract))]``;

val packet_out_map =
 ``[("emit", (stmt_seq stmt_ext (stmt_ret (e_v v_bot)), [("this", d_in); ("data", d_in)], packet_out_emit))]``;

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
                         ("pre_deparser", ffblock_ff vss_pre_deparser)]``;

val vss_Checksum16_map =
 ``[("clear", (stmt_seq stmt_ext (stmt_ret (e_v v_bot)), [("this", d_in)], Checksum16_clear));
    ("update", (stmt_seq stmt_ext (stmt_ret (e_v v_bot)), [("this", d_in); ("data", d_in)], Checksum16_update));
    ("get", (stmt_seq stmt_ext (stmt_ret (e_var varn_ext_ret)), [("this", d_in)], Checksum16_get))]``;

val vss_ext_map =
 ``((^(inst [``:'a`` |-> ``:vss_ascope``] core_ext_map))
    ++ [("packet_in", (NONE, (^packet_in_map)));
        ("packet_out", (NONE, (^packet_out_map)));
("Checksum16", SOME (stmt_seq stmt_ext (stmt_ret (e_v v_bot)), [("this", d_out)], Checksum16_construct), (^vss_Checksum16_map))])``;

end
