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
 ``(FEMPTY |+ (varn_name "REAL_PORT_COUNT", (^REAL_PORT_COUNT_tm, NONE) )
           |+ (varn_name "RECIRCULATE_IN_PORT", (^RECIRCULATE_IN_PORT_tm, NONE) )
           |+ (varn_name "CPU_IN_PORT", (^CPU_IN_PORT_tm, NONE) )
           |+ (varn_name "DROP_PORT", (^DROP_PORT_tm, NONE) )
           |+ (varn_name "CPU_OUT_PORT", (^CPU_OUT_PORT_tm, NONE) )
           |+ (varn_name "RECIRCULATE_OUT_PORT", (^RECIRCULATE_OUT_PORT_tm, NONE) )
   ):scope``;

(*************************)
(* Architectural context *)

(* Input function term *)
val vss_input_f = ``vss_input_f``;

(* Output function term *)
val vss_output_f = ``vss_output_f``;

(* Fixed-function block map *)
val vss_ffblock_map = ``FEMPTY |+ ("parser_runtime", ffblock_ff vss_parser_runtime)
                               |+ ("pre_deparser", ffblock_ff vss_pre_deparser)``;

val vss_Checksum16_map =
 ``(FEMPTY
    |+ ("clear", (stmt_seq stmt_ext (stmt_ret (e_v v_bot)), [("this", d_inout)], Checksum16_clear))
    |+ ("update", (stmt_seq stmt_ext (stmt_ret (e_v v_bot)), [("this", d_inout); ("data", d_in)], Checksum16_update))
    |+ ("get", (stmt_seq stmt_ext (stmt_ret (e_var varn_ext_ret)), [("this", d_inout)], Checksum16_get))):ext_fun_map``;

val vss_ext_map =
 ``((^core_ext_map)
    |+ ("Checksum16", SOME (stmt_seq stmt_ext (stmt_ret (e_var varn_ext_ret)), [], Checksum16_construct), (^vss_Checksum16_map))):ext_map``;

end
