structure p4_vssLib :> p4_vssLib = struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

open listSyntax;

open p4Syntax;

open p4Theory p4_coreTheory p4_vssTheory;

(* Architectural constants *)
val REAL_PORT_COUNT_tm = mk_v_bitii (8, 4);

val RECIRCULATE_IN_PORT_tm = mk_v_bitii (13, 4);
val CPU_IN_PORT_tm = mk_v_bitii (14, 4);

val DROP_PORT_tm = mk_v_bitii (15, 4);
val CPU_OUT_PORT_tm = mk_v_bitii (14, 4);
val RECIRCULATE_OUT_PORT_tm = mk_v_bitii (13, 4);

val vss_init_global_scope =
 ``(FEMPTY |+ ("REAL_PORT_COUNT", (^REAL_PORT_COUNT_tm, NONE) )
           |+ ("RECIRCULATE_IN_PORT", (^RECIRCULATE_IN_PORT_tm, NONE) )
           |+ ("CPU_IN_PORT", (^CPU_IN_PORT_tm, NONE) )
           |+ ("DROP_PORT", (^DROP_PORT_tm, NONE) )
           |+ ("CPU_OUT_PORT", (^CPU_OUT_PORT_tm, NONE) )
           |+ ("RECIRCULATE_OUT_PORT", (^RECIRCULATE_OUT_PORT_tm, NONE) )
   ):scope``;

(*************************)
(* Architectural context *)

(* Input function term *)
val vss_input_f = ``vss_input_f``;

(* Output function term *)
val vss_output_f = ``vss_output_f``;

(* Fixed-function block map *)
val vss_ffblock_map = ``FEMPTY |+ ("parser_runtime", ffblock_ff vss_parser_runtime [])
                               |+ ("pre_deparser", ffblock_ff vss_pre_deparser [])``;

val vss_ext_map = ``FEMPTY |+ ("extract", (extract, [("hdr", d_out)]))
                           |+ ("construct", (construct, []))
                           |+ ("clear", (clear, []))
                           |+ ("update", (update, [("data", d_in)]))
                           |+ ("get", (get, []))
                           |+ ("emit", (emit, [("data", d_in)]))
                           |+ ("isValid", (is_valid, []))``;

end
