structure p4_vssLib :> p4_vssLib = struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

open listSyntax;

open p4Syntax;

open p4Theory p4_coreTheory p4_vssTheory;

(* Architectural constants *)
val DROP_PORT_tm = mk_v_bitii (15, 4);
val CPU_OUT_PORT_tm = mk_v_bitii (15, 4);

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
