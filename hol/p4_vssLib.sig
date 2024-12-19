signature p4_vssLib =
sig
  include Abbrev

val vss_arch_ty : hol_type

val vss_objectless_map : term
val vss_packet_in_map : term
val vss_packet_out_map : term

val REAL_PORT_COUNT_tm : term

val RECIRCULATE_IN_PORT_tm : term
val CPU_IN_PORT_tm : term

val DROP_PORT_tm : term
val CPU_OUT_PORT_tm : term
val RECIRCULATE_OUT_PORT_tm : term

val vss_init_global_scope : term

val vss_input_f : term
val vss_output_f : term

val vss_apply_table_f : term

val vss_copyin_pbl : term
val vss_copyout_pbl : term

val vss_ext_map : term
val vss_ffblock_map : term
val vss_func_map : term

val vss_init_counter : term
val vss_init_ext_obj_map : term

val vss_parsed_packet_struct_uninit : term

val vss_init_v_map : term

end
