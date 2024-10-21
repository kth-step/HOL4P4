signature p4_xsaLib =
sig
  include Abbrev

val xsa_arch_ty : hol_type

val xsa_init_global_scope : term
val xsa_init_ext_obj_map : term
val xsa_init_counter : term
val xsa_init_v_map : term

val xsa_packet_in_map : term
val xsa_packet_out_map : term

val xsa_input_f : term
val xsa_output_f : term
val xsa_is_drop_port : term

val xsa_copyin_pbl : term
val xsa_copyout_pbl : term

val xsa_apply_table_f : term

val xsa_ffblock_map : term
val xsa_ext_map : term
val xsa_func_map : term

val dest_xsa_ascope : term -> term * term * term * term

end
