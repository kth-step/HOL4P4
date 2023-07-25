signature p4_v1modelLib =
sig
  include Abbrev

val v1model_arch_ty : hol_type

val v1model_init_global_scope : term

val v1model_packet_in_map : term
val v1model_packet_out_map : term

val v1model_input_f : term
val v1model_output_f : term

val v1model_copyin_pbl : term
val v1model_copyout_pbl : term

val v1model_apply_table_f : term

val v1model_ffblock_map : term
val v1model_ext_map : term
val v1model_func_map : term

val v1model_init_counter : term
val v1model_init_ext_obj_map : term
val v1model_init_v_map : term

end
