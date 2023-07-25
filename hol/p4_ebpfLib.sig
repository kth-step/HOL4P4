signature p4_ebpfLib =
sig
  include Abbrev

val ebpf_arch_ty : hol_type

val ebpf_packet_in_map : term
val ebpf_packet_out_map : term

val ebpf_init_global_scope : term

val ebpf_input_f : term
val ebpf_output_f : term

val ebpf_apply_table_f : term

val ebpf_copyin_pbl : term
val ebpf_copyout_pbl : term

val ebpf_ext_map : term
val ebpf_ffblock_map : term
val ebpf_func_map : term

val ebpf_init_counter : term
val ebpf_init_ext_obj_map : term
val ebpf_init_v_map : term

end
