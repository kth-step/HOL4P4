signature p4_coreLib =
sig
  include Abbrev

val no_action_fun : term

val core_func_map : term

val core_ext_map : term

val core_init_v_map : term

val dest_compute_checksum16_inner : term -> term
val is_compute_checksum16_inner : term -> bool
val mk_compute_checksum16_inner : term -> term
val compute_checksum16_inner_tm : term

end
