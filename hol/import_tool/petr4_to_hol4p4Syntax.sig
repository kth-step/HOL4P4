signature petr4_to_hol4p4Syntax =
sig
  include Abbrev

val NONE_msg_tm   : term
val dest_NONE_msg : term -> term
val is_NONE_msg   : term -> bool
val mk_NONE_msg   : term -> term

val SOME_msg_tm   : term
val dest_SOME_msg : term -> term
val is_SOME_msg   : term -> bool
val mk_SOME_msg   : term -> term

val arch_vss_tm   : term
val dest_arch_vss : term -> term
val is_arch_vss   : term -> bool
val mk_arch_vss   : term -> term

val arch_vss_NONE_tm : term

val vss_pkg_VSS_tm   : term
val dest_vss_pkg_VSS : term -> term
val is_vss_pkg_VSS   : term -> bool
val mk_vss_pkg_VSS   : term -> term

val arch_ebpf_tm   : term
val dest_arch_ebpf : term -> term
val is_arch_ebpf   : term -> bool
val mk_arch_ebpf   : term -> term

val arch_ebpf_NONE_tm : term

val ebpf_pkg_ebpfFilter_tm    : term
val dest_ebpf_pkg_ebpfFilter  : term -> term
val is_ebpf_pkg_ebpfFilter    : term -> bool
val mk_ebpf_pkg_ebpfFilter    : term -> term

val arch_v1model_tm   : term
val dest_arch_v1model : term -> term
val is_arch_v1model   : term -> bool
val mk_arch_v1model   : term -> term

val arch_v1model_NONE_tm : term

val v1model_pkg_V1Switch_tm   : term
val dest_v1model_pkg_V1Switch : term -> term * term
val is_v1model_pkg_V1Switch   : term -> bool
val mk_v1model_pkg_V1Switch   : term * term -> term

end
