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

val arch_ebpf_tm   : term
val dest_arch_ebpf : term -> term
val is_arch_ebpf   : term -> bool
val mk_arch_ebpf   : term -> term

val arch_ebpf_NONE_tm : term

end
