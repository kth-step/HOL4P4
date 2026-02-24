signature p4_bigstepSyntax =
sig
  include Abbrev

val bigstep_arch_exec_tm : term
val dest_bigstep_arch_exec : term -> term * term * term
val is_bigstep_arch_exec : term -> bool
val mk_bigstep_arch_exec : term * term * term -> term

val bigstep_arch_exec_none : term
val bigstep_arch_exec_none_v1model : term

val bigstep_arch_exec'_tm : term
val dest_bigstep_arch_exec' : term -> term * term * term
val is_bigstep_arch_exec' : term -> bool
val mk_bigstep_arch_exec' : term * term * term -> term

val dest_in_local_fun : term -> term * term * term
val in_local_fun_tm : term
val is_in_local_fun : term -> bool
val mk_in_local_fun : term * term * term -> term

val dest_in_local_fun' : term -> term * term * term * term
val in_local_fun'_tm : term
val is_in_local_fun' : term -> bool
val mk_in_local_fun' : term * term * term * term -> term

end
