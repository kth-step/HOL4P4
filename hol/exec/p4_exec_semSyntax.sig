signature p4_exec_semSyntax =
sig
  include Abbrev

val arch_multi_exec_tm : term
val dest_arch_multi_exec : term -> term * term * term
val is_arch_multi_exec : term -> bool
val mk_arch_multi_exec : term * term * int -> term

end
