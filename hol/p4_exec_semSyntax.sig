signature p4_exec_semSyntax =
sig
  include Abbrev

val arch_multi_exec_tm : term
val dest_arch_multi_exec : term -> term * term * term * term
val is_arch_multi_exec : term -> bool
val mk_arch_multi_exec : term * term * int -> term
val mk_arch_multi_exec_arb : term * term * int -> term

val dest_match_all_exec : term -> term
val is_match_all_exec : term -> bool
val match_all_exec_tm : term
val mk_match_all_exec : term -> term

end
