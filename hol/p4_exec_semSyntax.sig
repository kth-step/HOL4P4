signature p4_exec_semSyntax =
sig
  include Abbrev

val arch_multi_exec_tm : term
val dest_arch_multi_exec : term -> term * term * term
val is_arch_multi_exec : term -> bool
val mk_arch_multi_exec : term * term * int -> term

val red_seq_empty_tm : term
val dest_red_seq_empty : term -> term
val is_red_seq_empty : term -> bool
val mk_red_seq_empty : term -> term

end
