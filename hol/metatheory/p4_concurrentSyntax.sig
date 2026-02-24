signature p4_concurrentSyntax =
sig
  include Abbrev

val dest_trace_path : term -> term * term * term * term
val is_trace_path : term -> bool
val mk_trace_path : term * term * term * term -> term
val trace_path_tm : term

end
