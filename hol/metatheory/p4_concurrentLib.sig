signature p4_concurrentLib =
sig
  include Abbrev

val dest_trace_path : term -> term * term * term * term
val is_trace_path : term -> bool
val mk_trace_path : term * term * term * term -> term
val trace_path_tm : term

val get_trace_thread_n : string -> term -> term -> int -> int -> thm
val get_trace_thread_next_n : string -> term -> thm -> int -> int -> thm

end
