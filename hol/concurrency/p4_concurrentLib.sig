signature p4_concurrentLib =
sig
  include Abbrev

val get_trace_thread_n : string -> term -> term -> int -> int -> thm
val get_trace_thread_next_n : string -> term -> thm -> int -> int -> thm

end
