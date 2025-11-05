signature p4_concurrency_testLib =
sig
  include Abbrev

val get_trace_thread_n : string -> term -> term -> int -> int -> thm
val get_trace_thread_next_n : string -> term -> thm -> int -> int -> thm

end
