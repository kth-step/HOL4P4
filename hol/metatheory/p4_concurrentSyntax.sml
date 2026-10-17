structure p4_concurrentSyntax :> p4_concurrentSyntax =
struct

open HolKernel Abbrev pairSyntax;

local open p4_concurrentTheory in end;


val (trace_path_tm,  mk_trace_path, dest_trace_path, is_trace_path) =
  syntax_fns4 "p4_concurrent" "trace_path";

(* conc_state = ((io, io', ascope), (thread1, thread2)) *)
fun dest_conc_state conc_state =
 let
  val (shared, thread_states) = pairSyntax.dest_pair conc_state
  val (io, shared') = pairSyntax.dest_pair shared
  val (io', ascope) = pairSyntax.dest_pair shared'
  val (thread1, thread2) = pairSyntax.dest_pair thread_states
 in
  (io, io', ascope, thread1, thread2)
 end
;

fun arch_state_from_conc_state conc_state tid =
 let
  val (io, io', ascope, thread1, thread2) = dest_conc_state conc_state
  val (index, rest) = pairSyntax.dest_pair (if tid = 1 then thread1 else thread2)
 in
  pairSyntax.mk_pair (pairSyntax.list_mk_pair [index, io, io', ascope], rest)
 end
;

fun thread_state_from_conc_state conc_state tid =
 let
  val (_, _, _, thread1, thread2) = dest_conc_state conc_state
 in
  if tid = 1 then thread1 else thread2
 end
;

end
