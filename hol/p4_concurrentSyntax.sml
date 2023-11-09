structure p4_concurrentSyntax :> p4_concurrentSyntax =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

open stringSyntax optionSyntax pairSyntax listSyntax
     wordsSyntax numSyntax bitstringSyntax;
open p4_concurrentTheory;


val (trace_path_tm,  mk_trace_path, dest_trace_path, is_trace_path) =
  syntax_fns4 "p4_concurrent" "trace_path";

end
