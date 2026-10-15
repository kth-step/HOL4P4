structure p4_exec_semSyntax :> p4_exec_semSyntax =
struct

open HolKernel Abbrev;

open numSyntax;
local open p4_exec_semTheory in end;

val (arch_multi_exec_tm, _, dest_arch_multi_exec, is_arch_multi_exec) =
  syntax_fns3 "p4_exec_sem" "arch_multi_exec";
val mk_arch_multi_exec =
 (fn (ctx, state, fuel) => (#2 (syntax_fns3 "p4_exec_sem" "arch_multi_exec")) (ctx, state, term_of_int fuel));

end
