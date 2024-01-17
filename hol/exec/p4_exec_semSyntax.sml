structure p4_exec_semSyntax :> p4_exec_semSyntax =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

open numSyntax;
open p4_exec_semTheory;

val (arch_multi_exec_tm, _, dest_arch_multi_exec, is_arch_multi_exec) =
  syntax_fns3 "p4_exec_sem" "arch_multi_exec";
val mk_arch_multi_exec =
 (fn (ctx, state, fuel) => (#2 (syntax_fns3 "p4_exec_sem" "arch_multi_exec")) (ctx, state, term_of_int fuel));

end
