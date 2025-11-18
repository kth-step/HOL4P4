structure p4_exec_semSyntax :> p4_exec_semSyntax =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

open numSyntax;
open p4_exec_semTheory;

val (arch_multi_exec_tm, _, dest_arch_multi_exec, is_arch_multi_exec) =
  syntax_fns4 "p4_exec_sem" "arch_multi_exec";
(* TODO: Generalise *)
val mk_arch_multi_exec =
 (fn (ctx, state, fuel) => (#2 (syntax_fns4 "p4_exec_sem" "arch_multi_exec")) (“uninit_zero”, ctx, state, term_of_int fuel));

val (match_all_exec_tm, mk_match_all_exec, dest_match_all_exec, is_match_all_exec) =
  syntax_fns1 "p4_exec_sem" "match_all_exec";

end
