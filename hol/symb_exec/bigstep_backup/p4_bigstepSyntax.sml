structure p4_bigstepSyntax :> p4_bigstepSyntax =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib listSyntax;

open p4_bigstepTheory;

(* TODO: Move *)
val (bigstep_arch_exec_tm,  mk_bigstep_arch_exec, dest_bigstep_arch_exec, is_bigstep_arch_exec) =
  syntax_fns3 "p4_bigstep" "bigstep_arch_exec";
val bigstep_arch_exec_none = optionSyntax.mk_none “:('a actx # b_func_map)”;
val bigstep_arch_exec_none_v1model = optionSyntax.mk_none “:(v1model_ascope actx # b_func_map)”;

val (bigstep_arch_exec'_tm,  mk_bigstep_arch_exec', dest_bigstep_arch_exec', is_bigstep_arch_exec') =
  syntax_fns3 "p4_bigstep" "bigstep_arch_exec'";

(* TODO: Move *)
val (in_local_fun_tm,  mk_in_local_fun, dest_in_local_fun, is_in_local_fun) =
  syntax_fns3 "p4_bigstep" "in_local_fun";

(* TODO: Move *)
val (in_local_fun'_tm,  mk_in_local_fun', dest_in_local_fun', is_in_local_fun') =
  syntax_fns4 "p4_bigstep" "in_local_fun'";

end
