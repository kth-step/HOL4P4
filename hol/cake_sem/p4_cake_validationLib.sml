structure p4_cake_validationLib :> p4_cake_validationLib = struct

open HolKernel boolLib Parse bossLib numSyntax;

open p4_auxTheory;
open p4Syntax p4_testLib;

open p4_cake_validationTheory;

val (arch_multi_exec''_tm, _, dest_arch_multi_exec'', is_arch_multi_exec'') =
  syntax_fns3 "p4_cake_validation" "arch_multi_exec''";
val mk_arch_multi_exec'' =
 (fn (ctx, state, fuel) => (#2 (syntax_fns3 "p4_cake_validation" "arch_multi_exec''")) (ctx, state, term_of_int fuel));

fun final_state_is_none step_thm = optionSyntax.is_none $ rhs $ concl step_thm;

(* WARNING: Not guaranteed to terminate! *)
local
fun eval_step_cake' actx comp_thm step_thm =
 let
  val curr_state = the_final_state step_thm
  val step_thm2 =
   EVAL “^(mk_arch_multi_exec'' (actx, curr_state, 1))”;
 in
  if final_state_is_none step_thm2
  then step_thm
  else
   let
    val comp_step_thm =
     SIMP_RULE simple_arith_ss []
      (MATCH_MP (MATCH_MP comp_thm step_thm) step_thm2);
   in
    eval_step_cake' actx comp_thm comp_step_thm
   end
 end
in
fun eval_step_cake ascope_ty actx astate =
 let
  val step_thm =
   EVAL “^(mk_arch_multi_exec'' (actx, astate, 1))”;
  val comp_thm = INST_TYPE [Type.alpha |-> ascope_ty] arch_multi_exec''_comp_n_tl;
 in
  if final_state_is_none step_thm
  then raise UNCHANGED
  else eval_step_cake' actx comp_thm step_thm
 end
end;

local
fun get_existentials eval_thm =
 let
  val final_state = the_final_state eval_thm
  val steps = last $ snd $ strip_comb $ lhs $ concl eval_thm
  val (aenv', g_scope_list', arch_frame_list', status') = dest_astate final_state
  (* TODO: Below line might not generalise well in future if the aenv type changes *)
  val (ab_index', _, _, ascope') = dest_aenv aenv'
 in
  [steps, ab_index', ascope', g_scope_list', arch_frame_list', status']
 end

in
fun p4_eval_test_tac' aenv_ty actx astate =
 let
  (* eval_steps repeatedly evaluates until NONE is reached *)
  val step_thm = eval_step_cake aenv_ty actx astate
  val [n, ab_index', ascope', g_scope_list', arch_frame_list', status'] =
   get_existentials step_thm
 in
  (* Perform consecutive exists_tac on all existentially quantified variables in the
   * theorem *)
  (foldr (fn (a, b) => a >> b) ALL_TAC
   (map exists_tac [n, ab_index', ascope', g_scope_list', arch_frame_list', status']))
  >> fs [step_thm, p4_replace_input_def]
  >> FULL_SIMP_TAC (bool_ss++bitstringLib.v2w_n2w_ss) [v2w8l'_def]
 end
end;

end
