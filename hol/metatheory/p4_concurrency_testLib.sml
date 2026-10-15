structure p4_concurrency_testLib :> p4_concurrency_testLib = struct

open HolKernel boolLib;

open p4_concurrentSyntax p4_testLib;

open p4_concurrentTheory;

fun get_trace_thread_n arch_name actx conc_state nsteps tid =
 let
  val arch_state = arch_state_from_conc_state conc_state tid
  val other_thread_state =
   if tid = 1
   then thread_state_from_conc_state conc_state 2
   else thread_state_from_conc_state conc_state 1

  val arch_exec_thm =
   eval_step_fuel (ascope_ty_from_arch arch_name) actx arch_state nsteps;

  val trace_path_arch_thm = HO_MATCH_MP arch_exec_trace_n arch_exec_thm;

  val trace_path_conc_thm =
   if tid = 1
   then HO_MATCH_MP arch_path_implies_conc_thread1 trace_path_arch_thm
   else HO_MATCH_MP arch_path_implies_conc_thread2 trace_path_arch_thm;
 in
  SPEC other_thread_state trace_path_conc_thm
 end
;

fun get_trace_thread_next_n arch_name actx conc_trace_thm nsteps tid =
 let
  val conc_state_mid = #4 $ dest_trace_path $ concl conc_trace_thm

  val conc_trace_next_n_thm = get_trace_thread_n arch_name actx conc_state_mid nsteps tid
 in
  HO_MATCH_MP (HO_MATCH_MP conc_paths_compose_alt conc_trace_thm) conc_trace_next_n_thm
 end
;

end
