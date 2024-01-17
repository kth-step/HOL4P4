structure p4_concurrentLib :> p4_concurrentLib =
struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

open pairSyntax optionSyntax wordsSyntax bitstringSyntax listSyntax numSyntax;

open evalwrapLib;
open p4Syntax p4_auxTheory testLib;
open p4_vssTheory p4_ebpfTheory;
open p4_exec_semTheory p4_exec_semSyntax;
open p4_testLib;

open p4_concurrentTheory p4_concurrentSyntax;


(***********************)
(* Concurrency-related *)

(* TODO: Move to concurrencySyntax *)
fun arch_state_from_conc_state conc_state tid =
 let
  val [io, io', n_externs, ext_obj_map, v_map, ctrl, index1, gscope1, arch_frame_list1, status1, index2, gscope2, arch_frame_list2, status2] = strip_pair conc_state
  val aenv = list_mk_pair [n_externs, ext_obj_map, v_map, ctrl]
 in
  if tid = 1
  then list_mk_pair [
        list_mk_pair [index1, io, io', aenv],
        gscope1, arch_frame_list1, status1
       ]
  else list_mk_pair [
        list_mk_pair [index2, io, io', aenv],
        gscope2, arch_frame_list2, status2
       ]
 end
;

(* TODO: Move to concurrencySyntax *)
fun thread_state_from_conc_state conc_state tid =
 let
  val [io, io', n_externs, ext_obj_map, v_map, ctrl, index1, gscope1, arch_frame_list1, status1, index2, gscope2, arch_frame_list2, status2] = strip_pair conc_state
 in
  if tid = 1
  then list_mk_pair [index1, gscope1, arch_frame_list1, status1]
  else list_mk_pair [index2, gscope2, arch_frame_list2, status2]
 end
;

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
