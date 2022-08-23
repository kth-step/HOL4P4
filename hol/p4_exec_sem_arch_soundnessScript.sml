open HolKernel boolLib Parse bossLib;

val _ = new_theory "p4_exec_sem_arch_soundness";

open p4Lib;
open listTheory ottTheory p4Theory p4_auxTheory p4_exec_semTheory p4_exec_sem_frames_soundnessTheory;

(* Type argument added to avoid "Unbound type variable(s) in definition: "'a"" *)
Definition arch_exec_sound:
 (arch_exec_sound arch_frame_list (type:('a itself)) =
  !(actx:'a actx) aenv g_scope_list ctrl status astate'.
  arch_exec actx (aenv, g_scope_list, arch_frame_list, ctrl, status) = SOME astate' ==>
  arch_red actx (aenv, g_scope_list, arch_frame_list, ctrl, status) astate')
End


val _ = export_theory ();
