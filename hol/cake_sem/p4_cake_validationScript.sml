open HolKernel Parse bossLib boolLib;

val _ = new_theory "p4_cake_validation";

open p4_exec_sem_cakeTheory;

(* TODO: Move this entire file to cake_exec_sem theory? *)

(* TODO: This is a variant of arch_multi_exec' that can give NONE as a result - try to merge with other definition *)
Definition arch_multi_exec''_def:
 (arch_multi_exec'' actx ((aenv, g_scope_list, arch_frame_list, status):'a astate') 0 =
  SOME (aenv, g_scope_list, arch_frame_list, status))
  /\
 (arch_multi_exec'' actx (aenv, g_scope_list, arch_frame_list, status) (SUC fuel) =
  case arch_exec' actx (aenv, g_scope_list, arch_frame_list, status) of
  | SOME (aenv', g_scope_list', arch_frame_list', status') =>
   arch_multi_exec'' actx (aenv', g_scope_list', arch_frame_list', status') fuel
  | NONE => NONE)
End

Theorem arch_multi_exec''_add:
!actx aenv g_scope_list arch_frame_list status m n.
arch_multi_exec'' actx (aenv, g_scope_list, arch_frame_list, status) (m+n) =
 case arch_multi_exec'' actx (aenv, g_scope_list, arch_frame_list, status) n of
 | SOME (aenv', g_scope_list', arch_frame_list', status') =>
  arch_multi_exec'' actx (aenv', g_scope_list', arch_frame_list', status') m
 | NONE => NONE
Proof
Induct_on `n` >- (
 fs [arch_multi_exec''_def]
) >>
rpt strip_tac >>
fs [arch_multi_exec''_def, arithmeticTheory.ADD_CLAUSES] >>
Cases_on `arch_exec' actx (aenv,g_scope_list,arch_frame_list,status)` >> (
 fs []
) >>
PairCases_on `x` >>
fs []
QED

Theorem arch_multi_exec''_comp_n_tl:
!n m actx assl astate astate' astate''.
arch_multi_exec'' actx astate n =
  SOME astate' ==>
arch_multi_exec'' actx astate' m =
  SOME astate'' ==>
arch_multi_exec'' actx astate (n+m) =
  SOME astate''
Proof
rpt strip_tac >>
gs[] >>
PairCases_on ‘astate’ >>
PairCases_on ‘astate'’ >>
PairCases_on ‘astate''’ >>
fs [arch_multi_exec''_add]
QED


val _ = export_theory ();
