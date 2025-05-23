open HolKernel Parse bossLib boolLib;

val _ = new_theory "p4_cake_validation";

open p4_exec_sem_cakeTheory;

(* TODO: These seem general, move? *)
Definition v2w8l_def:
 (v2w8l [] = SOME []) /\
 (v2w8l l =
  case oTAKE 8 l of
  | SOME v =>
   (case v2w8l (DROP 8 l) of
    | SOME res =>
     SOME (((v2w v):word8)::res)
    | NONE => NONE)
  | NONE => NONE)
Termination
WF_REL_TAC ‘measure ( \ (bl). LENGTH bl)’ \\
fs[listTheory.LENGTH_DROP]
End
(* Same as the above, using partiality instead of option type *)
Definition v2w8l'_def:
 (v2w8l' [] = []) /\
 (v2w8l' (a::(b::(c::(d::(e::(f::(g::(h::t)))))))) =
   (((v2w [a;b;c;d;e;f;g;h]):word8)::(v2w8l' t)))
End

(* TODO: Move to cake_exec_sem theory? *)
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
(* TODO: Move to cake_exec_sem theory? *)
Theorem arch_multi_exec''_comp_n_tl:
!n m actx assl aenv g_scope_list arch_frame_list status aenv' g_scope_list' arch_frame_list' status' aenv'' g_scope_list'' arch_frame_list'' status''.
arch_multi_exec'' actx (aenv, g_scope_list, arch_frame_list, status) n =
  SOME (aenv', g_scope_list', arch_frame_list', status') ==>
arch_multi_exec'' actx (aenv', g_scope_list', arch_frame_list', status') m =
  SOME (aenv'', g_scope_list'', arch_frame_list'', status'') ==>
arch_multi_exec'' actx (aenv, g_scope_list, arch_frame_list, status) (n+m) =
  SOME (aenv'', g_scope_list'', arch_frame_list'', status'')
Proof
cheat
QED


val _ = export_theory ();
