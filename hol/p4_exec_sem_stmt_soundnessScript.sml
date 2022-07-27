open HolKernel boolLib Parse bossLib;

val _ = new_theory "p4_exec_sem_stmt_soundness";

open p4Lib;
open ottTheory p4Theory p4_exec_semTheory p4_exec_sem_e_soundnessTheory;

(* Only meant to skip certain soundness proof parts for now *)
Theorem stmt_ignore_pars_next:
 !ctx g_scope_list frame_list ctrl p state'.
  stmt_red ctx (g_scope_list, frame_list, ctrl, (status_pars_next p)) state'
Proof
cheat
QED

(* Note that this definition is phrased for given singleton statement lists, not on the frame list,
 * so soundness block nesting rules and comp1 and comp2 rules are excluded *)
Definition stmt_exec_sound:
 (stmt_exec_sound stmt =
  !ctx g_scope_list funn scopes_stack ctrl status state'.
  stmt_exec ctx (g_scope_list, [(funn, [stmt], scopes_stack)], ctrl, status) = SOME state' ==>
  stmt_red ctx (g_scope_list, [(funn, [stmt], scopes_stack)], ctrl, status) state')
End

Theorem stmt_block_exec_sound_red:
!stmt decl_list.
stmt_exec_sound stmt ==>
stmt_exec_sound (stmt_block decl_list stmt)
Proof
cheat
QED

Theorem stmt_verify_exec_sound_red:
!e1 e2.
e_exec_sound e1 ==>
e_exec_sound e2 ==>
stmt_exec_sound (stmt_verify e1 e2)
Proof
fs [stmt_exec_sound, e_exec_sound] >>
REPEAT STRIP_TAC >>
pairLib.PairCases_on `state'` >>
rename1 `(g_scope_list',state'1,state'2,state'3)` >>
rename1 `(g_scope_list',frame_list',ctrl',status')` >>
Cases_on `status` >> (
 fs [stmt_exec, stmt_ignore_pars_next]
) >>
Cases_on `is_v e1` >> Cases_on `is_v e2` >| [
 (* First case *)
 fs [] >>
 Cases_on `stmt_exec_verify e1 e2` >> (
  fs [] >>
  rw []
 ) >>
 Cases_on `e1` >> Cases_on `e2` >> (
  fs [stmt_exec_verify] >>
  rw []
 ) >>
 rename1 `is_v_bool (e_v v1)` >>
 rename1 `is_v_err (e_v v2)` >>
 Cases_on `v1` >> Cases_on `v2` >> (
  fs [stmt_exec_verify] >>
  rw []
 ) >>
 Cases_on `x` >> (
  Cases_on `b` >> (
   fs [stmt_exec_verify]
  )
 ) >| [
  METIS_TAC [(valOf o find_clause_stmt_red) "stmt_verify_3", clause_name_def],

  METIS_TAC [(valOf o find_clause_stmt_red) "stmt_verify_4", clause_name_def]
 ],

 (* Second case - second operand unreduced *)
 fs [] >>
 Cases_on `e_exec ctx g_scope_list scopes_stack e2` >> (
  fs []
 ) >>
 Cases_on `x` >>
 fs [] >>
 rw [] >>
 Cases_on `e1` >> (
  fs [is_v] >>
  rw []
 ) >>
 Cases_on `v` >> (
  fs [is_v_bool] >>
  rw []
 ) >>
 METIS_TAC [((valOf o find_clause_stmt_red) "stmt_verify_e2"), clause_name_def],

 (* Third case - first operand unreduced *)
 fs [] >>
 Cases_on `e_exec ctx g_scope_list scopes_stack e1` >> (
  fs []
 ) >>
 Cases_on `x` >>
 fs [] >>
 rw [] >>
 METIS_TAC [((valOf o find_clause_stmt_red) "stmt_verify_e1"), clause_name_def],

 (* Fourth case - both operands unreduced *)
 fs [] >>
 Cases_on `e_exec ctx g_scope_list scopes_stack e1` >> (
  fs []
 ) >>
 Cases_on `x` >>
 fs [] >>
 rw [] >>
 METIS_TAC [((valOf o find_clause_stmt_red) "stmt_verify_e1"), clause_name_def]
]
QED

Theorem stmt_exec_sound_red:
!stmt. stmt_exec_sound stmt
Proof
ASSUME_TAC e_exec_sound_red >>
irule stmt_induction >>
REPEAT STRIP_TAC >| [
 (* TODO: Empty statement - how should this be handled in reductions? *)
 cheat,

 (* Extern *)
 (* TODO *)
 cheat,

 (* Return statement *)
 (* TODO *)
 cheat,

 (* Transition statement *)
 (* TODO *)
 cheat,

 (* Verify statement *)
 fs [stmt_verify_exec_sound_red],

 (* Apply statement *)
 (* TODO *)
 cheat,

 (* Assign statement *)
 (* TODO *)
 cheat,

 (* Sequence of statements *)
 (* TODO *)
 cheat,

 (* Conditional statement *)
 (* TODO *)
 cheat,

 (* Block entry *)
 fs [stmt_block_exec_sound_red]
]
QED

val _ = export_theory ();
