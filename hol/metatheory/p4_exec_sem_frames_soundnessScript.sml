open HolKernel boolLib Parse bossLib;

val _ = new_theory "p4_exec_sem_frames_soundness";

open p4Lib;
open listTheory ottTheory p4Theory p4_auxTheory p4_exec_semTheory p4_exec_sem_stmt_soundnessTheory;

Definition frame_list_exec_sound:
 (frame_list_exec_sound (type:'a itself) frame_list =
  !(ctx:'a ctx) ascope g_scope_list status state'.
  frames_exec uninit_arb ctx (ascope, g_scope_list, frame_list, status) = SOME state' ==>
  frames_red ctx (ascope, g_scope_list, frame_list, status) state')
End

Theorem scopes_to_pass_exec_imp:
!funn func_map b_func_map g_scope_list g_scope_list'.
scopes_to_pass_exec funn func_map b_func_map g_scope_list = SOME g_scope_list' ==>
scopes_to_pass funn func_map b_func_map g_scope_list = SOME g_scope_list'
Proof
rpt strip_tac >>
gs[scopes_to_pass_def, scopes_to_pass_exec_def, AllCaseEqs()]
QED

Theorem scopes_to_retrieve_exec_imp:
!funn func_map b_func_map g_scope_list1 g_scope_list2 g_scope_list'.
scopes_to_retrieve_exec funn func_map b_func_map g_scope_list1 g_scope_list2 = SOME g_scope_list' ==>
scopes_to_retrieve funn func_map b_func_map g_scope_list1 g_scope_list2 = SOME g_scope_list'
Proof
rpt strip_tac >>
gs[scopes_to_retrieve_def, scopes_to_retrieve_exec_def, AllCaseEqs()]
QED

Theorem frame_list_exec_sound_red:
!type frame_list. frame_list_exec_sound type frame_list
Proof
Induct_on `frame_list` >> (
 gs[frame_list_exec_sound] >>
 Cases_on `status` >> (
  gs[frames_exec_def]
 )
) >>
rpt strip_tac >>
pairLib.PairCases_on `ctx` >>
rename1 `(apply_table_f, ext_map, func_map, b_func_map, pars_map, tbl_map)` >>
Cases_on `frame_list` >| [
 (* Single frame (comp1) *)
 pairLib.PairCases_on `h` >>
 gvs[frames_exec_def, AllCaseEqs()] >>
 assume_tac stmt_stack_exec_sound_red >>
 gs[stmt_stack_exec_sound] >>
 res_tac >>
 irule (SIMP_RULE list_ss [] (Q.SPECL [`apply_table_f`, `ext_map`, `func_map`, `b_func_map`, `pars_map`, `tbl_map`, `ascope`, `g_scope_list`, `h0`, `h1`, `h2`, `[]`] ((valOf o find_clause_frames_red) "frames_comp1"))) >>
 gs[clause_name_def] >>
 qexistsl_tac [‘g_scope_list'’, ‘g_scope_list''’] >>
 gvs[scopes_to_pass_exec_imp, scopes_to_retrieve_exec_imp],

 (* Multiple frames *)
 pairLib.PairCases_on `h` >>
 pairLib.PairCases_on `h'` >>
 gvs[frames_exec_def, AllCaseEqs()] >| [
  assume_tac stmt_stack_exec_sound_red >>
  fs [stmt_stack_exec_sound] >>
  RES_TAC >>
  irule (SIMP_RULE list_ss [] (Q.SPECL [`apply_table_f`, `ext_map`, `func_map`, `b_func_map`, `pars_map`, `tbl_map`, `ascope`, `g_scope_list`, `h0`, `h1`, `h2`, `(h'0,h'1,h'2)::t`] ((valOf o find_clause_frames_red) "frames_comp1"))) >>
  fs [clause_name_def, notret_def] >>
  qexistsl_tac [‘g_scope_list'’, ‘g_scope_list''’] >>
  gvs[scopes_to_pass_exec_imp, scopes_to_retrieve_exec_imp],

  (* comp2 *)
  IMP_RES_TAC stmt_exec_status_returnv_inv >>
  gvs[] >>
  assume_tac stmt_stack_exec_sound_red >>
  gs[stmt_stack_exec_sound] >>
  res_tac >>
  gs[] >>
  irule (SIMP_RULE list_ss [] (Q.SPECL [`x_d_l`, `apply_table_f`, `ext_map`, `func_map`, `b_func_map`, `pars_map`, `tbl_map`, `ascope`, `g_scope_list`, `funn`, `h1`, `h2`, `h'0`, `h'1`, `h'2`, `t`] ((valOf o find_clause_frames_red) "frames_comp2"))) >>
  gs[clause_name_def] >>
  qexistsl_tac [‘g_scope_list'’, ‘g_scope_list''’, ‘g_scope_list'3'’, ‘g_scope_list'4'’, ‘g_scope_list'5'’, ‘g_scope_list'6'’, ‘scope_list'’, ‘stmt_stack'’, ‘v’] >>
  gvs[lambda_FST, lambda_SND] >>
  gvs[scopes_to_pass_exec_imp, scopes_to_retrieve_exec_imp],

  (* comp1 *)
  assume_tac stmt_stack_exec_sound_red >>
  gs[stmt_stack_exec_sound] >>
  res_tac >>
  irule (SIMP_RULE list_ss [] (Q.SPECL [`apply_table_f`, `ext_map`, `func_map`, `b_func_map`, `pars_map`, `tbl_map`, `ascope`, `g_scope_list`, `h0`, `h1`, `h2`, `(h'0,h'1,h'2)::t`] ((valOf o find_clause_frames_red) "frames_comp1"))) >>
  gs[clause_name_def, notret_def] >>
  qexistsl_tac [‘g_scope_list'’, ‘g_scope_list''’] >>
  gvs[scopes_to_pass_exec_imp, scopes_to_retrieve_exec_imp]
 ]
]
QED

val _ = export_theory ();
