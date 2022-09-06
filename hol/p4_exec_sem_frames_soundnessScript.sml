open HolKernel boolLib Parse bossLib;

val _ = new_theory "p4_exec_sem_frames_soundness";

open p4Lib;
open listTheory ottTheory p4Theory p4_auxTheory p4_exec_semTheory p4_exec_sem_stmt_soundnessTheory;

Definition frame_list_exec_sound:
 (frame_list_exec_sound (type:'a itself) frame_list =
  !(ctx:'a ctx) ascope g_scope_list status state'.
  frames_exec ctx (ascope, g_scope_list, frame_list, status) = SOME state' ==>
  frames_red ctx (ascope, g_scope_list, frame_list, status) state')
End


Theorem frame_list_exec_sound_red:
!type frame_list. frame_list_exec_sound type frame_list
Proof
Induct_on `frame_list` >> (
 fs [frame_list_exec_sound] >>
 Cases_on `status` >> (
  fs [frames_exec]
 )
) >>
rpt strip_tac >>
pairLib.PairCases_on `ctx` >>
rename1 `(apply_table_f, ext_map, func_map, b_func_map, pars_map, tbl_map)` >>
Cases_on `frame_list` >| [
 (* Single frame (comp1) *)
 pairLib.PairCases_on `h` >>
 fs [frames_exec] >>
 Cases_on `scopes_to_pass h0 func_map b_func_map g_scope_list` >> (
  fs []
 ) >>
 Cases_on `stmt_exec (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)
            (ascope,x,[(h0,h1,h2)],status_running)` >- (
  fs []
 ) >>
 pairLib.PairCases_on `x'` >>
 fs [] >>
 Cases_on `scopes_to_retrieve h0 func_map b_func_map g_scope_list x'1` >> (
  fs []
 ) >>
 rw [] >>
 rename1 `(ascope', x'1, frame_list', status')` >>
 rename1 `(ascope', g_scope_list', frame_list', status')` >>
 assume_tac stmt_stack_exec_sound_red >>
 fs [stmt_stack_exec_sound] >>
 RES_TAC >>
 irule (SIMP_RULE list_ss [] (Q.SPECL [`apply_table_f`, `ext_map`, `func_map`, `b_func_map`, `pars_map`, `tbl_map`, `ascope`, `g_scope_list`, `h0`, `h1`, `h2`, `[]`] ((valOf o find_clause_frames_red) "frames_comp1"))) >>
 fs [clause_name_def] >>
 qexists_tac `x'1` >>
 fs [],

 (* Multiple frames *)
 pairLib.PairCases_on `h` >>
 pairLib.PairCases_on `h'` >>
 fs [frames_exec] >>
 Cases_on `stmt_exec (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)
             (ascope,g_scope_list,[(h0,h1,h2)],status_running)` >> (
  fs []
 ) >>
 pairLib.PairCases_on `x` >>
 rename1 `(ascope', x1, frame_list', status')` >>
 rename1 `(ascope', g_scope_list', frame_list', status')` >>
 fs [] >>
 Cases_on `status'` >> (
  fs []
 ) >| [
  (* comp1 *)
  Cases_on `scopes_to_pass h0 func_map b_func_map g_scope_list` >> (
   fs []
  ) >>
  Cases_on `stmt_exec (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)
             (ascope,x,[(h0,h1,h2)],status_running)` >> (
   fs []
  ) >>
  pairLib.PairCases_on `x'` >>
  rename1 `(ascope'', x'1, frame_list'', status'')` >>
  rename1 `(ascope'', g_scope_list'', frame_list'', status'')` >>
  fs [] >>
  Cases_on `scopes_to_retrieve h0 func_map b_func_map g_scope_list g_scope_list''` >> (
   fs []
  ) >>
  rw [] >>
  assume_tac stmt_stack_exec_sound_red >>
  fs [stmt_stack_exec_sound] >>
  RES_TAC >>
  irule (SIMP_RULE list_ss [] (Q.SPECL [`apply_table_f`, `ext_map`, `func_map`, `b_func_map`, `pars_map`, `tbl_map`, `ascope`, `g_scope_list`, `h0`, `h1`, `h2`, `(h'0,h'1,h'2)::t`] ((valOf o find_clause_frames_red) "frames_comp1"))) >>
  fs [clause_name_def, notret_def] >>
  rpt strip_tac >| [
   cheat,

   qexists_tac `g_scope_list''` >>
   fs []
  ],

  (* comp2 *)
  Cases_on `assign g_scope_list' v (lval_varname (varn_star h0))` >> (
   fs []
  ) >>
  Cases_on `scopes_to_retrieve h0 func_map b_func_map g_scope_list x` >> (
   fs []
  ) >>
  Cases_on `lookup_funn_sig_body h0 func_map b_func_map ext_map` >> (
   fs []
  ) >>
  pairLib.PairCases_on `x''` >>
  fs [] >>
  Cases_on `copyout (MAP FST x''1) (MAP SND x''1) x' h'2 h2` >> (
   fs []
  ) >>
  pairLib.PairCases_on `x''` >>
  fs [] >>
  rw [] >>
  IMP_RES_TAC stmt_exec_status_returnv_inv >>
  rw [] >>
  assume_tac stmt_stack_exec_sound_red >>
  fs [stmt_stack_exec_sound] >>
  RES_TAC >>
  fs [] >>
  irule (SIMP_RULE list_ss [] (Q.SPECL [`x''''1`, `apply_table_f`, `ext_map`, `func_map`, `b_func_map`, `pars_map`, `tbl_map`, `ascope`, `g_scope_list`, `h0`, `h1`, `h2`, `h'0`, `h'1`, `h'2`, `t`] ((valOf o find_clause_frames_red) "frames_comp2"))) >>
  fs [clause_name_def] >>
  qexistsl_tac [`x`, `x'`, `stmt_stack'`, `v`] >>
  fs [lambda_FST, lambda_SND],

  (* comp1 *)
  Cases_on `scopes_to_pass h0 func_map b_func_map g_scope_list` >> (
   fs []
  ) >>
  Cases_on `stmt_exec (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)
             (ascope,x,[(h0,h1,h2)],status_running)` >> (
   fs []
  ) >>
  pairLib.PairCases_on `x'` >>
 rename1 `(ascope', x1, frame_list', status')` >>
 rename1 `(ascope', g_scope_list', frame_list', status')` >>
  fs [] >>
  Cases_on `scopes_to_retrieve h0 func_map b_func_map g_scope_list x'1` >> (
   fs []
  ) >>
  rw [] >>
  assume_tac stmt_stack_exec_sound_red >>
  fs [stmt_stack_exec_sound] >>
  RES_TAC >>
  irule (SIMP_RULE list_ss [] (Q.SPECL [`apply_table_f`, `ext_map`, `func_map`, `b_func_map`, `pars_map`, `tbl_map`, `ascope`, `g_scope_list`, `h0`, `h1`, `h2`, `(h'0,h'1,h'2)::t`] ((valOf o find_clause_frames_red) "frames_comp1"))) >>
  fs [clause_name_def, notret_def] >>
  rpt strip_tac >| [
   cheat,

   qexists_tac `x'1` >>
   fs []
  ]
 ]
]
QED

val _ = export_theory ();
