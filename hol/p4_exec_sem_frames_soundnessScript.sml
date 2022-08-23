open HolKernel boolLib Parse bossLib;

val _ = new_theory "p4_exec_sem_frames_soundness";

open p4Lib;
open listTheory ottTheory p4Theory p4_auxTheory p4_exec_semTheory p4_exec_sem_stmt_soundnessTheory;

Definition frame_list_exec_sound:
 (frame_list_exec_sound frame_list =
  !ctx g_scope_list ctrl status state'.
  frames_exec ctx (g_scope_list, frame_list, ctrl, status) = SOME state' ==>
  frames_red ctx (g_scope_list, frame_list, ctrl, status) state')
End


Theorem frame_list_exec_sound_red:
!frame_list. frame_list_exec_sound frame_list
Proof
Induct_on `frame_list` >> (
 fs [frame_list_exec_sound] >>
 Cases_on `status` >> (
  fs [frames_exec]
 )
) >>
rpt strip_tac >>
pairLib.PairCases_on `ctx` >>
rename1 `(ext_map, func_map, b_func_map, pars_map, tbl_map)` >>
Cases_on `frame_list` >| [
 (* Single frame (comp1) *)
 pairLib.PairCases_on `h` >>
 fs [frames_exec] >>
 Cases_on `scopes_to_pass h0 func_map b_func_map g_scope_list` >> (
  fs []
 ) >>
 Cases_on `stmt_exec (ext_map,func_map,b_func_map,pars_map,tbl_map)
            (x,[(h0,h1,h2)],ctrl,status_running)` >- (
  fs []
 ) >>
 pairLib.PairCases_on `x'` >>
 fs [] >>
 Cases_on `scopes_to_retrieve h0 func_map b_func_map g_scope_list x'0` >> (
  fs []
 ) >>
 rw [] >>
 rename1 `(x'0, frame_list', ctrl', status')` >>
 rename1 `(g_scope_list', frame_list', ctrl', status')` >>
 assume_tac stmt_stack_exec_sound_red >>
 fs [stmt_stack_exec_sound] >>
 RES_TAC >>
 irule (SIMP_RULE list_ss [] (Q.SPECL [`ext_map`, `func_map`, `b_func_map`, `pars_map`, `tbl_map`, `g_scope_list`, `h0`, `h1`, `h2`, `[]`] ((valOf o find_clause_frames_red) "frames_comp1"))) >>
 fs [clause_name_def] >>
 qexists_tac `x'0` >>
 fs [],

 (* Multiple frames *)
 pairLib.PairCases_on `h` >>
 pairLib.PairCases_on `h'` >>
 fs [frames_exec] >>
 Cases_on `scopes_to_pass h0 func_map b_func_map g_scope_list` >> (
  fs []
 ) >>
 Cases_on `stmt_exec (ext_map,func_map,b_func_map,pars_map,tbl_map)
            (x,[(h0,h1,h2)],ctrl,status_running)` >- (
  fs []
 ) >>
 pairLib.PairCases_on `x'` >>
 fs [] >>
 Cases_on `x'3` >> (
  fs []
 ) >| [
  (* comp1 *)
  Cases_on `scopes_to_retrieve h0 func_map b_func_map g_scope_list x'0` >> (
   fs []
  ) >>
  rw [] >>
  rename1 `(x'0, frame_list', ctrl', status_running)` >>
  rename1 `(g_scope_list'', frame_list', ctrl', status_running)` >>
  assume_tac stmt_stack_exec_sound_red >>
  fs [stmt_stack_exec_sound] >>
  RES_TAC >>
  irule (SIMP_RULE list_ss [] (Q.SPECL [`ext_map`, `func_map`, `b_func_map`, `pars_map`, `tbl_map`, `g_scope_list`, `h0`, `h1`, `h2`, `(h'0,h'1,h'2)::t`] ((valOf o find_clause_frames_red) "frames_comp1"))) >>
  fs [clause_name_def, notret_def] >>
  qexists_tac `g_scope_list''` >>
  fs [],

  (* comp2 *)
  Cases_on `oTAKE 2 (initialise (g_scope_list ++ h'2) (varn_star h0) v)` >> (
   fs []
  ) >>
  Cases_on `oDROP 2 (initialise (g_scope_list ++ h'2) (varn_star h0) v)` >> (
   fs []
  ) >>
  Cases_on `scopes_to_retrieve h0 func_map b_func_map g_scope_list x'` >> (
   fs []
  ) >>
  Cases_on `lookup_funn_sig_body h0 func_map b_func_map ext_map` >> (
   fs []
  ) >>
  pairLib.PairCases_on `x'4'` >>
  fs [] >>
  Cases_on `copyout (MAP FST x''''1) (MAP SND x''''1) x'3' x'' h2` >> (
   fs []
  ) >>
  pairLib.PairCases_on `x'4'` >>
  fs [] >>
  rw [] >>
  rename1 `(x'0, frame_list', ctrl', status_returnv v)` >>
  rename1 `(g_scope_list', frame_list', ctrl', status_returnv v)` >>
  IMP_RES_TAC stmt_exec_status_returnv_inv >>
  rw [] >>
  assume_tac stmt_stack_exec_sound_red >>
  fs [stmt_stack_exec_sound] >>
  RES_TAC >>
  fs [] >>
  irule (SIMP_RULE list_ss [] (Q.SPECL [`x''''1`, `ext_map`, `func_map`, `b_func_map`, `pars_map`, `tbl_map`, `g_scope_list`, `h0`, `h1`, `h2`, `h'0`, `h'1`, `h'2`, `t`] ((valOf o find_clause_frames_red) "frames_comp2"))) >>
  fs [clause_name_def] >>
  qexistsl_tac [`x'`, `x'3'`, `x''`, `stmt_stack'`, `v`] >>
  fs [lambda_FST, lambda_SND] >>
  rpt strip_tac >| [
   subgoal `g_scope_list ++ h'2 <> []` >- (
    subgoal `2 > 0` >- (
     fs []
    ) >>
    IMP_RES_TAC oTAKE_SOME >>
    subgoal `?ss'. initialise (g_scope_list ++ h'2) (varn_star h0) v = ss'` >- (
     fs []
    ) >>
    IMP_RES_TAC initialise_LENGTH >>
    CCONTR_TAC >>
    fs []
   ) >>
   metis_tac [initialise_equiv],

   subgoal `g_scope_list ++ h'2 <> []` >- (
    subgoal `2 > 0` >- (
     fs []
    ) >>
    IMP_RES_TAC oTAKE_SOME >>
    subgoal `?ss'. initialise (g_scope_list ++ h'2) (varn_star h0) v = ss'` >- (
     fs []
    ) >>
    IMP_RES_TAC initialise_LENGTH >>
    CCONTR_TAC >>
    fs []
   ) >>
   metis_tac [initialise_equiv],

   IMP_RES_TAC stmt_exec_status_returnv_indep >>
   Q.PAT_X_ASSUM `!g_scope_list'' ctrl''. ?g_scope_list'3' ctrl'3'. _` (fn thm => ASSUME_TAC (Q.SPECL [`g_scope_list`, `ctrl`] thm)) >>
   fs [] >>
   IMP_RES_TAC stmt_exec_status_returnv_inv >>
   fs []
  ],

  (* comp1 *)
  Cases_on `scopes_to_retrieve h0 func_map b_func_map g_scope_list x'0` >> (
   fs []
  ) >>
  rw [] >>
  rename1 `(x'0, frame_list', ctrl', status_trans s)` >>
  rename1 `(g_scope_list'', frame_list', ctrl', status_trans s)` >>
  assume_tac stmt_stack_exec_sound_red >>
  fs [stmt_stack_exec_sound] >>
  RES_TAC >>
  irule (SIMP_RULE list_ss [] (Q.SPECL [`ext_map`, `func_map`, `b_func_map`, `pars_map`, `tbl_map`, `g_scope_list`, `h0`, `h1`, `h2`, `(h'0,h'1,h'2)::t`] ((valOf o find_clause_frames_red) "frames_comp1"))) >>
  fs [clause_name_def, notret_def] >>
  qexists_tac `g_scope_list''` >>
  fs [],

  (* comp1 *)
  Cases_on `scopes_to_retrieve h0 func_map b_func_map g_scope_list x'0` >> (
   fs []
  ) >>
  rw [] >>
  rename1 `(x'0, frame_list', ctrl', status_type_error)` >>
  rename1 `(g_scope_list'', frame_list', ctrl', status_type_error)` >>
  assume_tac stmt_stack_exec_sound_red >>
  fs [stmt_stack_exec_sound] >>
  RES_TAC >>
  irule (SIMP_RULE list_ss [] (Q.SPECL [`ext_map`, `func_map`, `b_func_map`, `pars_map`, `tbl_map`, `g_scope_list`, `h0`, `h1`, `h2`, `(h'0,h'1,h'2)::t`] ((valOf o find_clause_frames_red) "frames_comp1"))) >>
  fs [clause_name_def, notret_def] >>
  qexists_tac `g_scope_list''` >>
  fs []
 ]
]
QED

val _ = export_theory ();
