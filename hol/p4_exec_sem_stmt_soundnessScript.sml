open HolKernel boolLib Parse bossLib;

val _ = new_theory "p4_exec_sem_stmt_soundness";

open p4Lib;
open listTheory ottTheory p4Theory p4_auxTheory p4_exec_semTheory p4_exec_sem_e_soundnessTheory;

(* Note that this definition is phrased for given singleton statement lists, not on the frame list,
 * so soundness block nesting rules and comp1 and comp2 rules are excluded *)
Definition stmt_exec_sound:
 (stmt_exec_sound stmt =
  !ctx g_scope_list funn scopes_stack ctrl status state'.
  stmt_exec ctx (g_scope_list, [(funn, [stmt], scopes_stack)], ctrl, status) = SOME state' ==>
  stmt_red ctx (g_scope_list, [(funn, [stmt], scopes_stack)], ctrl, status) state')
End

Definition stmt_stack_exec_sound:
 (stmt_stack_exec_sound [] = T) /\
 (stmt_stack_exec_sound (h::t) = (stmt_exec_sound h /\ stmt_stack_exec_sound t))
End

Definition frame_list_exec_sound:
 (frame_list_exec_sound frame_list =
  !ctx g_scope_list ctrl status state'.
  frames_exec ctx (g_scope_list, frame_list, ctrl, status) = SOME state' ==>
  frames_red ctx (g_scope_list, frame_list, ctrl, status) state')
End

(*
val specl_stmt_block_exec_empty =
 SIMP_RULE list_ss [] (ISPECL [``ctx:ctx``, ``g_scope_list:g_scope_list``, ``funn:funn``, ``s:stmt``, ``scopes_stack:scopes_stack``, ``ctrl:ctrl``, ``status_running``, ``g_scope_list':g_scope_list``, ``[]:frame_list``] ((valOf o find_clause_stmt_red) "stmt_block_exec"))
;

val specl_stmt_block_exec_sing =
 SIMP_RULE list_ss [] (ISPECL [``ctx:ctx``, ``g_scope_list:g_scope_list``, ``funn:funn``, ``s:stmt``, ``scopes_stack:scopes_stack``, ``ctrl:ctrl``, ``status_running``, ``g_scope_list':g_scope_list``, ``[h]:frame_list``] ((valOf o find_clause_stmt_red) "stmt_block_exec"))
;
*)

Theorem stmt_ext_exec_sound_red:
stmt_exec_sound stmt_ext
Proof
fs [stmt_exec_sound] >>
rpt strip_tac >>
Cases_on `status` >> (
 fs [stmt_exec]
) >>
pairLib.PairCases_on `ctx` >>
rename1 `(ext_map, func_map, b_func_map, pars_map, tbl_map)` >>
Cases_on `scopes_stack` >> (
 fs [stmt_exec]
) >>
Cases_on `lookup_ext_fun funn ext_map` >> (
 fs []
) >>
Cases_on `x (g_scope_list,h::t,ctrl)` >> (
 fs []
) >>
pairLib.PairCases_on `x'` >>
fs [] >>
metis_tac [(valOf o find_clause_stmt_red) "stmt_ext", clause_name_def]
QED

Theorem stmt_ret_exec_sound_red:
!e.
 e_exec_sound e ==>
 stmt_exec_sound (stmt_ret e)
Proof
fs [stmt_exec_sound, e_exec_sound] >>
rpt strip_tac >>
Cases_on `status` >> (
 fs [stmt_exec]
) >>
Cases_on `scopes_stack` >> (
 fs [stmt_exec]
) >>
Cases_on `get_v e` >> (
 fs []
) >| [
 Cases_on `e_exec ctx g_scope_list (h::t) e` >> (
  fs []
 ) >>
 Cases_on `x` >> (
  fs []
 ) >>
 metis_tac [(valOf o find_clause_stmt_red) "stmt_ret_e", clause_name_def],

 Cases_on `e` >> (
  fs [get_v]
 ) >>
 metis_tac [(valOf o find_clause_stmt_red) "stmt_ret_v", clause_name_def]
]
QED

Theorem stmt_trans_exec_sound_red:
!e.
 e_exec_sound e ==>
 stmt_exec_sound (stmt_trans e)
Proof
fs [stmt_exec_sound, e_exec_sound] >>
rpt strip_tac >>
Cases_on `status` >> (
 fs [stmt_exec]
) >>
Cases_on `scopes_stack` >> (
 fs [stmt_exec]
) >>
Cases_on `is_v e` >> (
 fs []
) >| [
 Cases_on `e` >> (
  fs [is_v]
 ) >>
 Cases_on `v` >> (
  fs [is_v_str]
 ) >>
 rw [] >>
 fs [stmt_exec_trans] >>
 metis_tac [(valOf o find_clause_stmt_red) "stmt_trans", clause_name_def],

 Cases_on `e_exec ctx g_scope_list (h::t) e` >> (
  fs []
 ) >>
 pairLib.PairCases_on `x` >>
 fs [] >>
 metis_tac [(valOf o find_clause_stmt_red) "stmt_trans_e", clause_name_def]
]
QED

Theorem stmt_app_exec_sound_red:
!e_l tbl.
 (!e. e_exec_sound e) ==>
(* OR: l_sound e_l ==> ? *)
 stmt_exec_sound (stmt_app tbl e_l)
Proof
fs [stmt_exec_sound] >>
rpt strip_tac >>
pairLib.PairCases_on `ctx` >>
rename1 `(ctx0, func_map, b_func_map, pars_map, tbl_map)` >>
rename1 `(ext_map, func_map, b_func_map, pars_map, tbl_map)` >>
Cases_on `status` >> (
 fs [stmt_exec]
) >>
Cases_on `scopes_stack` >> (
 fs [stmt_exec]
) >>
Cases_on `index_not_const e_l` >> (
 fs []
) >| [
 Cases_on `FLOOKUP tbl_map tbl` >> (
  fs []
 ) >>
 Cases_on `ctrl (tbl,e_l,x)` >> (
  fs []
 ) >>
 pairLib.PairCases_on `x'` >>
 fs [] >>
 rw [] >>
 IMP_RES_TAC index_not_const_NONE >>
 subgoal `?v_l. x'1 = MAP e_v v_l` >- (
  qexists_tac `vl_of_el x'1` >>
  IMP_RES_TAC vl_of_el_MAP_e_v
 ) >>
 Q.SUBGOAL_THEN `(MAP ( \ (e_,mk_). e_) (ZIP (e_l,x)) = e_l) /\
                 (MAP ( \ v_. e_v v_) v_l = x'1)`
  (fn thm => (irule (SIMP_RULE std_ss [thm] (ISPECL [``ZIP ((e_l:e list), x: mk list)``, ``v_l:v list``]
                                                  ((valOf o find_clause_stmt_red) "stmt_apply_table_v"))))) >- (
  fs [lambda_FST, MAP_ZIP] >>
  metis_tac []
 ) >>
 fs [clause_name_def, lambda_SND, MAP_ZIP],

 Cases_on `e_exec (ext_map,func_map,b_func_map,pars_map,tbl_map) g_scope_list (h::t) (EL x e_l)` >> (
  fs []
 ) >>
 pairLib.PairCases_on `x'` >>
 fs [] >>
 rw [] >>
 Q.SUBGOAL_THEN `(MAP ( \ (e_,e'_). e_) (ZIP ((e_l:e list), (LUPDATE x'0 x e_l):e list)) = e_l) /\
                 (MAP ( \ (e_,e'_). e'_) (ZIP ((e_l:e list), (LUPDATE x'0 x e_l):e list)) = (LUPDATE x'0 x e_l))`
  (fn thm => (irule (SIMP_RULE std_ss [thm] (ISPEC ``ZIP ((e_l:e list), (LUPDATE x'0 x e_l):e list)``
                                                  ((valOf o find_clause_stmt_red) "stmt_apply_table_e"))))) >- (
  fs [lambda_FST, lambda_SND, MAP_ZIP]
 ) >>
 fs [clause_name_def] >>
 metis_tac [e_exec_sound]
]
QED

Theorem stmt_verify_exec_sound_red:
!e1 e2.
e_exec_sound e1 ==>
e_exec_sound e2 ==>
stmt_exec_sound (stmt_verify e1 e2)
Proof
fs [stmt_exec_sound, e_exec_sound] >>
rpt strip_tac >>
pairLib.PairCases_on `state'` >>
rename1 `(g_scope_list',state'1,state'2,state'3)` >>
rename1 `(g_scope_list',frame_list',ctrl',status')` >>
Cases_on `status` >> (
 fs [stmt_exec]
) >>
fs [exec_stmt_verify_SOME_REWRS] >>
Cases_on `is_v e1` >> Cases_on `is_v e2` >| [
 (* First case *)
 Cases_on `e1` >> Cases_on `e2` >> (
  fs [stmt_exec_verify]
 ) >>
 Cases_on `v` >> Cases_on `v'` >> (
  fs [stmt_exec_verify]
 ) >>
 Cases_on `b` >> (
  fs [stmt_exec_verify]
 ) >| [
  metis_tac [(valOf o find_clause_stmt_red) "stmt_verify_3", clause_name_def],

  metis_tac [(valOf o find_clause_stmt_red) "stmt_verify_4", clause_name_def]
 ],

 (* Second case - second operand unreduced *)
 Cases_on `e1` >> (
  fs [is_v]
 ) >>
 Cases_on `v` >> (
  fs [is_v_bool]
 ) >>
 metis_tac [((valOf o find_clause_stmt_red) "stmt_verify_e2"), clause_name_def],

 (* Third case - first operand unreduced *)
 metis_tac [((valOf o find_clause_stmt_red) "stmt_verify_e1"), clause_name_def],

 (* Fourth case - both operands unreduced *)
 metis_tac [((valOf o find_clause_stmt_red) "stmt_verify_e1"), clause_name_def]
]
QED

Theorem stmt_ass_exec_sound_red:
!lval e.
e_exec_sound e ==>
stmt_exec_sound (stmt_ass lval e)
Proof
fs [stmt_exec_sound, e_exec_sound] >>
rpt strip_tac >>
Cases_on `status` >> (
 fs [stmt_exec]
) >>
Cases_on `scopes_stack` >> (
 fs [stmt_exec]
) >>
Cases_on `is_v e` >> (
 fs []
) >| [
 Cases_on `stmt_exec_ass lval e (g_scope_list ++ (h::t))` >> (
  fs []
 ) >>
 Cases_on `e` >> (
  fs [is_v]
 ) >>
 rename1 `TAKE 2 g_scope_list'` >>
 rw [] >>
 fs [stmt_exec_ass] >>
 subgoal `?g_scope g_scope'. TAKE 2 g_scope_list' = [g_scope; g_scope']` >- (
  cheat
 ) >>
 subgoal `?scopes_stack''. DROP 2 g_scope_list' = scopes_stack''` >- (
  cheat
 ) >>
 fs [] >>
 irule ((valOf o find_clause_stmt_red) "stmt_ass_v") >>
 fs [clause_name_def] >>
 rpt conj_tac >| [
  Cases_on `g_scope_list'` >> (
   fs []
  ),

  Cases_on `g_scope_list'` >> (
   fs []
  ) >>
  Cases_on `t'` >> (
   fs []
  ),

  Cases_on `g_scope_list'` >> (
   fs []
  ) >>
  Cases_on `t'` >> (
   fs []
  )
 ],

 Cases_on `e_exec ctx g_scope_list (h::t) e` >> (
  fs []
 ) >>
 pairLib.PairCases_on `x` >>
 fs [] >>
 metis_tac [((valOf o find_clause_stmt_red) "stmt_ass_e"), clause_name_def]
]
QED

Theorem stmt_seq_exec_sound_red:
!s1 s2.
stmt_exec_sound s1 ==>
stmt_exec_sound s2 ==>
stmt_exec_sound (stmt_seq s1 s2)
Proof
fs [stmt_exec_sound] >>
rpt strip_tac >>
Cases_on `status` >> (
 fs [stmt_exec]
) >>
Cases_on `scopes_stack` >> (
 fs [stmt_exec]
) >>
Cases_on `is_empty s1` >> (
 fs []
) >| [
 Cases_on `s1` >> (
  fs [is_empty]
 ) >>
 metis_tac [((valOf o find_clause_stmt_red) "stmt_seq2"), clause_name_def],

 Cases_on `stmt_exec ctx (g_scope_list,[(funn,[s1],(h::t))],ctrl,status_running)` >> (
  fs []
 ) >>
 pairLib.PairCases_on `x` >> (
  fs []
 ) >>
 Cases_on `x1` >> (
  fs []
 ) >>
 Cases_on `t'` >> (
  fs []
 ) >| [
  pairLib.PairCases_on `h'` >> (
   fs []
  ) >>
  Cases_on `h'1` >> (
   fs []
  ) >>
  Cases_on `t'` >> (
   fs []
  ) >| [
   Cases_on `x3` >> (
    fs []
   ) >| [
    rw [] >>
    rename1 `(x0, [(funn', [stmt_seq s1' s2], scopes_stack')], ctrl', status_running)` >>
    rename1 `(g_scope_list', [(funn', [stmt_seq s1' s2], scopes_stack')], ctrl', status_running)` >>
    Q.SUBGOAL_THEN `funn' = funn`
     (fn thm => fs [thm]) >- (
     metis_tac [stmt_exec_inv]
    ) >>
    Q.SUBGOAL_THEN `[(funn, [stmt_seq s1' s2], scopes_stack')] = [] ++ [(funn, [stmt_seq s1' s2], scopes_stack')]`
     (fn thm => ONCE_REWRITE_TAC [thm]) >- (
     fs []
    ) >>
    Q.SUBGOAL_THEN `[(funn, [stmt_seq s1' s2], scopes_stack')] = [(funn, [] ++ [stmt_seq s1' s2], scopes_stack')]`
     (fn thm => ONCE_REWRITE_TAC [thm]) >- (
     fs []
    ) >>
    irule ((valOf o find_clause_stmt_red) "stmt_seq1") >>
    fs [clause_name_def],

    rw [] >>
    rename1 `(x0, [(funn', [s], scopes_stack')], ctrl', status_returnv v)` >>
    rename1 `(g_scope_list', [(funn', [s], scopes_stack')], ctrl', status_returnv v)` >>
    Q.SUBGOAL_THEN `funn' = funn`
     (fn thm => fs [thm]) >- (
     metis_tac [stmt_exec_inv]
    ) >>
    metis_tac [((valOf o find_clause_stmt_red) "stmt_seq3"), clause_name_def, status_distinct],

    rw [] >>
    rename1 `(x0, [(funn', [s1'], scopes_stack')], ctrl', status_trans s)` >>
    rename1 `(g_scope_list', [(funn', [s1'], scopes_stack')], ctrl', status_trans s)` >>
    Q.SUBGOAL_THEN `funn' = funn`
     (fn thm => fs [thm]) >- (
     metis_tac [stmt_exec_inv]
    ) >>
    metis_tac [((valOf o find_clause_stmt_red) "stmt_seq3"), clause_name_def, status_distinct],

    rw [] >>
    rename1 `(x0, [(funn', [s1'], scopes_stack')], ctrl', status_type_error)` >>
    rename1 `(g_scope_list', [(funn', [s1'], scopes_stack')], ctrl', status_type_error)` >>
    Q.SUBGOAL_THEN `funn' = funn`
     (fn thm => fs [thm]) >- (
     metis_tac [stmt_exec_inv]
    ) >>
    metis_tac [((valOf o find_clause_stmt_red) "stmt_seq3"), clause_name_def, status_distinct]
   ],

   Cases_on `t''` >> (
    fs []
   ) >>
   Cases_on `x3` >> (
    fs []
   ) >>
   rw [] >>
   (* TODO: stmt_seq1 *)
   (* ((valOf o find_clause_stmt_red) "stmt_seq1") *)
   cheat
  ],

  pairLib.PairCases_on `h''` >> (
   fs []
  ) >>
  Cases_on `h''1` >> (
   fs []
  ) >>
  Cases_on `t'` >> (
   fs []
  ) >>
  Cases_on `t''` >> (
   fs []
  ) >>
  Cases_on `x3` >> (
   fs []
  ) >>
  (* TODO: seq1: new frame is created *)
  rw [] >>
  cheat
 ]
]
(* OLD:
 rename1 `(x0,frame_list',ctrl',status')` >>
 rename1 `(g_scope_list',frame_list',ctrl',status')` >>
 Cases_on `frame_list'` >> (
  fs []
 ) >>
 Cases_on `t` >> (
  fs []
 ) >| [
  pairLib.PairCases_on `h` >>
  fs [] >>
  rw [] >>
  Cases_on `status'` >> (
   fs []
  ) >| [
   Q.SUBGOAL_THEN `[(funn,stmt_seq h1 s2,h2)] = [] ++ [(funn,stmt_seq h1 s2,h2)]`
    (fn thm => ONCE_REWRITE_TAC [thm]) >- (
    fs []
   ) >>
   irule ((valOf o find_clause_stmt_red) "stmt_seq1") >>
   fs [clause_name_def],

   metis_tac [((valOf o find_clause_stmt_red) "stmt_seq3"), clause_name_def, status_distinct],

   metis_tac [((valOf o find_clause_stmt_red) "stmt_seq3"), clause_name_def, status_distinct],

   metis_tac [((valOf o find_clause_stmt_red) "stmt_seq3"), clause_name_def, status_distinct]
  ],

  pairLib.PairCases_on `h'` >>
  fs [] >>
  Cases_on `t'` >> (
   fs []
  ) >>
  Cases_on `status'` >> (
   fs []
  ) >>
  rw [] >>
  Q.SUBGOAL_THEN `[h; (funn,stmt_seq h'1 s2,h'2)] = [h] ++ [(funn,stmt_seq h'1 s2,h'2)]`
   (fn thm => ONCE_REWRITE_TAC [thm]) >- (
   fs []
  ) >>
  irule ((valOf o find_clause_stmt_red) "stmt_seq1") >>
  fs [clause_name_def]
 ]
]
*)
QED

Theorem stmt_cond_exec_sound_red:
!e s1 s2.
e_exec_sound e ==>
stmt_exec_sound s1 ==>
stmt_exec_sound s2 ==>
stmt_exec_sound (stmt_cond e s1 s2)
Proof
fs [stmt_exec_sound, e_exec_sound] >>
rpt strip_tac >>
Cases_on `status` >> Cases_on `scopes_stack` >> (
 fs [stmt_exec]
) >>
Cases_on `is_v_bool e` >> (
 fs []
) >| [
 Cases_on `e` >> (
  fs [is_v_bool]
 ) >>
 Cases_on `v` >> (
  fs [is_v_bool]
 ) >>
 Cases_on `b` >> (
  fs [stmt_exec_cond]
 ) >| [
  metis_tac [((valOf o find_clause_stmt_red) "stmt_cond2"), clause_name_def],

  metis_tac [((valOf o find_clause_stmt_red) "stmt_cond3"), clause_name_def]
 ],

 Cases_on `e_exec ctx g_scope_list (h::t) e` >> (
  fs []
 ) >>
 pairLib.PairCases_on `x` >>
 fs [] >>
 metis_tac [((valOf o find_clause_stmt_red) "stmt_cond_e"), clause_name_def]
]
QED

Theorem stmt_block_exec_sound_red:
!s decl_list.
stmt_exec_sound s ==>
stmt_exec_sound (stmt_block decl_list s)
Proof
fs [stmt_exec_sound] >>
rpt strip_tac >>
Cases_on `status` >> Cases_on `scopes_stack` >> (
 fs [stmt_exec]
) >>
rw [] >>
irule ((valOf o find_clause_stmt_red) "stmt_block_enter") >>
fs [clause_name_def]
QED

Theorem stmt_exec_sound_red:
!stmt. stmt_exec_sound stmt
Proof
ASSUME_TAC e_exec_sound_red >>
irule stmt_induction >>
rpt strip_tac >| [
 (* Empty statement *)
 fs [stmt_exec_sound] >>
 rpt strip_tac >>
 Cases_on `status` >> Cases_on `scopes_stack` >> (
  fs [stmt_exec]
 ),

 (* Extern *)
 fs [stmt_ext_exec_sound_red],

 (* Return statement *)
 fs [stmt_ret_exec_sound_red],

 (* Transition statement *)
 fs [stmt_trans_exec_sound_red],

 (* Verify statement *)
 fs [stmt_verify_exec_sound_red],

 (* Apply statement *)
 fs [stmt_app_exec_sound_red],

 (* TODO: Assign statement *)
 fs [stmt_ass_exec_sound_red],

 (* TODO: Sequence of statements *)
 fs [stmt_seq_exec_sound_red],

 (* Conditional statement *)
 fs [stmt_cond_exec_sound_red],

 (* Block entry *)
 fs [stmt_block_exec_sound_red]
]
QED

Theorem return_ctrl_invar:
!ctx g_scope_list g_scope_list' funn stmt scope_stack frame_list' ctrl ctrl' v.
stmt_exec ctx (g_scope_list, [(funn, stmt, scope_stack)], ctrl, status_running) =
        SOME (g_scope_list', frame_list', ctrl', status_returnv v) ==>
 ctrl' = ctrl /\ g_scope_list' = g_scope_list /\ ?stmt'. frame_list' = [(funn, stmt', scope_stack)]
Proof
(* TODO: First, need the different possible final statuses of all different statements in
 *       rewrite theorems. Second, make separate theorem that final status return means
 *       reduced statement was return. Third, use rewrite theorem of return to prove the conclusion.       Might need to use structural induction... *)
(* TODO: Use stmt_exec_ind? P could be lambda function from ctx and state... *)
cheat
QED

Theorem initialise_equiv:
!scopes_list v funn.
scopes_list <> [] ==>
init_in_highest_scope scopes_list v (varn_star funn) = initialise scopes_list (varn_star funn) v
Proof
rpt strip_tac >>
fs [init_in_highest_scope_def, initialise_def, newest_scope_ind_def] >>
`decl_init_star scopes_list v (varn_star funn) = LAST scopes_list |+ (varn_star funn, v, NONE)` suffices_by (
 fs []
) >>
fs [decl_init_star_def, newest_scope_def, newest_scope_ind_def] >>
metis_tac [LAST_EL, arithmeticTheory.PRE_SUB1]
QED

Theorem frame_list_exec_sound_red:
!frame_list. frame_list_exec_sound frame_list
Proof
fs [frame_list_exec_sound] >>
rpt strip_tac >>
Induct_on `frame_list` >- (
 Cases_on `status` >> (
  fs [frames_exec]
 )
) >>
rpt strip_tac >>
Cases_on `status` >> (
 fs [frames_exec]
) >>
pairLib.PairCases_on `ctx` >>
rename1 `(ctx0, func_map, b_func_map, pars_map, tbl_map)` >>
rename1 `(ext_map, func_map, b_func_map, pars_map, tbl_map)` >>
Cases_on `frame_list` >| [
 (* TODO: Single frame *)
 pairLib.PairCases_on `h` >>
 fs [frames_exec] >>
 assume_tac stmt_exec_sound_red >>
 fs [stmt_exec_sound] >>
 cheat,

 (* TODO: Multiple frames *)
 cheat
]
(* OLD
 pairLib.PairCases_on `h` >>
 pairLib.PairCases_on `h'` >>
 fs [stmt_exec] >>
 Cases_on `stmt_exec (ext_map,func_map,b_func_map,pars_map,tbl_map)
             (g_scope_list,[(h0,h1,h2)],ctrl,status_running)` >> (
  fs []
 ) >>
 pairLib.PairCases_on `x` >>
 fs [] >>
 Cases_on `x3` >> (
  fs []
 ) >| [
  rw [] >>
  Q.SUBGOAL_THEN `(h0,h1,h2)::(h'0,h'1,h'2)::t = [(h0,h1,h2)] ++ ((h'0,h'1,h'2)::t)`
   (fn thm => ONCE_REWRITE_TAC [thm]) >- (
   fs []
  ) >>
  irule ((valOf o find_clause_frames_red) "frames_comp1") >>
  fs [clause_name_def, notret_def] >>
  assume_tac stmt_exec_sound_red >>
  fs [stmt_exec_sound],

  Cases_on `lookup_funn_sig_body h0 func_map ext_map` >> (
   fs []
  ) >>
  pairLib.PairCases_on `x` >>
  fs [] >>
  Cases_on `copyout (MAP FST x1') (MAP SND x1')
             (TAKE 2 (initialise (x0 ++ h'2) varn_star v))
             (DROP 2 (initialise (x0 ++ h'2) varn_star v)) h2` >> (
   fs []
  ) >>
  pairLib.PairCases_on `x` >>
  fs [] >>
  rw [] >>
  imp_res_tac return_ctrl_invar >>
  rw [] >>
  Q.SUBGOAL_THEN `(h0,h1,h2)::(h'0,h'1,h'2)::t = [(h0,h1,h2)] ++ ([(h'0,h'1,h'2)] ++ t)`
   (fn thm => ONCE_REWRITE_TAC [thm]) >- (
   fs []
  ) >>
  Q.SUBGOAL_THEN `(h'0,h'1,x1'')::t = [(h'0,h'1,x1'')] ++ t`
   (fn thm => ONCE_REWRITE_TAC [thm]) >- (
   fs []
  ) >>
  irule ((valOf o find_clause_frames_red) "frames_comp2") >>
  fs [clause_name_def] >>
  qexistsl_tac [`stmt'`, `v`] >>
  (* TODO: How can we know this? Through the addition of oTAKE and/or oDROP... *)
  subgoal `g_scope_list ++ h'2 <> []` >- (
   cheat
  ) >>
  fs [initialise_equiv] >>
  rpt conj_tac >| [
   ONCE_REWRITE_TAC [EQ_SYM_EQ] >>
   fs [] >>
   Q.PAT_X_ASSUM `copyout (MAP FST x1') (MAP SND x1')
          (TAKE 2 (initialise (g_scope_list ++ h'2) varn_star v))
          (DROP 2 (initialise (g_scope_list ++ h'2) varn_star v)) h2 =
        SOME (x0'',x1'')` (fn thm => fs [GSYM thm]) >>
   `(MAP (\(x_,d_). x_) x1') = (MAP FST x1') /\ (MAP (\(x_,d_). d_) x1') = (MAP SND x1') /\
    (TAKE 2 (initialise (g_scope_list ++ h'2) varn_star v)) = [HD (initialise (g_scope_list ++ h'2) varn_star v);
           EL 1 (initialise (g_scope_list ++ h'2) varn_star v)] /\
    (TL (TL (initialise (g_scope_list ++ h'2) varn_star v))) = (DROP 2 (initialise (g_scope_list ++ h'2) varn_star v))` suffices_by (
    fs []
   ) >>
   rpt conj_tac >| [
    fs [lambda_FST],

    fs [lambda_SND],

    (* TODO: TAKE 2 problem *)
    cheat,

    (* TODO: DROP 2 problem *)
    cheat
   ],

   assume_tac stmt_exec_sound_red >>
   fs [stmt_exec_sound]
  ],

  rw [] >>
  Q.SUBGOAL_THEN `(h0,h1,h2)::(h'0,h'1,h'2)::t = [(h0,h1,h2)] ++ ((h'0,h'1,h'2)::t)`
   (fn thm => ONCE_REWRITE_TAC [thm]) >- (
   fs []
  ) >>
  irule ((valOf o find_clause_stmt_red) "stmt_comp1") >>
  fs [clause_name_def, notret_def] >>
  assume_tac stmt_exec_sound_red >>
  fs [stmt_exec_sound],

  rw [] >>
  Q.SUBGOAL_THEN `(h0,h1,h2)::(h'0,h'1,h'2)::t = [(h0,h1,h2)] ++ ((h'0,h'1,h'2)::t)`
   (fn thm => ONCE_REWRITE_TAC [thm]) >- (
   fs []
  ) >>
  irule ((valOf o find_clause_stmt_red) "stmt_comp1") >>
  fs [clause_name_def, notret_def] >>
  assume_tac stmt_exec_sound_red >>
  fs [stmt_exec_sound]
 ]
]
*)
QED

val _ = export_theory ();
