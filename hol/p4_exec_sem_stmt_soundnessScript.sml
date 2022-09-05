open HolKernel boolLib Parse bossLib;

val _ = new_theory "p4_exec_sem_stmt_soundness";

open p4Lib;
open listTheory ottTheory p4Theory p4_auxTheory p4_exec_semTheory p4_exec_sem_e_soundnessTheory;

(* Note that this definition is phrased for given singleton statement lists, not on the frame list,
 * so soundness block nesting rules and comp1 and comp2 rules are excluded *)
Definition stmt_exec_sound:
 (stmt_exec_sound stmt =
  !ctx g_scope_list funn stmt_stack scopes_stack ctrl status state'.
  stmt_exec ctx (g_scope_list, [(funn, stmt::stmt_stack, scopes_stack)], ctrl, status) = SOME state' ==>
  stmt_red ctx (g_scope_list, [(funn, stmt::stmt_stack, scopes_stack)], ctrl, status) state')
End

Definition stmt_stack_exec_sound:
 (stmt_stack_exec_sound stmt_stack =
  !ctx g_scope_list funn scopes_stack ctrl status state'.
  stmt_exec ctx (g_scope_list, [(funn, stmt_stack, scopes_stack)], ctrl, status) = SOME state' ==>
  stmt_red ctx (g_scope_list, [(funn, stmt_stack, scopes_stack)], ctrl, status) state')
End


fun specl_stmt_block_exec stmt frame_list' stmt_stack' =
 SIMP_RULE list_ss [] (ISPECL [``ext_map:ext_map``, ``func_map:func_map``, ``b_func_map:b_func_map``, ``pars_map:pars_map``, ``tbl_map:tbl_map``, ``g_scope_list:g_scope_list``, ``funn:funn``, stmt, ``stmt_stack:stmt_stack``, ``scopes_stack:scopes_stack``, ``ctrl:ctrl``, ``status_running``, ``g_scope_list':g_scope_list``, frame_list', stmt_stack'] ((valOf o find_clause_stmt_red) "stmt_block_exec"))
;


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
pairLib.PairCases_on `state'` >>
rename1 `(g_scope_list',state'1,state'2,state'3)` >>
rename1 `(g_scope_list',frame_list',ctrl',status')` >>
 fs [exec_stmt_ext_SOME_REWRS] >>
Cases_on `stmt_stack` >| [
 metis_tac [(valOf o find_clause_stmt_red) "stmt_ext", clause_name_def],

 irule (specl_stmt_block_exec ``stmt_ext`` ``[]:frame_list`` ``[stmt_empty]``) >>
 fs [clause_name_def] >>
 metis_tac [(valOf o find_clause_stmt_red) "stmt_ext", clause_name_def]
]
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
pairLib.PairCases_on `ctx` >>
rename1 `(ext_map, func_map, b_func_map, pars_map, tbl_map)` >>
pairLib.PairCases_on `state'` >>
rename1 `(g_scope_list',state'1,state'2,state'3)` >>
rename1 `(g_scope_list',frame_list',ctrl',status')` >>
fs [exec_stmt_ret_SOME_REWRS] >>
Cases_on `stmt_stack` >> (
 Cases_on `get_v e` >> (
  fs []
 )
) >| [
 metis_tac [(valOf o find_clause_stmt_red) "stmt_ret_e", clause_name_def],

 Cases_on `e` >> (
  fs [get_v]
 ) >>
 metis_tac [(valOf o find_clause_stmt_red) "stmt_ret_v", clause_name_def],

 irule (specl_stmt_block_exec ``stmt_ret e`` ``frame_list'':frame_list`` ``[stmt_ret e']``) >>
 fs [clause_name_def] >>
 metis_tac [(valOf o find_clause_stmt_red) "stmt_ret_e", clause_name_def],

 Cases_on `e` >> (
  fs [get_v]
 ) >>
 irule (specl_stmt_block_exec ``stmt_ret e`` ``[]:frame_list`` ``[stmt_empty]``) >>
 fs [clause_name_def] >>
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
pairLib.PairCases_on `ctx` >>
rename1 `(ext_map, func_map, b_func_map, pars_map, tbl_map)` >>
pairLib.PairCases_on `state'` >>
rename1 `(g_scope_list',state'1,state'2,state'3)` >>
rename1 `(g_scope_list',frame_list',ctrl',status')` >>
fs [exec_stmt_trans_SOME_REWRS] >>
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
 Cases_on `stmt_stack` >| [
  metis_tac [(valOf o find_clause_stmt_red) "stmt_trans", clause_name_def],

  irule (specl_stmt_block_exec ``stmt_trans (e_v (v_str s))`` ``[]:frame_list`` ``[stmt_empty]``) >>
  fs [clause_name_def] >>
  metis_tac [(valOf o find_clause_stmt_red) "stmt_trans", clause_name_def]
 ],

 Cases_on `stmt_stack` >| [
  metis_tac [(valOf o find_clause_stmt_red) "stmt_trans_e", clause_name_def],

  irule (specl_stmt_block_exec ``stmt_trans e`` ``frame_list'':frame_list`` ``[stmt_trans e']``) >>
  fs [clause_name_def] >>
  metis_tac [(valOf o find_clause_stmt_red) "stmt_trans_e", clause_name_def]
 ]
]
QED

Theorem stmt_app_exec_sound_red:
!e_l tbl.
 (!e. e_exec_sound e) ==>
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
pairLib.PairCases_on `state'` >>
rename1 `(g_scope_list',state'1,state'2,state'3)` >>
rename1 `(g_scope_list',frame_list',ctrl',status')` >>
fs [exec_stmt_app_SOME_REWRS] >>
Cases_on `index_not_const e_l` >> (
 fs []
) >| [
 rw [] >>
 IMP_RES_TAC index_not_const_NONE >>
 Cases_on `stmt_stack` >| [
  ALL_TAC,

  irule (specl_stmt_block_exec ``stmt_app tbl e_l`` ``[]:frame_list`` ``[stmt_ass lval_null (e_call (funn_name f) f_args)]``) >>
  fs [clause_name_def]
 ] >> (
  subgoal `?v_l. f_args = MAP e_v v_l` >- (
   qexists_tac `vl_of_el f_args` >>
   IMP_RES_TAC vl_of_el_MAP_e_v
  ) >>
  Q.SUBGOAL_THEN `(MAP ( \ (e_,mk_). e_) (ZIP (e_l,mk_l)) = e_l) /\
                  (MAP ( \ v_. e_v v_) v_l = f_args)`
   (fn thm => (irule (SIMP_RULE std_ss [thm] (ISPECL [``ZIP ((e_l:e list), mk_l: mk list)``, ``v_l:v list``]
                                                   ((valOf o find_clause_stmt_red) "stmt_apply_table_v"))))) >- (
   fs [lambda_FST, MAP_ZIP] >>
   metis_tac []
  ) >>
  fs [clause_name_def, lambda_SND, MAP_ZIP]
 ),

 rw [] >>
 Cases_on `stmt_stack` >| [
  ALL_TAC,

  irule (specl_stmt_block_exec ``stmt_app tbl e_l`` ``frame_list'':frame_list`` ``[stmt_app tbl (LUPDATE e' x e_l)]``) >>
  fs [clause_name_def]
 ] >> (
  Q.SUBGOAL_THEN `(MAP ( \ (e_,e'_). e_) (ZIP ((e_l:e list), (LUPDATE e' x e_l):e list)) = e_l) /\
                  (MAP ( \ (e_,e'_). e'_) (ZIP ((e_l:e list), (LUPDATE e' x e_l):e list)) = (LUPDATE e' x e_l))`
   (fn thm => (irule (SIMP_RULE std_ss [thm] (ISPEC ``ZIP ((e_l:e list), (LUPDATE e' x e_l):e list)``
                                                   ((valOf o find_clause_stmt_red) "stmt_apply_table_e"))))) >- (
   fs [lambda_FST, lambda_SND, MAP_ZIP]
  ) >>
  fs [clause_name_def] >>
  metis_tac [e_exec_sound]
 )
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
pairLib.PairCases_on `ctx` >>
rename1 `(ctx0, func_map, b_func_map, pars_map, tbl_map)` >>
rename1 `(ext_map, func_map, b_func_map, pars_map, tbl_map)` >>
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
  Cases_on `stmt_stack` >| [
   ALL_TAC,

   irule (specl_stmt_block_exec ``stmt_verify (e_v (v_bool T)) (e_v (v_err s))`` ``[]:frame_list`` ``[stmt_empty]``) >>
   fs [clause_name_def]
  ] >> (
   metis_tac [(valOf o find_clause_stmt_red) "stmt_verify_3", clause_name_def]
  ),

  Cases_on `stmt_stack` >| [
   ALL_TAC,

   irule (specl_stmt_block_exec ``stmt_verify (e_v (v_bool F)) (e_v (v_err s))`` ``[]:frame_list`` ``[stmt']:stmt list``) >>
   fs [clause_name_def]
  ] >> (
   metis_tac [(valOf o find_clause_stmt_red) "stmt_verify_4", clause_name_def]
  )
 ],

 (* Second case - second operand unreduced *)
 Cases_on `e1` >> (
  fs [is_v]
 ) >>
 Cases_on `v` >> (
  fs [is_v_bool]
 ) >>
 Cases_on `stmt_stack` >| [
  ALL_TAC,

  irule (specl_stmt_block_exec ``stmt_verify (e_v (v_bool b)) e2`` ``frame_list'':frame_list`` ``[stmt_verify (e_v (v_bool b)) e2']``) >>
  fs [clause_name_def]
 ] >> (
  metis_tac [((valOf o find_clause_stmt_red) "stmt_verify_e2"), clause_name_def]
 ),

 (* Third case - first operand unreduced *)
 fs [] >>
 Cases_on `stmt_stack` >| [
  ALL_TAC,

  irule (specl_stmt_block_exec ``stmt_verify e1 e2`` ``frame_list'':frame_list`` ``[stmt_verify e1' e2]``) >>
  fs [clause_name_def]
 ] >> (
  metis_tac [((valOf o find_clause_stmt_red) "stmt_verify_e1"), clause_name_def]
 ),

 (* Fourth case - both operands unreduced *)
 fs [] >>
 Cases_on `stmt_stack` >| [
  ALL_TAC,

  irule (specl_stmt_block_exec ``stmt_verify e1 e2`` ``frame_list'':frame_list`` ``[stmt_verify e1' e2]``) >>
  fs [clause_name_def]
 ] >> (
  metis_tac [((valOf o find_clause_stmt_red) "stmt_verify_e1"), clause_name_def]
 )
]
QED

Theorem stmt_ass_exec_sound_red:
!lval e.
e_exec_sound e ==>
stmt_exec_sound (stmt_ass lval e)
Proof
fs [stmt_exec_sound, e_exec_sound] >>
rpt strip_tac >>
pairLib.PairCases_on `ctx` >>
rename1 `(ctx0, func_map, b_func_map, pars_map, tbl_map)` >>
rename1 `(ext_map, func_map, b_func_map, pars_map, tbl_map)` >>
pairLib.PairCases_on `state'` >>
rename1 `(g_scope_list',state'1,state'2,state'3)` >>
rename1 `(g_scope_list',frame_list',ctrl',status')` >>
Cases_on `status` >> (
 fs [stmt_exec]
) >>
fs [exec_stmt_ass_SOME_REWRS] >>
Cases_on `is_v e` >> (
 fs []
) >| [
 Cases_on `e` >> (
  fs [is_v]
 ) >>
 rw [] >>
 fs [stmt_exec_ass] >>
 Cases_on `stmt_stack` >| [
  ALL_TAC,

  irule (specl_stmt_block_exec ``stmt_ass lval (e_v v)`` ``[]:frame_list`` ``[stmt_empty]``) >>
  fs [clause_name_def]
 ] >> (
  irule ((valOf o find_clause_stmt_red) "stmt_ass_v") >>
  fs [clause_name_def]
 ),

 Cases_on `stmt_stack` >| [
  ALL_TAC,

  irule (specl_stmt_block_exec ``stmt_ass lval e`` ``frame_list'':frame_list`` ``[stmt_ass lval e']``) >>
  fs [clause_name_def]
 ] >> (
 metis_tac [((valOf o find_clause_stmt_red) "stmt_ass_e"), clause_name_def]
 )
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
pairLib.PairCases_on `ctx` >>
rename1 `(ctx0, func_map, b_func_map, pars_map, tbl_map)` >>
rename1 `(ext_map, func_map, b_func_map, pars_map, tbl_map)` >>
pairLib.PairCases_on `state'` >>
rename1 `(g_scope_list',state'1,state'2,state'3)` >>
rename1 `(g_scope_list',frame_list',ctrl',status')` >>
fs [exec_stmt_seq_SOME_REWRS] >>
Cases_on `is_empty s1` >> (
 fs []
) >| [
 Cases_on `s1` >> (
  fs [is_empty]
 ) >>
 Cases_on `stmt_stack` >| [
  ALL_TAC,

  irule (specl_stmt_block_exec ``stmt_seq stmt_empty s2`` ``[]:frame_list`` ``[s2]:stmt list``) >>
  fs [clause_name_def]
 ] >> (
  metis_tac [((valOf o find_clause_stmt_red) "stmt_seq2"), clause_name_def]
 ),

 Cases_on `status' = status_running` >> (
  fs []
 ) >| [
  Cases_on `stmt_stack` >| [
   ALL_TAC,

   irule (specl_stmt_block_exec ``stmt_seq s1 s2`` ``[]:frame_list`` ``[stmt_seq stmt1' s2]:stmt list``) >>
   fs [clause_name_def]
  ] >> (
   metis_tac [SIMP_RULE list_ss [] (Q.SPECL [`ctx`, `g_scope_list`, `funn`, `s1`, `s2`, `scopes_stack`, `ctrl`, `g_scope_list'`, `[]`, `[]`] ((valOf o find_clause_stmt_red) "stmt_seq1")), clause_name_def]
  ),

  Cases_on `stmt_stack` >| [
   ALL_TAC,

   irule (specl_stmt_block_exec ``stmt_seq s1 s2`` ``[]:frame_list`` ``[stmt1']:stmt list``) >>
   fs [clause_name_def]
  ] >> (
   metis_tac [(valOf o find_clause_stmt_red) "stmt_seq3", clause_name_def]
  )
 ],

 (* stmt added to stmt stack (block entered) *)
 fs [] >>
 Cases_on `stmt_stack` >| [
  ALL_TAC,

  irule (specl_stmt_block_exec ``stmt_seq s1 s2`` ``[]:frame_list`` ``stmt1''::[stmt_seq stmt1' s2]:stmt list``) >>
  fs [clause_name_def]
 ] >> (
  metis_tac [SIMP_RULE list_ss [] (Q.SPECL [`ctx`, `g_scope_list`, `funn`, `s1`, `s2`, `scopes_stack`, `ctrl`, `g_scope_list'`, `[]`, `[stmt1'']`] ((valOf o find_clause_stmt_red) "stmt_seq1")), clause_name_def]
 ),

 (* frame added (function called) *)
 fs [] >>
 Cases_on `stmt_stack` >| [
  ALL_TAC,

  irule (specl_stmt_block_exec ``stmt_seq s1 s2`` ``[(funn',[stmt'],[scope'])]:frame_list`` ``[stmt_seq stmt1' s2]:stmt list``) >>
  fs [clause_name_def]
 ] >> (
  metis_tac [SIMP_RULE list_ss [] (Q.SPECL [`ctx`, `g_scope_list`, `funn`, `s1`, `s2`, `scopes_stack`, `ctrl`, `g_scope_list'`, `[frame]`, `[]`] ((valOf o find_clause_stmt_red) "stmt_seq1")), clause_name_def]
 )
]
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
Cases_on `status` >> (
 fs [stmt_exec]
) >>
pairLib.PairCases_on `ctx` >>
rename1 `(ctx0, func_map, b_func_map, pars_map, tbl_map)` >>
rename1 `(ext_map, func_map, b_func_map, pars_map, tbl_map)` >>
pairLib.PairCases_on `state'` >>
rename1 `(g_scope_list',state'1,state'2,state'3)` >>
rename1 `(g_scope_list',frame_list',ctrl',status')` >>
fs [exec_stmt_cond_SOME_REWRS] >>
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
  fs []
 ) >> (
  Cases_on `b'` >> (
   fs [stmt_exec_cond]
  )
 ) >| [
  Cases_on `stmt_stack` >| [
   ALL_TAC,

   irule (specl_stmt_block_exec ``stmt_cond (e_v (v_bool T)) s1 s2`` ``[]:frame_list`` ``[s1]:stmt list``) >>
   fs [clause_name_def]
  ] >> (
   metis_tac [(valOf o find_clause_stmt_red) "stmt_cond2", clause_name_def]
  ),

  Cases_on `stmt_stack` >| [
   ALL_TAC,

   irule (specl_stmt_block_exec ``stmt_cond (e_v (v_bool F)) s1 s2`` ``[]:frame_list`` ``[s2]:stmt list``) >>
   fs [clause_name_def]
  ] >> (
   metis_tac [(valOf o find_clause_stmt_red) "stmt_cond3", clause_name_def]
  )
 ],

 Cases_on `stmt_stack` >| [
  ALL_TAC,

  irule (specl_stmt_block_exec ``stmt_cond e s1 s2`` ``frame_list'':frame_list`` ``[stmt_cond e' s1 s2]``) >>
  fs [clause_name_def]
 ] >> (
  metis_tac [(valOf o find_clause_stmt_red) "stmt_cond_e", clause_name_def]
 )
]
QED

Theorem stmt_block_exec_sound_red:
!s decl_list.
stmt_exec_sound s ==>
stmt_exec_sound (stmt_block decl_list s)
Proof
fs [stmt_exec_sound] >>
rpt strip_tac >>
Cases_on `status` >> (
 fs [stmt_exec]
) >>
pairLib.PairCases_on `ctx` >>
rename1 `(ctx0, func_map, b_func_map, pars_map, tbl_map)` >>
rename1 `(ext_map, func_map, b_func_map, pars_map, tbl_map)` >>
pairLib.PairCases_on `state'` >>
rename1 `(g_scope_list',state'1,state'2,state'3)` >>
rename1 `(g_scope_list',frame_list',ctrl',status')` >>
fs [exec_stmt_block_SOME_REWRS] >>
Cases_on `stmt_stack` >| [
 ALL_TAC,

 irule (specl_stmt_block_exec ``stmt_block decl_list s`` ``[]:frame_list`` ``s::[stmt_empty]``) >>
 fs [clause_name_def]
] >> (
 irule ((valOf o find_clause_stmt_red) "stmt_block_enter") >>
 fs [clause_name_def]
)
QED

Theorem stmt_exec_sound_red:
!stmt. stmt_exec_sound stmt
Proof
assume_tac e_exec_sound_red >>
irule stmt_induction >>
rpt strip_tac >| [
 (* Empty statement *)
 fs [stmt_exec_sound] >>
 rpt strip_tac >>
 Cases_on `status` >> Cases_on `scopes_stack` >> Cases_on `stmt_stack` >> (
  fs [stmt_exec]
 ) >>
 rw [] >>
 irule ((valOf o find_clause_stmt_red) "stmt_block_exit") >>
 fs [clause_name_def],

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

 (* Assign statement *)
 fs [stmt_ass_exec_sound_red],

 (* Sequence of statements *)
 fs [stmt_seq_exec_sound_red],

 (* Conditional statement *)
 fs [stmt_cond_exec_sound_red],

 (* Block entry *)
 fs [stmt_block_exec_sound_red]
]
QED

Theorem stmt_stack_exec_sound_red:
!stmt_stack. stmt_stack_exec_sound stmt_stack
Proof
Cases_on `stmt_stack` >> (
 fs [stmt_stack_exec_sound] >>
 rpt strip_tac >>
 Cases_on `status` >> (
  fs [stmt_exec]
 ) >>
 Cases_on `scopes_stack` >> (
  fs [stmt_exec]
 )
) >>
assume_tac (SPEC ``h:stmt`` stmt_exec_sound_red) >>
fs [stmt_exec_sound]
QED

val _ = export_theory ();
