open HolKernel boolLib Parse bossLib;

val _ = new_theory "p4_exec_sem_arch_soundness";

open p4Lib;
open listTheory ottTheory p4Theory p4_auxTheory p4_exec_semTheory p4_exec_sem_frames_soundnessTheory;

(* Type argument added to avoid "Unbound type variable(s) in definition: "'a"" *)
Definition arch_exec_sound:
 (arch_exec_sound arch_frame_list (type:('a itself)) =
  !(actx:'a actx) aenv g_scope_list status astate'.
  arch_exec actx (aenv, g_scope_list, arch_frame_list, status) = SOME astate' ==>
  arch_red actx (aenv, g_scope_list, arch_frame_list, status) astate')
End


Theorem arch_exec_sound_red:
!arch_frame_list type. arch_exec_sound arch_frame_list type
Proof
Cases_on `arch_frame_list` >> (
 fs [arch_exec_sound] >>
 Cases_on `status` >> (
  fs [arch_exec_def]
 )
) >> (
 rpt strip_tac >>
 PairCases_on `actx` >>
 rename1 `(ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map)` >>
 PairCases_on `aenv` >>
 rename1 `(aenv0, in_out_list, in_out_list', ascope)` >>
 rename1 `(i, in_out_list, in_out_list', ascope)`
) >| [
 Cases_on `EL i ab_list` >| [
  (* input *)
  fs [arch_exec_def] >>
  Cases_on `input_f (in_out_list,ascope)` >> (
   fs []
  ) >>
  PairCases_on `x` >>
  fs [] >>
  rw [] >>
  metis_tac [(valOf o find_clause_arch_red) "arch_in", clause_name_def],

  (* programmable block initialisation *)
  fs [arch_exec_def] >>
  Cases_on `ALOOKUP pblock_map s` >> (
   fs []
  ) >>
  Cases_on `x` >>
  fs [] >>
  Cases_on `copyin_pbl (MAP FST l',MAP SND l',l,ascope,p)` >> (
   fs []
  ) >>
  Cases_on `oEL 0 g_scope_list` >> (
   fs []
  ) >>
  Cases_on `initialise_var_stars func_map l0 [x'; declare_list_in_scope (l1,x)]` >> (
   fs []
  ) >>
  rw [] >>
  irule ((valOf o find_clause_arch_red) "arch_pbl_init") >>
  fs [clause_name_def] >>
  qexistsl_tac [`ZIP (l, ZIP (MAP FST l', MAP SND l'))`, `x`] >>
  fs [] >>
  rpt strip_tac >| [
   fs [map_tri_zip12],

   gs [listTheory.oEL_EQ_EL],

   fs [map_tri_zip12, ZIP_MAP_FST_SND],

   fs [map_tri_zip12, ZIP_MAP_FST_SND]
  ],

  (* fixed-function block *)
  fs [arch_exec_def] >>
  Cases_on `ALOOKUP ffblock_map s` >> (
   fs []
  ) >>
  Cases_on `x` >>
  fs [] >>
  Cases_on `f ascope` >> (
   fs []
  ) >>
  rw [] >>
  metis_tac [(valOf o find_clause_arch_red) "arch_ffbl", clause_name_def],

  (* output *)
  fs [arch_exec_def] >>
  Cases_on `output_f (in_out_list',ascope)` >> (
   fs []
  ) >>
  PairCases_on `x` >>
  fs [] >>
  rw [] >>
  metis_tac [(valOf o find_clause_arch_red) "arch_out", clause_name_def]
 ],

 fs [arch_exec_def],

 fs [arch_exec_def],

 Cases_on `state_fin status_running l` >| [
  (* programmable block return *)
  fs [state_fin_def] >>
  rw [] >>
  fs [arch_exec_def] >>
  Cases_on `EL i ab_list` >> (
   fs []
  ) >>
  Cases_on `ALOOKUP pblock_map s` >> (
   fs []
  ) >>
  Cases_on `x` >>
  fs [state_fin_def] >>
  Cases_on `copyout_pbl
             (g_scope_list,ascope,MAP SND l',MAP FST l',p,
              set_fin_status p status_running)` >> (
   fs []
  ) >>
  rw [] >>
  irule ((valOf o find_clause_arch_red) "arch_pbl_ret") >>
  fs [clause_name_def, state_fin_def] >>
  qexists_tac `ZIP (l, ZIP (MAP FST l', MAP SND l'))` >>
  rpt strip_tac >| [
   fs [map_tri_zip12],

   fs [map_tri_zip12, ZIP_MAP_FST_SND],

   fs [map_tri_zip12, ZIP_MAP_FST_SND]
  ],

  (* programmable block execution *)
  fs [state_fin_def, arch_exec_def] >>
  Cases_on `EL i ab_list` >> (
   fs []
  ) >>
  Cases_on `ALOOKUP pblock_map s` >> (
   fs []
  ) >>
  Cases_on `x` >>
  fs [state_fin_def] >>
  Cases_on `frames_exec (apply_table_f,ext_map,func_map,l0,l2,l3)
             (ascope,g_scope_list,l,status_running)` >> (
   fs []
  ) >>
  PairCases_on `x` >>
  fs [] >>
  rw [] >>
  irule ((valOf o find_clause_arch_red) "arch_pbl_exec") >>
  fs [clause_name_def] >>
  qexists_tac `ZIP (l', l'')` >>
  rpt strip_tac >| [
   fs [map_tri_zip12],

   fs [map_tri_zip12],

   assume_tac frame_list_exec_sound_red >>
   fs [frame_list_exec_sound]
  ]
 ],

 (* programmable block return *)
 subgoal `state_fin (status_returnv v) l` >- (
  fs [state_fin_def]
 ) >>
 fs [arch_exec_def] >>
 Cases_on `EL i ab_list` >> (
  fs []
 ) >>
 Cases_on `ALOOKUP pblock_map s` >> (
  fs []
 ) >>
 Cases_on `x` >>
 fs [] >>
 Cases_on `copyout_pbl
             (g_scope_list,ascope,MAP SND l'',MAP FST l'',p,
              set_fin_status p (status_returnv v))` >> (
  fs []
 ) >>
 rw [] >>
 irule ((valOf o find_clause_arch_red) "arch_pbl_ret") >>
 fs [clause_name_def] >>
 qexists_tac `ZIP (l', l'')` >>
 fs [map_tri_zip12],

 (* programmable block transition *)
 fs [arch_exec_def] >>
 Cases_on `EL i ab_list` >> (
  fs []
 ) >>
 Cases_on `ALOOKUP pblock_map s'` >> (
  fs []
 ) >>
 Cases_on `x` >>
 Cases_on `state_fin (status_trans s) l` >> (
  fs []
 ) >| [
  (* programmable block return *)
  Cases_on `copyout_pbl
             (g_scope_list,ascope,MAP SND l'',MAP FST l'',p,
              set_fin_status p (status_trans s))` >> (
   fs []
  ) >>
  rw [] >>
  irule ((valOf o find_clause_arch_red) "arch_pbl_ret") >>
  fs [clause_name_def] >>
  qexists_tac `ZIP (l', l'')` >>
  fs [map_tri_zip12],

  (* parser transition *)
  Cases_on `p` >> (
   fs []
  ) >>
  Cases_on `ALOOKUP l2 s` >> (
   fs []
  ) >>
  rw [] >>
  irule ((valOf o find_clause_arch_red) "arch_parser_trans") >>
  fs [clause_name_def, state_fin_def] >>
  qexists_tac `ZIP (l', l'')` >>
  rpt strip_tac >| [
   fs [map_tri_zip12],

   fs [map_tri_zip12]
  ]
 ]
]
QED

val _ = export_theory ();
