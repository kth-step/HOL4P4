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
  rename1 `pblock_regular p b_func_map t_scope pars_map tbl_map` >>
  Cases_on `lookup_block_sig_body s b_func_map` >> (
   fs []
  ) >>
  PairCases_on `x` >>
  rename1 `lookup_block_sig_body s b_func_map = SOME (stmt,x_d_list)` >>
  fs [] >>
  Cases_on `copyin_pbl (MAP FST x_d_list,MAP SND x_d_list,l,ascope,p)` >> (
   fs []
  ) >>
  Cases_on `oLASTN 1 g_scope_list` >> (
   fs []
  ) >>
  Cases_on `x'` >> (
   fs []
  ) >>
  Cases_on `t` >> (
   fs []
  ) >>
  Cases_on `initialise_var_stars func_map b_func_map ext_map [declare_list_in_scope (t_scope,x); h]` >> (
   fs []
  ) >>
  rw [] >>
  irule ((valOf o find_clause_arch_red) "arch_pbl_init") >>
  fs [clause_name_def] >>
  qexistsl_tac [`ZIP (l, ZIP (MAP FST x_d_list, MAP SND x_d_list))`, `x`] >>
  fs [] >>
  rpt strip_tac >| [
   fs [map_tri_zip12],

   gs [listTheory.oEL_EQ_EL] >>
   metis_tac [oLASTN_imp_LASTN],

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
  fs [state_fin_exec_def] >>
  Cases_on `lookup_block_sig_body s l'` >> (
   fs []
  ) >>
  Cases_on `x` >>
  rename1 `lookup_block_sig_body s b_func_map = SOME (stmt,x_d_list)` >>
  fs [] >>
  Cases_on `copyout_pbl
             (g_scope_list,ascope,MAP SND x_d_list,MAP FST x_d_list,p,
              set_fin_status p status_running)` >> (
   fs []
  ) >>
  rw [] >>
  irule ((valOf o find_clause_arch_red) "arch_pbl_ret") >>
  fs [clause_name_def, state_fin_def] >>
  qexists_tac `ZIP (l, ZIP (MAP FST x_d_list, MAP SND x_d_list))` >>
  rpt strip_tac >| [
   fs [map_tri_zip12],

   fs [map_tri_zip12, ZIP_MAP_FST_SND],

   fs [map_tri_zip12, ZIP_MAP_FST_SND]
  ],

  (* programmable block execution *)
  fs [GSYM state_fin_exec_equiv, arch_exec_def] >>
  Cases_on `EL i ab_list` >> (
   fs []
  ) >>
  Cases_on `ALOOKUP pblock_map s` >> (
   fs []
  ) >>
  Cases_on `x` >>
  fs [state_fin_exec_equiv, state_fin_def] >>
  Cases_on `frames_exec (apply_table_f,ext_map,func_map,l'',l1,l2)
             (ascope,g_scope_list,l,status_running)` >> (
   fs []
  ) >>
  PairCases_on `x` >>
  fs [] >>
  rw [] >>
  irule ((valOf o find_clause_arch_red) "arch_pbl_exec") >>
  fs [clause_name_def] >>
(*
  qexists_tac `ZIP (l', l'')` >>
  rpt strip_tac >| [
   fs [map_tri_zip12],

   fs [map_tri_zip12],
*)
   assume_tac frame_list_exec_sound_red >>
   fs [frame_list_exec_sound]
(*
  ]
*)
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
 Cases_on `lookup_block_sig_body s l''` >> (
  fs []
 ) >>
 Cases_on `x` >>
 fs [] >>
 rename1 `lookup_block_sig_body s b_func_map = SOME (stmt,x_d_list)` >>
 fs [] >>
 Cases_on `copyout_pbl
             (g_scope_list, ascope, MAP SND x_d_list, MAP FST x_d_list, p,
              set_fin_status p (status_returnv v))` >> (
  fs []
 ) >>
 rw [] >>
 irule ((valOf o find_clause_arch_red) "arch_pbl_ret") >>
 fs [clause_name_def] >>
 qexists_tac `ZIP (l', x_d_list)` >>
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
 fs [state_fin_exec_equiv] >>
 Cases_on `state_fin (status_trans s) l` >> (
  fs []
 ) >| [
  (* programmable block return *)
  Cases_on `lookup_block_sig_body s' l''` >> (
   fs []
  ) >>
  Cases_on `x` >>
  fs [] >>
  rename1 `lookup_block_sig_body s' b_func_map = SOME (stmt,x_d_list)` >>
  fs [] >>
  Cases_on `copyout_pbl
             (g_scope_list,ascope,MAP SND x_d_list,MAP FST x_d_list,p,
              set_fin_status p (status_trans s))` >> (
   fs []
  ) >>
  rw [] >>
  irule ((valOf o find_clause_arch_red) "arch_pbl_ret") >>
  fs [clause_name_def] >>
  qexists_tac `ZIP (l', x_d_list)` >>
  fs [map_tri_zip12],

  (* parser transition *)
  Cases_on `p` >> (
   fs []
  ) >>
  Cases_on `ALOOKUP l1 s` >> (
   fs []
  ) >>
  rw [] >>
  irule ((valOf o find_clause_arch_red) "arch_parser_trans") >>
  fs [clause_name_def, state_fin_def] (* >>
  qexists_tac `ZIP (l', l'')` >>
  rpt strip_tac >| [
   fs [map_tri_zip12],

   fs [map_tri_zip12]
  ]
*)
 ]
]
QED

val _ = export_theory ();
