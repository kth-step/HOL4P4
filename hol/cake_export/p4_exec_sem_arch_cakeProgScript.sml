open HolKernel boolLib Parse bossLib;

val _ = new_theory "p4_exec_sem_arch_cakeProg";

open p4Syntax;
open p4Theory;
open p4_auxTheory;
open p4_exec_semTheory;

(* CakeML: *)
open preamble ml_translatorLib ml_translatorTheory ml_progLib basisProgTheory mlmapTheory basisFunctionsLib
     astPP comparisonTheory;

open p4_exec_sem_frames_cakeProgTheory;

intLib.deprecate_int();
val _ = (max_print_depth := 100);

Definition declare_list_in_scope'_def:
 declare_list_in_scope' (t_scope:t_scope, scope:scope) =
  FOLDR (\(x, (t, lvalop)) f. p4$AUPDATE f (x, (init_v_from_tau_cake t, NONE))) scope t_scope
End

Definition arch_exec'_def:
 (arch_exec' ((ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map):'a actx)
            (((i, in_out_list, in_out_list', scope):'a aenv), g_scope_list:g_scope_list, arch_frame_list_regular frame_list, status:status) =
  (case oEL i ab_list of
   | SOME (arch_block_pbl x e_l) =>
    (case ALOOKUP pblock_map x of
     | SOME (pbl_type, x_d_list, b_func_map, decl_list, pars_map, tbl_map) =>
      if state_fin_exec status frame_list
      then
       (case lookup_block_body x b_func_map of
        | SOME stmt =>
         (* TODO: The below LENGTH check is only used for proofs (e.g. soundness proof) *)
         (if LENGTH e_l = LENGTH x_d_list
          then
           (* pbl_ret *)
           (* TODO: OK to only copy out from block-global scope here? *)
           (case copyout_pbl (g_scope_list, scope, MAP SND x_d_list, MAP FST x_d_list, set_fin_status pbl_type status) of
            | SOME scope' =>
             (case oLASTN 1 g_scope_list of
              | SOME g_scope_sing =>
               SOME ((i+1, in_out_list, in_out_list', scope'), g_scope_sing,
                     arch_frame_list_empty, status_running)
              | NONE => NONE)
            | _ => NONE)
          else NONE)
        | NONE => NONE)
      else
       (case status of
        | status_trans x' =>
         (* parser_trans *)
         (case pbl_type of
          | pbl_type_parser =>
           (case ALOOKUP pars_map x' of
            | SOME stmt' =>
             SOME ((i, in_out_list, in_out_list', scope), g_scope_list, (arch_frame_list_regular [(funn_name x', [stmt'], [ [] ])]), status_running)
            | _ => NONE)
          | _ => NONE)
        | status_running =>
         (* pbl_exec *)
         (case frames_exec' (apply_table_f, ext_map, func_map, b_func_map, pars_map, tbl_map) (scope, g_scope_list, frame_list, status) of
          | SOME (scope', g_scope_list', frame_list', status') =>
           SOME ((i, in_out_list, in_out_list', scope'), g_scope_list', (arch_frame_list_regular frame_list'), status')
          | _ => NONE)
        | _ => NONE)
     | _ => NONE)
   | _ => NONE)
 )
 /\
 (arch_exec' (ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map)
            ((i, in_out_list, in_out_list', scope), g_scope_list,
             arch_frame_list_empty, status_running) =
  (case oEL i ab_list of
   (* in *)
   | SOME arch_block_inp =>
    (case input_f (in_out_list, scope) of
     | SOME (in_out_list'', scope') => 
      SOME ((i+1, in_out_list'', in_out_list', scope'), g_scope_list, arch_frame_list_empty,
             status_running)
     | NONE => NONE)
   | SOME (arch_block_pbl x e_l) =>
    (case ALOOKUP pblock_map x of
     (* pbl_init *)
     | SOME (pbl_type, x_d_list, b_func_map, decl_list, pars_map, tbl_map) =>
      (case lookup_block_body x b_func_map of
       | SOME stmt =>
        (* TODO: The below LENGTH check is only used for proofs (e.g. soundness proof) *)
        (if LENGTH e_l = LENGTH x_d_list
         then
          (case copyin_pbl ((MAP FST x_d_list), (MAP SND x_d_list), e_l, scope) of
           | SOME scope' =>
            (case oLASTN 1 g_scope_list of
             | SOME [g_scope] =>
              let g_scope_list' = ([declare_list_in_scope' (decl_list, scope')]++[g_scope]) in
               (case initialise_var_stars func_map b_func_map ext_map g_scope_list' of
                | SOME g_scope_list'' =>
                 SOME ((i, in_out_list, in_out_list', scope), g_scope_list'',
                       arch_frame_list_regular [(funn_name x, [stmt], [ [] ])], status_running)
                | NONE => NONE)
             | _ => NONE)
           | _ => NONE)
         else NONE)
       | NONE => NONE)
     | _ => NONE)
   (* ffbl *)
   | SOME (arch_block_ffbl x) =>
    (case ALOOKUP ffblock_map x of
     | SOME (ffblock_ff ff) =>
      (case ff scope of
       | SOME scope' =>
        SOME ((i+1, in_out_list, in_out_list', scope'), g_scope_list, arch_frame_list_empty, status_running)
       | NONE => NONE)
     | NONE => NONE)
   (* out *)
   | SOME arch_block_out =>
    (case output_f (in_out_list', scope) of
     | SOME (in_out_list'', scope') =>
      SOME ((0, in_out_list, in_out_list'', scope'), g_scope_list, arch_frame_list_empty,
            status_running)
     | NONE => NONE)
   | NONE => NONE
  )
 )
/\
(arch_exec' _ _ = NONE)
End

Definition arch_multi_exec'_def:
 (arch_multi_exec' actx (aenv, g_scope_list, arch_frame_list, status) 0 =
  SOME (aenv, g_scope_list, arch_frame_list, status))
  /\
 (arch_multi_exec' actx (aenv, g_scope_list, arch_frame_list, status) (SUC fuel) =
  case arch_exec' actx (aenv, g_scope_list, arch_frame_list, status) of
  | SOME (aenv', g_scope_list', arch_frame_list', status') =>
   arch_multi_exec' actx (aenv', g_scope_list', arch_frame_list', status') fuel
  | NONE => NONE)
End


val _ = translation_extends "p4_exec_sem_frames_cakeProg";

val _ = ml_prog_update (open_module "p4_exec_sem_arch_cake");

val _ = translate lookup_block_body_def;
val _ = translate oLASTN_def;
val _ = translate declare_list_in_scope'_def;
val _ = translate AUPDATE_LIST_def;
val _ = translate var_star_updates_of_func_map_def;
val _ = translate var_star_updates_of_ext_map_def;
val _ = translate initialise_var_stars_def;
val _ = translate state_fin_exec_def;
val _ = translate set_fin_status_def;

val _ = translate arch_exec'_def;

val _ = translate arch_multi_exec'_def;

val _ = ml_prog_update (close_module NONE);

val _ = export_theory ();
