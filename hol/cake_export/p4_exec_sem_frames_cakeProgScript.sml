open HolKernel boolLib Parse bossLib;

val _ = new_theory "p4_exec_sem_frames_cakeProg";

open p4Syntax;
open p4Theory;
open p4_auxTheory;
open p4_exec_semTheory;

(* CakeML: *)
open preamble ml_translatorLib ml_translatorTheory ml_progLib basisProgTheory mlmapTheory basisFunctionsLib
     astPP comparisonTheory;

open p4_exec_sem_stmt_cakeProgTheory;

intLib.deprecate_int();
val _ = (max_print_depth := 100);


Definition scopes_to_pass'_def:
 scopes_to_pass' (funn:funn) (func_map_g:func_map) (b_func_map:b_func_map) (g_scope_list:g_scope_list) =
  case g_scope_list of
  | [block_scope; global_scope] =>
   (case funn of
    | (funn_name x) =>
     (case ALOOKUP b_func_map x of
      | SOME (stmt, x_d_l) => SOME [block_scope; global_scope]
      | NONE =>
       (case ALOOKUP func_map_g x of
        | SOME (stmt, x_d_l) => SOME ([[]; global_scope])
        | NONE => SOME [block_scope; global_scope]
       )
     )
    | _ => SOME ([[]; global_scope]))
  | _ => NONE
End

Definition scopes_to_retrieve'_def:
 scopes_to_retrieve' (funn:funn) (func_map_g:func_map) (b_func_map:b_func_map) (g_scope_list_og:g_scope_list) (g_scope_list:g_scope_list) =
  case g_scope_list_og of
   | [block_scope_og; global_scope_og] =>
    (case g_scope_list of
     | [block_scope; global_scope] =>
      (case funn of
       | (funn_name x) =>
        (case ALOOKUP b_func_map x of
         | SOME (stmt, x_d_l) => SOME [block_scope; global_scope]
         | NONE =>
          (case ALOOKUP func_map_g x of
           | SOME (stmt, x_d_l) => SOME [block_scope_og; global_scope]
           | NONE => SOME [block_scope; global_scope]))
       | _ => SOME [block_scope_og; global_scope])
     | _ => NONE)
   | _ => NONE
End

Definition update_return_frame'_def:
 update_return_frame' xlist dlist ss ss_curr = 
  FOLDL
   (\ss_temp_opt (x,d).
    if (is_d_none_in d)
    then ss_temp_opt
    else
     case ss_temp_opt of
     | SOME ss_temp =>
      (case lookup_map ss_curr (varn_name x) of
       | SOME (v, stret_opt) =>
        (case stret_opt of
         | SOME stret => assign' ss_temp v stret
         | NONE => NONE)
       | _ => NONE)
     | NONE => NONE
   )
   (SOME ss)
   (ZIP(xlist, dlist))
End

Definition copyout'_def:
 copyout' xlist dlist gsl ss ss_curr =
  if ss_curr <> []
  then
   (case update_return_frame' xlist dlist (ss++gsl) [LAST ss_curr] of
    | SOME updated_return_ss =>
     (case (LENGTH updated_return_ss) of
      | 0 => NONE
      | i => SOME (THE (oDROP (i-2) updated_return_ss), THE(oTAKE (i-2) updated_return_ss)))
    | NONE => NONE)
  else NONE
End

Definition frames_exec'_def:
 (******************************************)
 (* Catch-all clauses for special statuses *)
 (frames_exec' (ctx:'a ctx) ((ascope:'a, g_scope_list:g_scope_list, frame_list:frame_list, status_returnv v):'a state') = NONE)
  /\
 (frames_exec' _ (_, _, _, status_trans x) = NONE)
  /\
 (* Empty frame list *)
 (frames_exec' _ (_, _, [], _) = NONE)
  /\
 (*********)
 (* Comp2 + Comp1 case of multiple frames *)
 (frames_exec' (apply_table_f, ext_map, func_map, b_func_map, pars_map, tbl_map) (ascope, g_scope_list, ((funn, stmt_stack, scope_list)::((funn', stmt_stack', scope_list')::frame_list'')), status_running) =
  (case scopes_to_pass' funn func_map b_func_map g_scope_list of
   | SOME g_scope_list' =>
    (case map_to_pass funn b_func_map of
     | SOME b_func_map' =>
      (case tbl_to_pass funn b_func_map tbl_map of
       | SOME tbl_map' =>
        (case stmt_exec' (apply_table_f, ext_map, func_map, b_func_map', pars_map, tbl_map') (ascope, g_scope_list', [(funn, stmt_stack, scope_list)], status_running) of
         | SOME (ascope', g_scope_list'', frame_list', status') =>
          (case status' of
           | status_returnv v =>
            (* Comp2 *)
            (case frame_list' of
             | [(funn, stmt_stack'', scope_list'')] =>
              (case assign' g_scope_list'' v (lval_varname (varn_star funn)) of
               | SOME g_scope_list''' =>
                (case scopes_to_retrieve' funn func_map b_func_map g_scope_list g_scope_list''' of
                 | SOME g_scope_list'''' =>
                  (case lookup_funn_sig_body funn func_map b_func_map ext_map of
                   | SOME (stmt'', x_d_l) =>
                    (case scopes_to_pass' funn' func_map b_func_map g_scope_list'''' of
                     | SOME g_scope_list''''' =>
                      (case copyout' (MAP FST x_d_l) (MAP SND x_d_l) g_scope_list''''' scope_list' scope_list'' of
                       | SOME (g_scope_list'''''', scope_list''') =>
                        (case scopes_to_retrieve' funn' func_map b_func_map g_scope_list'''' g_scope_list'''''' of
                         | SOME g_scope_list''''''' =>
                          SOME (ascope', g_scope_list''''''', ((funn', stmt_stack', scope_list''')::frame_list''), status_running)
                         | _ => NONE)
                       | _ => NONE)
                     | _ => NONE)
                   | _ => NONE)
                 | _ => NONE)
               | NONE => NONE)
             | _ => NONE)
           | _ => 
            (* Comp1 *)
            (case scopes_to_retrieve' funn func_map b_func_map g_scope_list g_scope_list'' of
             | SOME g_scope_list''' =>
              SOME (ascope', g_scope_list''', frame_list'++((funn', stmt_stack', scope_list')::frame_list''), status')
             | _ => NONE))
         | _ => NONE)
       | _ => NONE)
     | _ => NONE)
   | _ => NONE))
  /\
 (*********)
 (* Comp1, remaining cases *)
 (frames_exec' (apply_table_f, ext_map, func_map, b_func_map, pars_map, tbl_map) (ascope, g_scope_list, [(funn, stmt_stack, scope_list)], status_running) =
  (case scopes_to_pass' funn func_map b_func_map g_scope_list of
   | SOME g_scope_list' =>
    (case map_to_pass funn b_func_map of
     | SOME b_func_map' =>
      (case tbl_to_pass funn b_func_map tbl_map of
       | SOME tbl_map' =>
        (case stmt_exec' (apply_table_f, ext_map, func_map, b_func_map', pars_map, tbl_map') (ascope, g_scope_list', [(funn, stmt_stack, scope_list)], status_running) of
         | SOME (ascope', g_scope_list'', frame_list', status') =>
          (case scopes_to_retrieve' funn func_map b_func_map g_scope_list g_scope_list'' of
           | SOME g_scope_list''' =>
            SOME (ascope', g_scope_list''', frame_list', status')
           | _ => NONE)
         | _ => NONE)
       | _ => NONE)
     | _ => NONE)
   | _ => NONE))
 /\
 (frames_exec' _ _ = NONE)
End

val _ = translation_extends "p4_exec_sem_stmt_cakeProg";

val _ = ml_prog_update (open_module "p4_exec_sem_frames_cake");

val _ = translate ALOOKUP_def; (* TODO: Has this really not been translated before? *)
val _ = translate scopes_to_pass'_def;
val _ = translate map_to_pass_def;
val _ = translate tbl_to_pass_def;
val _ = translate scopes_to_retrieve'_def;

val _ = translate is_d_none_in_def;
val _ = translate update_return_frame'_def;
val _ = translate copyout'_def;
Theorem copyout'_side:
!xlist dlist gsl ss ss_curr. copyout'_side xlist dlist gsl ss ss_curr
Proof
simp[Once $ definition "copyout'_side_def"] \\
rpt strip_tac >- (
 gs[oTAKE_TAKE]
) \\
gs[oDROP_DROP]
QED
val _ = update_precondition copyout'_side;
val _ = translate frames_exec'_def;

val _ = ml_prog_update (close_module NONE);

val _ = export_theory ();
