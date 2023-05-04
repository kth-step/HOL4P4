open HolKernel boolLib liteLib simpLib Parse bossLib;

open p4Theory;

val _ = new_theory "p4_stf";

(* TODO: Do all of these operations in petr4_to_hol4p4.sml directly instead of in every lifted Script file? *)

Definition p4_replace_tbl_default_def:
 p4_replace_tbl_default (ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map) block_name table_name action_name args =
  case ALOOKUP pblock_map block_name of
  | SOME (pblock_regular pbl_type_control ctrl_params b_func_map decl_list body ([]:pars_map) tbl_map) =>
   (case ALOOKUP tbl_map table_name of
    | SOME (mk_l, (old_action_name, old_args)) =>
     SOME (ab_list, AUPDATE pblock_map (block_name, (pblock_regular pbl_type_control ctrl_params b_func_map decl_list body ([]:pars_map) (AUPDATE tbl_map (table_name, (mk_l, (action_name, args)))))),
             ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map)
    | NONE => NONE)
  | _ => NONE
End

Definition ebpf_add_ctrl_def:
 ebpf_add_ctrl (((i, in_out_list, in_out_list', (counter, ext_obj_map, v_map, ctrl)), g_scope_list, scope_list, status):ebpf_ascope astate) table_name keys action_name args =
  case ALOOKUP ctrl table_name of
  | SOME table => SOME ((i, in_out_list, in_out_list', (counter, ext_obj_map, v_map, AUPDATE ctrl (table_name, (AUPDATE table (keys, (action_name, args)))))), g_scope_list, scope_list, status)
  | NONE => NONE
End

Definition vss_add_ctrl_def:
 vss_add_ctrl (((i, in_out_list, in_out_list', (counter, ext_obj_map, v_map, ctrl)), g_scope_list, scope_list, status):vss_ascope astate) table_name keys action_name args =
  case ALOOKUP ctrl table_name of
  | SOME table => SOME ((i, in_out_list, in_out_list', (counter, ext_obj_map, v_map, AUPDATE ctrl (table_name, (AUPDATE table (keys, (action_name, args)))))), g_scope_list, scope_list, status)
  | NONE => NONE
End

(* TODO: Fix duplication *)
Definition v1model_add_ctrl_def:
 v1model_add_ctrl (((i, in_out_list, in_out_list', (counter, ext_obj_map, v_map, ctrl)), g_scope_list, scope_list, status):v1model_ascope astate) table_name keys action_name args =
  case ALOOKUP ctrl table_name of
  | SOME table => SOME ((i, in_out_list, in_out_list', (counter, ext_obj_map, v_map, AUPDATE ctrl (table_name, (AUPDATE table (keys, (action_name, args)))))), g_scope_list, scope_list, status)
  | NONE => NONE
End

val _ = export_theory ();
