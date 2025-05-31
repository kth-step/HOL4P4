open HolKernel boolLib liteLib simpLib Parse bossLib;

open p4Theory;

val _ = new_theory "p4_arch_aux";

(* This file contains all architecture-specific definitions that are used for importing to HOL4P4.
 * None of these should be found in imported Script files or used by the semantics *)


(* Adding entries to tables *)

Definition add_ctrl_gen_def:
 add_ctrl_gen (((i, in_out_list, in_out_list', (counter:num, ext_obj_map:(num, (core_v_ext, 'a) sum) alist, v_map:(string, v) alist, ctrl:(string, (((e_list -> bool) # num), string # e_list) alist) alist)), g_scope_list, scope_list, status)) table_name keys action_name args =
  case ALOOKUP ctrl table_name of
  (* TODO: Note that this does not have any capability of removing old keys, only supersede them *)
  | SOME table => SOME ((i, in_out_list, in_out_list', (counter, ext_obj_map, v_map, AUPDATE ctrl (table_name, ((keys, (action_name, args))::table)))), g_scope_list, scope_list, status)
  | NONE => NONE
End

Definition ebpf_add_ctrl_def:
 ebpf_add_ctrl (astate:ebpf_ascope astate) =
  add_ctrl_gen astate
End

Definition vss_add_ctrl_def:
 vss_add_ctrl (astate:vss_ascope astate) =
  add_ctrl_gen astate
End

Definition v1model_add_ctrl_def:
 v1model_add_ctrl (astate:v1model_ascope astate) =
  add_ctrl_gen astate
End

(* Replaces the default action of a table. Used when parsing STF specifications *)
Definition p4_replace_tbl_default_def:
 p4_replace_tbl_default (ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map) block_name table_name action_name args =
  case ALOOKUP pblock_map block_name of
  | SOME (pbl_type_control, params, b_func_map, decl_list, ([]:pars_map), tbl_map) =>
   (case ALOOKUP tbl_map table_name of
    | SOME (mk_l, (old_action_name, old_args)) =>
     SOME (ab_list, AUPDATE pblock_map (block_name, (pbl_type_control, params, b_func_map, decl_list, ([]:pars_map), (AUPDATE tbl_map (table_name, (mk_l, (action_name, args)))))),
             ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map)
    | NONE => NONE)
  | _ => NONE
End

val _ = export_theory ();
