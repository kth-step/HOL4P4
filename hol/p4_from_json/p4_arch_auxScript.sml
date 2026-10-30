Theory p4_arch_aux
Ancestors
  p4 p4_core p4_ebpf p4_v1model p4_vss

(* Architecture-specific control-plane updates used by the import and by imported Script files *)

(* Adding entries to tables *)

Definition add_ctrl_gen_def:
 add_ctrl_gen (((i, in_out_list, in_out_list', (counter:num, ext_obj_map:(num, (core_v_ext, 'a) sum) alist, v_map:(string, v) alist, ctrl:(string, (((e_list -> bool) # num), string # e_list) alist) alist, oracle_index:num)), g_scope_list:scope list, scope_list:arch_frame_list, status:status)) table_name keys action_name args =
  case ALOOKUP ctrl table_name of
  (* TODO: Note that this does not have any capability of removing old keys, only supersede them *)
  | SOME table => SOME ((i, in_out_list, in_out_list', (counter, ext_obj_map, v_map, AUPDATE ctrl (table_name, ((keys, (action_name, args))::table)), oracle_index)), g_scope_list, scope_list, status)
  | NONE => NONE
End

Definition add_ctrl_list_gen_def:
 (add_ctrl_list_gen astate [] = SOME astate) /\
 (add_ctrl_list_gen astate ((table_name, keys, action_name, args)::t) =
  case add_ctrl_gen astate table_name keys action_name args of
  | SOME astate' => add_ctrl_list_gen astate' t
  | NONE => NONE)
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
 v1model_add_ctrl (((i, in_out_list, in_out_list', (counter, ext_obj_map, v_map, (tables, groups), oracle_index)), g_scope_list, scope_list, status):v1model_ascope astate) table_name keys action_name args =
  case ALOOKUP tables table_name of
  | SOME table => SOME ((i, in_out_list, in_out_list', (counter, ext_obj_map, v_map, (AUPDATE tables (table_name, ((keys, (action_name, args))::table)), groups), oracle_index)), g_scope_list, scope_list, status)
  | NONE => NONE
End

Definition v1model_add_ctrl_list_def:
 (v1model_add_ctrl_list astate [] = SOME astate) /\
 (v1model_add_ctrl_list astate ((table_name, keys, action_name, args)::t) =
  case v1model_add_ctrl astate table_name keys action_name args of
  | SOME astate' => v1model_add_ctrl_list astate' t
  | NONE => NONE)
End

(* Multicast groups *)

Definition v1model_mc_mgrp_create_def:
 v1model_mc_mgrp_create (((i, in_out_list, in_out_list', (counter, ext_obj_map, v_map, (tables, groups), oracle_index)), g_scope_list, scope_list, status):v1model_ascope astate) g =
  case ALOOKUP groups g of
  | SOME _ => SOME ((i, in_out_list, in_out_list', (counter, ext_obj_map, v_map, (tables, groups), oracle_index)), g_scope_list, scope_list, status)
  | NONE => SOME ((i, in_out_list, in_out_list', (counter, ext_obj_map, v_map, (tables, AUPDATE groups (g, [])), oracle_index)), g_scope_list, scope_list, status)
End

Definition v1model_mc_associate_def:
 v1model_mc_associate (((i, in_out_list, in_out_list', (counter, ext_obj_map, v_map, (tables, groups), oracle_index)), g_scope_list, scope_list, status):v1model_ascope astate) g copies =
  case ALOOKUP groups g of
  | SOME copies' => SOME ((i, in_out_list, in_out_list', (counter, ext_obj_map, v_map, (tables, AUPDATE groups (g, copies'++copies)), oracle_index)), g_scope_list, scope_list, status)
  | NONE => NONE
End
