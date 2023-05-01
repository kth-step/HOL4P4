open HolKernel boolLib liteLib simpLib Parse bossLib;

open p4Theory;

val _ = new_theory "p4_stf";

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

val _ = export_theory ();
