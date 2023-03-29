open HolKernel boolLib Parse bossLib;

val _ = new_theory "p4_refinementScript";

open p4Theory p4_auxTheory p4_exec_semTheory;

(* Not immediately clear how to update the extern maps - cannot do this with statement? *)
(* TODO: State an equivalence relation instead *)
Definition update_funn_body_def:
 update_funn_body (apply_table_f, ext_map, func_map, b_func_map, pars_map, tbl_map) funn stmt' = 
  case funn of
    funn_name x =>
      (case ALOOKUP b_func_map x of
         NONE =>
           (case ALOOKUP func_map x of
              NONE => NONE
            | SOME (stmt,x_d_l) =>
             SOME (apply_table_f, ext_map, AUPDATE func_map (x, (stmt', x_d_l)), b_func_map, pars_map, tbl_map))
       | SOME (stmt,x_d_l) =>
        SOME (apply_table_f, ext_map, func_map, AUPDATE b_func_map (x, (stmt', x_d_l)), pars_map, tbl_map))
  | _ => NONE
End

(* Limited to updating function bodies in global and block-local function maps for now *)
(* TODO: Use abstract semantics instead of exec *)
Theorem thm1:
!(f:funn) (frame_list:frame_list) frame_0 frame_list' (func_map:func_map) (b_func_map:b_func_map) (ext_map:'a ext_map) stmt stmt' params
 (ctx:'a ctx) ctx' (ascope:'a) ascope' (g_scope_list:g_scope_list) g_scope_list' status.
f NOTIN (set $ (MAP FST) frame_list) /\
lookup_funn_sig_body f func_map b_func_map ext_map = SOME (stmt, params) /\
frames_exec ctx ((ascope, g_scope_list, frame_list, status):'a state) =
 SOME (ascope', g_scope_list', (frame_0::frame_list'), status') ==>
update_funn_body ctx f stmt' = SOME ctx' ==>
?frame_0' scope_list.
frames_exec ctx' ((ascope, g_scope_list, frame_list, status):'a state) =
 SOME (ascope', g_scope_list', (frame_0'::frame_list'), status') /\
(f <> (FST frame_0) ==> frame_0' = frame_0) /\
(f = FST frame_0 ==> (frame_0 = (f, [stmt], scope_list)) /\ (frame_0' = (f, [stmt'], scope_list)))
Proof
(* Case analysis on the rule *)
(* Return or regular, regular would need stmt-level reasoning, but most do not use env, so OK -
 * but this could be factored out into separate lemma *)
QED

(* TODO: "Decomposition theorem" *)
Theorem thm2:
T
Proof
cheat
QED


val _ = export_theory ();
