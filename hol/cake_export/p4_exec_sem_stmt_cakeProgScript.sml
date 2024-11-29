open HolKernel boolLib Parse bossLib;

val _ = new_theory "p4_exec_sem_stmt_cakeProg";

open p4Syntax;
open p4Theory;
open p4_auxTheory;
open p4_exec_semTheory;

(* CakeML: *)
open preamble ml_translatorLib ml_translatorTheory ml_progLib basisProgTheory mlmapTheory basisFunctionsLib
     astPP comparisonTheory;

open p4_exec_sem_e_cakeProgTheory;

intLib.deprecate_int();
val _ = (max_print_depth := 100);

(* Same as regular state, but doesn't clash with state in semanticPrimitivesTheory *)
Type state' = “:('a # g_scope_list # frame_list # status)”

Definition get_e_ctx_def:
 get_e_ctx ((apply_table_f, ext_map, func_map, b_func_map, pars_map, tbl_map):'a ctx) = (ext_map, func_map, b_func_map)
End

(* TODO: This function initialises everything to zeroes instead of using ARBs,
 * which are not compatible with CakeML. Use this as a placeholder before you have
 * deep-embedded uninitialised values. *)
Definition init_v_from_tau_cake_def:
 (init_v_from_tau_cake tau_bool = v_bool F) /\
 (init_v_from_tau_cake (tau_bit w) = v_bit (GENLIST (\x. F) w, w)) /\
 (init_v_from_tau_cake tau_bot = v_bot) /\
 (init_v_from_tau_cake tau_ext = v_ext_ref 0) /\
 (init_v_from_tau_cake (tau_xtl struct_ty_struct []) = v_struct []) /\
 (init_v_from_tau_cake (tau_xtl struct_ty_struct ((x0,t0)::xtl)) =
  v_struct ((x0, init_v_from_tau_cake t0)::(MAP (\(x,t). (x, init_v_from_tau_cake t)) xtl))) /\
 (init_v_from_tau_cake (tau_xtl struct_ty_header [] ) = v_header F [] ) /\
 (init_v_from_tau_cake (tau_xtl struct_ty_header ((x0,t0)::xtl)) =
   v_header F ((x0, init_v_from_tau_cake t0)::(MAP (\(x,t). (x, init_v_from_tau_cake t)) xtl)))
Termination
wf_rel_tac `measure tau_size`
End

Definition declare_list_in_fresh_scope'_def:
 declare_list_in_fresh_scope' (t_scope:t_scope) =
  MAP (\(x, (t, lvalop)). (x, (init_v_from_tau_cake t, NONE))) t_scope
End

(* Puts the bits in bl1 between index hi and lo of bl2. *)
Definition replace_bits_def:
 replace_bits (bl1, (n1:num)) (bl2,n2) hi lo =
  if lo <= hi /\ hi < n2 /\ LENGTH bl2 = n2
  then
   SOME $ (SEG (n2-(hi+1)) 0 bl2) ++ bl1 ++ (SEG lo (n2-lo) bl2)
  else NONE
End

Definition assign_to_slice'_def:
 assign_to_slice' vb vb' ev1 ev2 =
  (case ev1 of
   | (e_v (v_bit (bl1, n1))) =>
    (case ev2 of
     | (e_v (v_bit (bl2, n2))) =>
      (case replace_bits vb vb' (v2n bl1) (v2n bl2) of
       | SOME bitv =>
        SOME $ v_bit (bitv, SND vb')
       | NONE => NONE)
     | _ => NONE)
   | _ => NONE)
End

Definition assign'_def:
 (assign' ss v (lval_varname x) =
  case find_topmost_map ss x of
  | SOME (i, sc) =>
   (case lookup_out ss x of
    | SOME str_opt =>
      SOME (LUPDATE (AUPDATE sc (x, (v, str_opt))) i ss)
    | NONE => NONE)
  | _ => NONE) /\
 (assign' ss v (lval_field lval f) =
  case lookup_lval' ss lval of
  | SOME (v_struct f_v_l) =>
   (case INDEX_OF f (MAP FST f_v_l) of
    | SOME i => assign' ss (v_struct (LUPDATE (f, v) i f_v_l)) lval
    | NONE => NONE)
  | SOME (v_header validity f_v_l) =>
   (case INDEX_OF f (MAP FST f_v_l) of
    | SOME i => assign' ss (v_header validity (LUPDATE (f, v) i f_v_l)) lval
    | NONE => NONE)
   | _ => NONE) /\    
 (assign' ss v (lval_slice lval ev1 ev2) =
  case v of
  | v_bit vb =>
   (case lookup_lval' ss lval of
    | SOME (v_bit vb') =>
     (case assign_to_slice' vb vb' ev1 ev2 of
      | SOME v_res => assign' ss v_res lval
      | _ => NONE)
    | _ => NONE)
  | _ => NONE) /\
 (assign' ss v lval_null = SOME ss) /\
 (assign' ss v (lval_paren lval) = assign' ss v lval)
End

Definition stmt_exec_ass'_def:
 (stmt_exec_ass' lval (e_v v) ss = assign' ss v lval) /\
 (stmt_exec_ass' _ _ _ = NONE)
End

Definition stmt_exec'_def:
 (******************************************)
 (* Catch-all clauses for special statuses *)
 (stmt_exec' (ctx:'a ctx) ((ascope:'a, g_scope_list:g_scope_list, frame_list:frame_list, status_returnv v):'a state') = NONE)
  /\
 (stmt_exec' _ (_, _, _, status_trans x) = NONE)
  /\
 (* Empty frame list *)
 (stmt_exec' _ (_, _, [], _) = NONE)
  /\
 (* Empty scope stack *)
 (stmt_exec' _ (_, _, [(funn, stmt_stack, [])], _) = NONE)
  /\
 (**************)
 (* Assignment *)
 (stmt_exec' ctx (ascope, g_scope_list, [(funn, [stmt_ass lval e], scope_list)], status_running) =
  if is_v e
  then
   (case stmt_exec_ass' lval e (scope_list++g_scope_list) of
    | SOME scope_list'' =>
     (case separate scope_list'' of
      | (SOME g_scope_list', SOME scope_list') =>
       SOME (ascope, g_scope_list', [(funn, [stmt_empty], scope_list')], status_running)
      | _ => NONE)
    | NONE => NONE)
  else
   (case e_exec' (get_e_ctx ctx) g_scope_list scope_list e of
    | SOME (e', frame_list) =>
     SOME (ascope, g_scope_list, frame_list++[(funn, [stmt_ass lval e'], scope_list)], status_running)
    | _ => NONE))
  /\
 (**************)
 (* Transition *)
 (stmt_exec' ctx (ascope, g_scope_list, [(funn, [stmt_trans e], scope_list)], status_running) =
  if is_v e
  then
   if is_v_str e
   then
    (case stmt_exec_trans e of
     | SOME status' => SOME (ascope, g_scope_list, [(funn, [stmt_empty], scope_list)], status')
     | NONE => NONE)
    else NONE
  else
   (case e_exec' (get_e_ctx ctx) g_scope_list scope_list e of
    | SOME (e', frame_list) =>
     SOME (ascope, g_scope_list, frame_list++[(funn, [stmt_trans e'], scope_list)], status_running)
    | NONE => NONE))
  /\
 (***************)
 (* Conditional *)
 (stmt_exec' ctx (ascope, g_scope_list, [(funn, [stmt_cond e stmt1 stmt2], scope_list)], status_running) =
  (* TODO: Make this more efficient by using a single get_v_bool e *)
  if is_v_bool e
  then
   (case stmt_exec_cond e of
    | SOME T => SOME (ascope, g_scope_list, [(funn, [stmt1], scope_list)], status_running)
    | SOME F => SOME (ascope, g_scope_list, [(funn, [stmt2], scope_list)], status_running)
    | NONE => NONE)
  else
   (case e_exec' (get_e_ctx ctx) g_scope_list scope_list e of
    | SOME (e', frame_list) =>
     SOME (ascope, g_scope_list, frame_list++[(funn, [stmt_cond e' stmt1 stmt2], scope_list)], status_running)
    | NONE => NONE))
  /\
 (*********************)
 (* Table application *)
 (stmt_exec' (apply_table_f, ext_map, func_map, b_func_map, pars_map, tbl_map) (ascope, g_scope_list, [(funn, [stmt_app t_name e_l], scope_list)], status_running) =
  (case index_not_const e_l of
   | SOME i =>
    (case oEL i e_l of
     | SOME elem =>
      (case e_exec' (ext_map, func_map, b_func_map) g_scope_list scope_list elem of
       | SOME (e', frame_list) =>
        SOME (ascope, g_scope_list, frame_list++[(funn, [stmt_app t_name (LUPDATE e' i e_l)], scope_list)], status_running)
       | NONE => NONE)
     | NONE => NONE)
   | NONE =>
    (case ALOOKUP tbl_map t_name of
     | SOME (mk_l, (default_f, default_f_args)) =>
      (if LENGTH mk_l = LENGTH e_l
       then
        (case apply_table_f (t_name, e_l, mk_l, (default_f, default_f_args), ascope) of
         | SOME (f, f_args) =>
          (if is_consts_exec f_args
           then
            SOME (ascope, g_scope_list, [(funn, [stmt_ass lval_null (e_call (funn_name f) f_args)], scope_list)], status_running)
           else NONE)
         | NONE => NONE)
       else NONE)
     | NONE => NONE)))
  /\
 (**********)
 (* Return *)
 (stmt_exec' ctx (ascope, g_scope_list, [(funn, [stmt_ret e], scope_list)], status_running) =
  (case get_v e of
   | SOME v => SOME (ascope, g_scope_list, [(funn, [stmt_empty], scope_list)], status_returnv v)
   | NONE => 
    (case e_exec' (get_e_ctx ctx) g_scope_list scope_list e of
     | SOME (e', frame_list) =>
      SOME (ascope, g_scope_list, frame_list++[(funn, [stmt_ret e'], scope_list)], status_running)
     | NONE => NONE)))
  /\
 (**********)
 (* Extern *)
 (stmt_exec' (apply_table_f, ext_map, func_map, b_func_map, pars_map, tbl_map) (ascope, g_scope_list, [(funn, [stmt_ext], scope_list)], status_running) =
  (case lookup_ext_fun funn ext_map of
   | SOME ext_fun =>
    (case ext_fun (ascope, g_scope_list, scope_list) of
     | SOME (ascope', scope_list', status') =>
      SOME (ascope', g_scope_list, [(funn, [stmt_empty], scope_list')], status')
     | NONE => NONE)
   | NONE => NONE))
  /\
 (*********)
 (* Block *)
 (stmt_exec' ctx (ascope, g_scope_list, [(funn, [stmt_block decl_list stmt], scope_list)], status_running) =
   SOME (ascope, g_scope_list, [(funn, [stmt]++[stmt_empty], ((declare_list_in_fresh_scope' decl_list)::scope_list))], status_running))
  /\
 (************)
 (* Sequence *)
 (stmt_exec' ctx (ascope, g_scope_list, [(funn, [stmt_seq stmt1 stmt2], scope_list)], status_running) =
  if is_empty stmt1
  then SOME (ascope, g_scope_list, [(funn, [stmt2], scope_list)], status_running)
  else
   (* Note: this only allows for 0 or 1 frame being added, or (exclusively) 1 stmt element *)
   (case stmt_exec' ctx (ascope, g_scope_list, [(funn, [stmt1], scope_list)], status_running) of
    | SOME (ascope', g_scope_list', [(funn, [stmt1'], scope_list')], status') =>
     (case status' of 
      | status_running =>
       SOME (ascope', g_scope_list', [(funn, [stmt_seq stmt1' stmt2], scope_list')], status_running)
      | _ =>
       SOME (ascope', g_scope_list', [(funn, [stmt1'], scope_list')], status'))
    | SOME (ascope', g_scope_list', [(funn, stmt1''::[stmt1'], scope_list')], status_running) =>
     SOME (ascope', g_scope_list', [(funn, [stmt1'']++[stmt_seq stmt1' stmt2], scope_list')], status_running)
    | SOME (ascope', g_scope_list', (frame::[(funn, [stmt1'], scope_list')]), status_running) =>
     SOME (ascope', g_scope_list', (frame::[(funn, [stmt_seq stmt1' stmt2], scope_list')]), status_running)
    | _ => NONE))
  /\
 (*********************)
 (* Stmt stack clause *)
 (*********************)
 (* TODO: Should the case statement be handled by better matching in the clause? *)
 (stmt_exec' ctx (ascope, g_scope_list, [(funn, stmt_empty::stmt_stack, scope_list)], status) =
  case stmt_stack of
  | [] => NONE
  | _ =>
   (case scope_list of
    | [] => NONE
    | (h_scope::scope_list') => SOME (ascope, g_scope_list, [(funn, stmt_stack, TL (h_scope::scope_list'))], status)))
  /\
 (* TODO: This clause gets expanded into multiple clauses to account for all different
  *       statements. An alternative solution, which may be even more convoluted,
  *       could be to make mutually recursive functions *)
 (stmt_exec' ctx (ascope, g_scope_list, [(funn, stmt::stmt_stack, scope_list)], status) =
   (case stmt_exec' ctx (ascope, g_scope_list, [(funn, [stmt], scope_list)], status) of
   | SOME (ascope', g_scope_list', frame_list', status') =>
    (case frame_list' of
     (* Regular case *)
     | [(funn, [stmt'], scope_list')] =>
      SOME (ascope', g_scope_list', [(funn, stmt'::stmt_stack, scope_list')], status')
     (* Block entry *)
     | [(funn, stmt''::[stmt'], scope_list')] =>
      SOME (ascope', g_scope_list', [(funn, stmt''::(stmt'::stmt_stack), scope_list')], status')
     (* Function call *)
     | ((funn', [stmt'], scope_list')::[(funn, [stmt''], scope_list)]) =>
      SOME (ascope', g_scope_list', ((funn', [stmt'], scope_list')::[(funn, stmt''::stmt_stack, scope_list)]), status')
     (* TODO: What can happen here? *)
     | _ => NONE)
   | NONE => NONE))
  /\
 (stmt_exec' _ _ = NONE)
End

val _ = translation_extends "p4_exec_sem_e_cakeProg";

val _ = ml_prog_update (open_module "p4_exec_sem_stmt_cake");

(**************)
(* Assignment *)
val _ = translate lookup_out_def;
val _ = translate listTheory.INDEX_OF_def;
val _ = translate replace_bits_def;
Theorem replace_bits_side:
!bitv1 bitv2 hi lo. replace_bits_side bitv1 bitv2 hi lo
Proof
simp[Once $ definition "replace_bits_side_def"]
QED
val _ = update_precondition replace_bits_side;
val _ = translate assign_to_slice'_def;
val _ = translate assign'_def;
val _ = translate stmt_exec_ass'_def;
val _ = translate oDROP_def;
val _ = translate oTAKE_def;
val _ = translate separate_def;
val _ = translate get_e_ctx_def;

(***************)
(* Conditional *)
val _ = translate is_v_bool_def;
val _ = translate stmt_exec_cond_def;

(*********)
(* Block *)
val _ = translate init_v_from_tau_cake_def;
val _ = translate declare_list_in_fresh_scope'_def;

(**********)
(* Return *)
val _ = translate get_v_def;

(************)
(* Sequence *)
val _ = translate is_empty_def;

(**************)
(* Transition *)
val _ = translate is_v_str_def;
val _ = translate stmt_exec_trans_def;

(*********)
(* Apply *)
val _ = translate index_not_const_def;
val _ = translate is_consts_exec_def;

(**********)
(* Extern *)
val _ = translate lookup_ext_fun_def;

val _ = translate stmt_exec'_def;

val _ = ml_prog_update (close_module NONE);

val _ = export_theory ();
