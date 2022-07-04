open HolKernel boolLib Parse bossLib;

val _ = new_theory "p4_exec_sem";

open p4Syntax;
open ottTheory;
open p4Theory p4_auxTheory;

(*********************************)
(* Expression-related shorthands *)

Definition is_v:
 (is_v (e_v v) = T) /\
 (is_v _ = F)
End

Definition get_v:
 (get_v (e_v v) = SOME v) /\
 (get_v _ = NONE)
End

Definition is_v_bool:
 (is_v_bool (e_v (v_bool b)) = T) /\
 (is_v_bool _ = F)
End

Definition is_v_err:
 (is_v_err (e_v (v_err x)) = T) /\
 (is_v_err _ = F)
End

Definition is_v_str:
 (is_v_str (e_v (v_str x)) = T) /\
 (is_v_str _ = F)
End

Definition is_var:
 (is_var (e_var x) = T) /\
 (is_var _ = F)
End

Definition unop_exec:
 (unop_exec unop_neg (v_bool b) = SOME (v_bool ~b))
 /\
 (unop_exec unop_compl (v_bit bitv) = SOME (v_bit (bitv_bl_unop bnot bitv)))
 /\
 (unop_exec unop_neg_signed (v_bit bitv) = SOME (v_bit (bitv_unop unop_neg_signed bitv)))
 /\
 (unop_exec unop_un_plus (v_bit bitv) = SOME (v_bit bitv))
 /\
 (unop_exec unop v = NONE)
End

Definition e_exec_unop:
 (e_exec_unop unop (e_v v) = unop_exec unop v)
  /\
 (e_exec_unop _ _ = NONE)
End

(* TODO: Split binop into binop, binpred, ... to reduce copypaste? *)
Definition binop_exec:
 (binop_exec binop_mul (v_bit bitv1) (v_bit bitv2) =
  case bitv_binop binop_mul bitv1 bitv2 of
  | SOME bitv3 => SOME (v_bit bitv3)
  | NONE => NONE)
 /\
 (binop_exec binop_div (v_bit bitv1) (v_bit bitv2) =
  case bitv_binop binop_div bitv1 bitv2 of
  | SOME bitv3 => SOME (v_bit bitv3)
  | NONE => NONE)
 /\
 (binop_exec binop_mod (v_bit bitv1) (v_bit bitv2) =
  case bitv_binop binop_mod bitv1 bitv2 of
  | SOME bitv3 => SOME (v_bit bitv3)
  | NONE => NONE)
 /\
 (binop_exec binop_add (v_bit bitv1) (v_bit bitv2) =
  case bitv_binop binop_add bitv1 bitv2 of
  | SOME bitv3 => SOME (v_bit bitv3)
  | NONE => NONE)
 /\
 (binop_exec binop_sub (v_bit bitv1) (v_bit bitv2) =
  case bitv_binop binop_sub bitv1 bitv2 of
  | SOME bitv3 => SOME (v_bit bitv3)
  | NONE => NONE)
 /\
 (binop_exec binop_shl (v_bit bitv1) (v_bit bitv2) =
  SOME (v_bit (bitv_bl_binop shiftl bitv1 ((\(bl, n). (v2n bl, n)) bitv2))))
 /\
 (binop_exec binop_shr (v_bit bitv1) (v_bit bitv2) =
  SOME (v_bit (bitv_bl_binop shiftr bitv1 ((\(bl, n). (v2n bl, n)) bitv2))))
 /\
 (binop_exec binop_le (v_bit bitv1) (v_bit bitv2) =
  case bitv_binpred binop_le bitv1 bitv2 of
  | SOME b => SOME (v_bool b)
  | NONE => NONE)
 /\
 (binop_exec binop_ge (v_bit bitv1) (v_bit bitv2) =
  case bitv_binpred binop_ge bitv1 bitv2 of
  | SOME b => SOME (v_bool b)
  | NONE => NONE)
 /\
 (binop_exec binop_lt (v_bit bitv1) (v_bit bitv2) =
  case bitv_binpred binop_lt bitv1 bitv2 of
  | SOME b => SOME (v_bool b)
  | NONE => NONE)
 /\
 (binop_exec binop_gt (v_bit bitv1) (v_bit bitv2) =
  case bitv_binpred binop_gt bitv1 bitv2 of
  | SOME b => SOME (v_bool b)
  | NONE => NONE)
 /\
 (* TODO: This would generalize easily in theory, but
  * gives rise to enormously many autogenerated cases *)
 (binop_exec binop_neq (v_bit bitv1) (v_bit bitv2) =
  SOME (v_bool (bitv1 <> bitv2)))
 /\
 (binop_exec binop_neq (v_bool b1) (v_bool b2) =
  SOME (v_bool (b1 <> b2)))
 /\
 (binop_exec binop_neq (v_err x1) (v_err x2) =
  SOME (v_bool (x1 <> x2)))
 /\
 (binop_exec binop_eq (v_bit bitv1) (v_bit bitv2) =
  SOME (v_bool (bitv1 = bitv2)))
 /\
 (binop_exec binop_eq (v_bool b1) (v_bool b2) =
  SOME (v_bool (b1 = b2)))
 /\
 (binop_exec binop_eq (v_err x1) (v_err x2) =
  SOME (v_bool (x1 = x2)))
 /\
 (binop_exec binop_and (v_bit bitv1) (v_bit bitv2) =
  SOME (v_bit (bitv_bl_binop band bitv1 bitv2)))
 /\
 (binop_exec binop_xor (v_bit bitv1) (v_bit bitv2) =
  SOME (v_bit (bitv_bl_binop bxor bitv1 bitv2)))
 /\
 (binop_exec binop_or (v_bit bitv1) (v_bit bitv2) =
  SOME (v_bit (bitv_bl_binop bor bitv1 bitv2)))
 /\
 (binop_exec binop v1 v2 = NONE)
End

Definition e_exec_binop:
 (e_exec_binop (e_v v1) binop (e_v v2) = binop_exec binop v1 v2)
  /\
 (e_exec_binop _ _ _ = NONE)
End

Definition e_exec_short_circuit:
 (e_exec_short_circuit (v_bool T) binop_bin_and e = SOME e)
  /\
 (e_exec_short_circuit (v_bool F) binop_bin_and e = SOME (e_v (v_bool F)))
  /\
 (e_exec_short_circuit (v_bool T) binop_bin_or e = SOME (e_v (v_bool T)))
  /\
 (e_exec_short_circuit (v_bool F) binop_bin_or e = SOME e)
  /\
 (e_exec_short_circuit _ _ _ = NONE)
End

(* Field access *)
Definition e_exec_acc:
 (e_exec_acc (e_acc (e_v (v_struct f_v_list)) f) =
  case FIND (\(k, v). k = f) f_v_list of
  | SOME (f, v) => SOME (e_v v)
  | NONE => NONE)
  /\
 (e_exec_acc (e_acc (e_v (v_header boolv f_v_list)) f) =
  case FIND (\(k, v). k = f) f_v_list of
  | SOME (f, v) => SOME (e_v v)
  | NONE => NONE)
  /\
 (e_exec_acc _ = NONE)
End

Definition e_exec_select:
 (e_exec_select (e_v v) v_x_l x =
  case FIND (\(v', x'). v' = v) v_x_l of
  | SOME (v', x') => SOME x'
  | NONE => SOME x)
  /\
 (e_exec_select _ _ _ = NONE)
End

(********************************)
(* Statement-related shorthands *)

Definition is_empty:
 (is_empty stmt_empty = T) /\
 (is_empty _ = F)
End

Definition get_ret_v:
 (get_ret_v (stmt_ret (e_v v)) = SOME v) /\
 (get_ret_v (stmt_seq (stmt_ret (e_v v)) stmt) = SOME v) /\
 (get_ret_v _ = NONE)
End

Definition stmt_exec_ass:
 (stmt_exec_ass lval (e_v v) ss =
  assign ss v lval)
  /\
 (stmt_exec_ass _ _ _ = NONE)
End

Definition stmt_exec_init:
 (stmt_exec_init varn (e_v v) ss = initialise ss varn v)
End

Definition stmt_exec_verify:
 (stmt_exec_verify (e_v (v_bool T)) (e_v (v_err x)) =
  SOME stmt_empty)
  /\
 (stmt_exec_verify (e_v (v_bool F)) (e_v (v_err x)) =
  SOME (stmt_seq (stmt_ass (lval_varname (varn_name "parseError")) ((e_v (v_err x)))) (stmt_trans (e_v (v_str "reject")))))
  /\
 (stmt_exec_verify _ _ = NONE)
End

Definition stmt_exec_trans:
 (stmt_exec_trans (e_v (v_str x)) =
  if x = "accept"
  then SOME (status_pars_next (pars_next_pars_fin pars_finaccept))
  else if x = "reject"
  then SOME (status_pars_next (pars_next_pars_fin pars_finreject))
  else SOME (status_pars_next (pars_next_trans x)))
  /\
 (stmt_exec_trans _ = NONE)
End

Definition stmt_exec_cond:
 (stmt_exec_cond (e_v (v_bool T)) =
  SOME T)
  /\
 (stmt_exec_cond (e_v (v_bool F)) =
  SOME F)
  /\
 (stmt_exec_cond _ = NONE)
End

val e_state_size_def = Define `
 (e_state_size ((ctx:ctx), (g_scope_list:g_scope_list), (scopes_stack:scopes_stack), (e:e)) = e_size e)
`;

(* TODO: Write explicit NONE-reducing clauses for operands of wrong types?
 *       This would reduce warnings *)
(* TODO: Use let-statements to avoid duplicate "MAP FST", et cetera *)
val e_exec = TotalDefn.tDefine "e_exec" `
 (********************)
 (* Variable look-up *)
 (e_exec (ctx:ctx) (g_scope_list:g_scope_list) (scopes_stack:scopes_stack) (e_var x) =
  case lookup_vexp2 scopes_stack g_scope_list x of
  | SOME v => SOME (e_v v, [])
  | NONE => NONE)
  /\
 (******************************)
 (* Struct/header field access *)
 (e_exec ctx g_scope_list scopes_stack (e_acc e_v_struct x) =
  if is_v e_v_struct
  then
   (case e_exec_acc (e_acc e_v_struct x) of
    | SOME v => SOME (v, [])
    | NONE => NONE)
  else NONE)
(* TODO: What happens if one tries to access an expression?
   else
    (case e_exec ctx g_scope_list scopes_stack e_v_struct of
     | SOME (e_v_struct', frame_list) =>
      SOME (e_acc e_v_struct' x, frame_list)
     | NONE => NONE))
*)
  /\
 (******************************)
 (* Struct/header field reduction *)
 (e_exec ctx g_scope_list scopes_stack (e_struct x_e_l) =
  case unred_mem_index (MAP SND x_e_l) of
  | SOME i =>
   (case e_exec ctx g_scope_list scopes_stack (EL i (MAP SND x_e_l)) of
    | SOME (e', frame_list) => SOME (e_struct (ZIP (MAP FST x_e_l, (LUPDATE e' i (MAP SND x_e_l)))), frame_list)
    | NONE => NONE)
  | NONE => SOME (e_v (v_struct (ZIP (MAP FST x_e_l, vl_of_el (MAP SND x_e_l)))), []))
  /\
 (************************)
 (* Function/extern call *)
 (e_exec (ext_map, func_map, tbl_map) g_scope_list scopes_stack (e_call funn e_l) =
  (case lookup_funn_sig_body funn func_map ext_map of
    | SOME (stmt, x_d_l) =>
     if LENGTH x_d_l = LENGTH e_l
     then
      (case unred_arg_index (MAP SND x_d_l) e_l of
       | SOME i =>
        (case e_exec (ext_map, func_map, tbl_map) g_scope_list scopes_stack (EL i e_l) of
         | SOME (e', frame_list) => SOME (e_call funn (LUPDATE e' i e_l), frame_list)
         | NONE => NONE)
       | NONE =>
        (case copyin (MAP FST x_d_l) (MAP SND x_d_l) e_l g_scope_list scopes_stack of
         | SOME scope => 
          SOME (e_var varn_star, [(funn, stmt, [scope])])
         | NONE => NONE))
     else NONE
    | NONE => NONE))
  /\
 (********************)
 (* Unary arithmetic *)
 (e_exec ctx g_scope_list scopes_stack (e_unop unop e) =
  if is_v e
  then 
   (case e_exec_unop unop e of
    | SOME v => SOME (e_v v, [])
    | NONE => NONE)
  else
   (case e_exec ctx g_scope_list scopes_stack e of
    | SOME (e', frame_list) => SOME (e_unop unop e', frame_list)
    | NONE => NONE))
  /\
 (*********************)
 (* Binary arithmetic *)
 (e_exec ctx g_scope_list scopes_stack (e_binop e1 binop e2) =
  (case e1 of
   | (e_v v) =>
    if is_short_circuitable binop
    then
     (case e_exec_short_circuit v binop e2 of
      | SOME e' => SOME (e', [])
      | NONE => NONE)
    else if is_v e2
    then
     (case e_exec_binop e1 binop e2 of
      | SOME v' => SOME (e_v v', [])
      | NONE => NONE)
    else
     (case e_exec ctx g_scope_list scopes_stack e2 of
      | SOME (e2', frame_list) => SOME (e_binop e1 binop e2', frame_list)
      | NONE => NONE)
   | _ =>
    (case e_exec ctx g_scope_list scopes_stack e1 of
     | SOME (e1', frame_list) => SOME (e_binop e1' binop e2, frame_list)
     | NONE => NONE)))
  /\
 (**********)
 (* Select *)
 (e_exec ctx g_scope_list scopes_stack (e_select e v_x_l x) =
  if is_v e
  then
    (case e_exec_select e v_x_l x of
     | SOME x' => SOME (e_v (v_str x'), [])
     | NONE => NONE)
  else
   (case e_exec ctx g_scope_list scopes_stack e of
    | SOME (e', frame_list) => SOME (e_select e' v_x_l x, frame_list)
    | NONE => NONE))
  /\
 (e_exec _ _ _ _ = NONE)
`
(WF_REL_TAC `measure e_state_size` >>
 fs [e_state_size_def, e_size_def] >>
 REPEAT STRIP_TAC >| [
  IMP_RES_TAC unred_arg_index_in_range >>
  IMP_RES_TAC rich_listTheory.EL_MEM >>
  IMP_RES_TAC e3_size_mem >>
  fs [],

  IMP_RES_TAC unred_mem_index_in_range >>
  IMP_RES_TAC rich_listTheory.EL_MEM >>
  `e_size (EL i (MAP SND x_e_l)) < e1_size x_e_l` suffices_by (
   fs []
  ) >>
  `e2_size (EL i (MAP FST x_e_l), EL i (MAP SND x_e_l)) < e1_size x_e_l` suffices_by (
   rpt strip_tac >>
   irule arithmeticTheory.LESS_TRANS >>
   qexists_tac `e2_size (EL i (MAP FST x_e_l),EL i (MAP SND x_e_l))` >>
   fs [e_e2_size_less]
  ) >>
  subgoal `MEM (EL i x_e_l) x_e_l` >- (
   irule rich_listTheory.EL_MEM >>
   fs [listTheory.LENGTH_MAP]
  ) >>
  imp_res_tac e1_size_mem >>
  fs [EL_pair_list]
 ]
);
(* TODO: Is the below line too hacky? Should the theorem only be referred to as "e_exec_def"? *)
val e_exec = save_thm("e_exec", e_exec);

Definition stmt_exec:
 (******************************************)
 (* Catch-all clauses for special statuses *)
 (stmt_exec (ctx:ctx) ((g_scope_list:g_scope_list, frame_list:frame_list, ctrl:ctrl, status_type_error):state) = NONE)
  /\
 (* No statement execution step begins with return status *)
 (stmt_exec _ (_, _, _, status_returnv v) = NONE)
  /\
 (* Empty frame list *)
 (stmt_exec _ (_, [], _, _) = NONE)
  /\
 (* TODO: frame list does not take into account nested frames here? *)
 (stmt_exec _ (g_scope_list, [(funn, stmt, scopes_stack)], ctrl, status_pars_next x) =
  SOME (g_scope_list, [(funn, stmt_empty, scopes_stack)], ctrl, status_pars_next x))
  /\
 (***************)
 (* Frame rules *)
 (stmt_exec (ext_map, func_map, tbl_map) (g_scope_list, ((funn, stmt, scopes_stack)::((funn', stmt', scopes_stack')::frame_list'')), ctrl, status_running) =
   (case stmt_exec (ext_map, func_map, tbl_map) (g_scope_list, [(funn, stmt, scopes_stack)], ctrl, status_running) of
    | SOME (g_scope_list', frame_list', ctrl', status') =>
     (case status' of
      | status_returnv v =>
       let scopes_stack'' = initialise (g_scope_list'++scopes_stack') varn_star v in
        (case lookup_funn_sig_body funn func_map ext_map of
         | SOME (stmt'', x_d_l) =>
          (case copyout (MAP FST x_d_l) (MAP SND x_d_l) (TAKE 2 scopes_stack'') (DROP 2 scopes_stack'') scopes_stack of
           | SOME (g_scope_list'', scopes_stack''') =>
            SOME (g_scope_list'', ((funn', stmt', scopes_stack''')::frame_list''), ctrl', status_running)
           | _ => NONE)
         | _ => NONE)
      | _ => 
       SOME (g_scope_list', frame_list'++((funn', stmt', scopes_stack')::frame_list''), ctrl', status'))
    | _ => NONE))
  /\
 (**************)
 (* Assignment *)
 (stmt_exec ctx (g_scope_list, [(funn, stmt_ass lval e, scopes_stack)], ctrl, status_running) =
  if is_v e
  then
   (case stmt_exec_ass lval e (g_scope_list++scopes_stack) of
    | SOME scopes_stack' =>
     SOME (TAKE 2 scopes_stack', [(funn, stmt_empty, DROP 2 scopes_stack')], ctrl, status_running)
    | NONE => NONE)
  else
   (case e_exec ctx g_scope_list scopes_stack e of
    | SOME (e', frame_list) =>
     SOME (g_scope_list, frame_list++[(funn, stmt_ass lval e', scopes_stack)], ctrl, status_running)
    | _ => NONE))
  /\
 (***********)
 (* Declare *)
 (stmt_exec ctx (g_scope_list, [(funn, stmt_declare t x init_opt, scopes_stack)], ctrl, status_running) =
  case init_opt of
  | SOME init =>
   if is_v init
   then
    let
     scopes_stack' = stmt_exec_init (varn_name x) init (g_scope_list++scopes_stack)
    in
     SOME (TAKE 2 scopes_stack', [(funn, stmt_empty, DROP 2 scopes_stack')], ctrl, status_running)
   else
    (case e_exec ctx g_scope_list scopes_stack init of
     | SOME (init', frame_list) =>
      SOME (g_scope_list, frame_list++[(funn, stmt_declare t x (SOME init'), scopes_stack)], ctrl, status_running)
     | _ => NONE)
  | NONE =>
   let
    (g_scope_list', scopes_stack') = declare g_scope_list scopes_stack x t
   in
    SOME (g_scope_list', [(funn, stmt_empty, scopes_stack')], ctrl, status_running))
  /\
 (**********)
 (* Verify *)
 (stmt_exec ctx (g_scope_list, [(funn, stmt_verify e1 e2, scopes_stack)], ctrl, status_running) =
  if is_v e1
  then
   if is_v_bool e1
   then
    if is_v e2
    then
     if is_v_err e2
     then
      (case stmt_exec_verify e1 e2 of
       | SOME stmt => SOME (g_scope_list, [(funn, stmt, scopes_stack)], ctrl, status_running)
       | NONE => NONE)
     else NONE
    else
     (case e_exec ctx g_scope_list scopes_stack e2 of
      | SOME (e2', frame_list) =>
       SOME (g_scope_list, frame_list++[(funn, stmt_verify e1 e2', scopes_stack)], ctrl, status_running)
      | NONE => NONE)
    else NONE
  else
   (case e_exec ctx g_scope_list scopes_stack e1 of
    | SOME (e1', frame_list) =>
     SOME (g_scope_list, frame_list++[(funn, stmt_verify e1' e2, scopes_stack)], ctrl, status_running)
    | NONE => NONE))
  /\
 (**************)
 (* Transition *)
 (stmt_exec ctx (g_scope_list, [(funn, stmt_trans e, scopes_stack)], ctrl, status_running) =
  if is_v e
  then
   if is_v_str e
   then
    (case stmt_exec_trans e of
     | SOME status' => SOME (g_scope_list, [(funn, stmt_empty, scopes_stack)], ctrl, status')
     | NONE => NONE)
    else NONE
  else
   (case e_exec ctx g_scope_list scopes_stack e of
    | SOME (e', frame_list) =>
     SOME (g_scope_list, frame_list++[(funn, stmt_trans e', scopes_stack)], ctrl, status_running)
    | NONE => NONE))
  /\
 (***************)
 (* Conditional *)
 (stmt_exec ctx (g_scope_list, [(funn, stmt_cond e stmt1 stmt2, scopes_stack)], ctrl, status_running) =
  if is_v_bool e
  then
   (case stmt_exec_cond e of
    | SOME T => SOME (g_scope_list, [(funn, stmt1, scopes_stack)], ctrl, status_running)
    | SOME F => SOME (g_scope_list, [(funn, stmt2, scopes_stack)], ctrl, status_running)
    | NONE => NONE)
  else
   (case e_exec ctx g_scope_list scopes_stack e of
    | SOME (e', frame_list) =>
     SOME (g_scope_list, frame_list++[(funn, stmt_cond e' stmt1 stmt2, scopes_stack)], ctrl, status_running)
    | NONE => NONE))
  /\
 (*********************)
 (* Table application *)
 (stmt_exec (ext_map, func_map, tbl_map) (g_scope_list, [(funn, stmt_app t_name e_l, scopes_stack)], ctrl, status_running) =
  (case index_not_const e_l of
   | SOME i =>
    (case e_exec (ext_map, func_map, tbl_map) g_scope_list scopes_stack (EL i e_l) of
     | SOME (e', frame_list) =>
      SOME (g_scope_list, frame_list++[(funn, stmt_app t_name (LUPDATE e' i e_l), scopes_stack)], ctrl, status_running)
     | NONE => NONE)
   | NONE =>
    (case FLOOKUP tbl_map t_name of
     | SOME mk_l =>
      (case ctrl (t_name, e_l, mk_l) of
       | SOME (f, f_args) =>
        SOME (g_scope_list, [(funn, stmt_ass lval_null (e_call (funn_name f) f_args), scopes_stack)], ctrl, status_running)
       | NONE => NONE)
     | NONE => NONE)))
  /\
 (**********)
 (* Return *)
 (stmt_exec ctx (g_scope_list, [(funn, stmt_ret e, scopes_stack)], ctrl, status_running) =
  (case get_v e of
   | SOME v => SOME (g_scope_list, [(funn, stmt_empty, scopes_stack)], ctrl, status_returnv v)
   | NONE => 
    (case e_exec ctx g_scope_list scopes_stack e of
     | SOME (e', frame_list) =>
      SOME (g_scope_list, frame_list++[(funn, stmt_ret e', scopes_stack)], ctrl, status_running)
     | NONE => NONE)))
  /\
 (**********)
 (* Extern *)
 (stmt_exec (ext_map, func_map, tbl_map) (g_scope_list, [(funn, stmt_ext, scopes_stack)], ctrl, status_running) =
  (case lookup_ext_fun funn ext_map of
   | SOME ext_fun =>
    (case ext_fun (g_scope_list, scopes_stack, ctrl) of
     | SOME (g_scope_list', scopes_stack', ctrl') =>
      SOME (g_scope_list', [(funn, stmt_empty, scopes_stack')], ctrl', status_running)
     | NONE => NONE)
   | NONE => NONE))
  /\
 (*********)
 (* Block *)
 (stmt_exec ctx (g_scope_list, [(funn, stmt_block stmt, scopes_stack)], ctrl, status_running) =
  SOME (g_scope_list, [(funn, stmt_block_ip stmt, (FEMPTY::scopes_stack))], ctrl, status_running))
  /\
 (*********)
 (* Block in-progress *)
 (stmt_exec ctx (g_scope_list, [(funn, stmt_block_ip stmt, scopes_stack)], ctrl, status_running) =
  (case stmt_exec ctx (g_scope_list, [(funn, stmt, scopes_stack)], ctrl, status_running) of
   | SOME (g_scope_list', [(funn, stmt_empty, scopes_stack')], ctrl', status') =>
    SOME (g_scope_list', [(funn, stmt_empty, TL scopes_stack')], ctrl', status')
   | SOME (g_scope_list', [(funn, stmt', scopes_stack')], ctrl', status') =>
    SOME (g_scope_list', [(funn, stmt_block_ip stmt', scopes_stack')], ctrl', status_running)
   | SOME (g_scope_list', (frame::[(funn, stmt', scopes_stack')]), ctrl', status_running) =>
    SOME (g_scope_list', (frame::[(funn, stmt_block_ip stmt', scopes_stack')]), ctrl', status_running)
   | _ => NONE))
  /\
 (************)
 (* Sequence *)
 (stmt_exec ctx (g_scope_list, [(funn, stmt_seq stmt1 stmt2, scopes_stack)], ctrl, status_running) =
  if is_empty stmt1
  then SOME (g_scope_list, [(funn, stmt2, scopes_stack)], ctrl, status_running)
  else
   (* Note: this only allows for 0 or 1 frame being added *)
   (case stmt_exec ctx (g_scope_list, [(funn, stmt1, scopes_stack)], ctrl, status_running) of
    | SOME (g_scope_list', [(funn, stmt1', scopes_stack')], ctrl', status') =>
     SOME (g_scope_list', [(funn, stmt_seq stmt1' stmt2, scopes_stack')], ctrl', status')
    | SOME (g_scope_list', (frame::[(funn, stmt1', scopes_stack')]), ctrl', status_running) =>
     SOME (g_scope_list', (frame::[(funn, stmt_seq stmt1' stmt2, scopes_stack')]), ctrl', status_running)
    | _ => NONE))
  /\
 (stmt_exec _ _ = NONE)
End

(* Then, define an executable semantics which performs execution until out of fuel. *)
(* Note that all concrete operations remain the same *)
(* Note that expression multi-step execution makes little sense with the current semantics... *)
Definition stmt_multi_exec:
 (stmt_multi_exec _ state 0 =
  SOME state)
 /\
 (stmt_multi_exec ctx state (SUC fuel) =
  case stmt_exec ctx state of
  | SOME state' => stmt_multi_exec ctx state' fuel
  | NONE => NONE)
End

(****************************)
(*  Parser block semantics  *)
(****************************)
        
val pars_exec_def = Define `
 (pars_exec (pctx:pctx) ((g_scope_list, frame_list, ctrl, status_type_error):state) = NONE) /\
 (* No step should start in status pars_next *)
 (pars_exec _ (_, _, _, status_pars_next x) = NONE) /\
 (pars_exec (ext_map, func_map, pars_map) (g_scope_list, frame_list, ctrl, status_running) =
  (case stmt_exec (ext_map, func_map, FEMPTY) (g_scope_list, frame_list, ctrl, status_running) of
   (* Empty frame list *)
   | SOME (g_scope_list', [], ctrl', status') => NONE
   (* No parser-level transition should end with return status *)
   | SOME (g_scope_list', frame_list', ctrl', status_returnv v) => NONE
   (* No parser-level transition should end with type error *)
   | SOME (g_scope_list', frame_list', ctrl', status_type_error) => NONE
   (* Transition to next parser state *)
   | SOME (g_scope_list', frame_list', ctrl', status_pars_next (pars_next_trans x)) =>
    (case FLOOKUP pars_map x of
     | SOME stmt'' => SOME (g_scope_list', [(funn_name x, stmt'', [])], ctrl', status_running)
     | NONE => NONE)
   (* Transition to final parser state *)
   | SOME (g_scope_list', frame_list', ctrl', status_pars_next (pars_next_pars_fin pars_fin)) =>
    SOME (g_scope_list', frame_list', ctrl', status_pars_next (pars_next_pars_fin pars_fin))
   (* When reaching the empty statement, go to reject *)
   | SOME (g_scope_list', [(funn, stmt_empty, scopes_stack)], ctrl', status_running) =>
    SOME (g_scope_list', [(funn, stmt_trans (e_v (v_str "reject")), scopes_stack)], ctrl', status_running)
   (* Regular execution of parser state body *)
   | SOME state' => SOME state'
   | NONE => NONE)
 )
`;

(* Fuel-powered multi-step executable semantics for parsers *)
val pars_multi_exec = Define `
 (pars_multi_exec _ state 0 =
  SOME state)
  /\
 (pars_multi_exec pctx state (SUC fuel) =
  case pars_exec pctx state of
  | SOME state' => pars_multi_exec pctx state' fuel
  | NONE => NONE)
`;

(*****************************)
(*  Control block semantics  *)
(*****************************)

(* TODO: Note cctx and ctx have same type, for now... *)
(* TODO: Handle return value in any way? *)
(* TODO: Outsouce matching of stmt_ret (e_v v) and stmt_seq (stmt_ret (e_v v)) stmt to new
 * function? *)
val ctrl_exec_def = Define `
 (ctrl_exec (cctx:cctx) ((g_scope_list, frame_list, ctrl, status_type_error):state) = NONE) /\
 (ctrl_exec _ (_, _, _, status_pars_next x) = NONE) /\
(*
 (ctrl_exec _ (g_scope_list, [(funn, stmt_ret e, scopes_stack)], ctrl, status_running) =
  if is_v e
  then
   SOME (g_scope_list, [(funn, stmt_empty, scopes_stack)], ctrl, status_running)
  else
   SOME (g_scope_list, [(funn, stmt_ret e, scopes_stack)], ctrl, status_running)
 ) /\
 (ctrl_exec _ (g_scope_list, [(funn, stmt_seq (stmt_ret e) stmt, scopes_stack)], ctrl, status_running) =
  if is_v e
  then
   SOME (g_scope_list, [(funn, stmt_empty, scopes_stack)], ctrl, status_running)
  else
   SOME (g_scope_list, [(funn, stmt_seq (stmt_ret e) stmt, scopes_stack)], ctrl, status_running)
 ) /\
*)
 (ctrl_exec cctx (g_scope_list, frame_list, ctrl, status_running) =
  (case stmt_exec cctx (g_scope_list, frame_list, ctrl, status_running) of
   | SOME (g_scope_list', frame_list', ctrl', status_running) =>
    SOME (g_scope_list', frame_list', ctrl', status_running)
   (* If return status is set on base level, set statement to empty (matching arch_control_ret) *)
   | SOME (g_scope_list', [(funn, stmt, scopes_stack)], ctrl', status_returnv v) =>
    SOME (g_scope_list', [(funn, stmt_empty, scopes_stack)], ctrl', status_running)
   | _ => NONE)
 ) /\
 (ctrl_exec _ _ = NONE)
`;

(* Fuel-powered multi-step executable semantics for control blocks *)
val ctrl_multi_exec = Define `
 (ctrl_multi_exec _ state 0 =
  SOME state)
  /\
 (ctrl_multi_exec cctx state (SUC fuel) =
  case ctrl_exec cctx state of
  | SOME state' => ctrl_multi_exec cctx state' fuel
  | NONE => NONE)
`;

(***********************************)
(*  Architectural-level semantics  *)
(***********************************)

(* TODO: Outsource the stuff that causes too many case splits to other functions
 *       i.e. exec_arch_e, exec_arch_update_return_frame, exec_arch_assign, ... *)
val arch_exec_def = Define `
 (arch_exec (actx:'a actx) ((aenv:'a aenv), (g_scope_list:g_scope_list) , (arch_frame_list:arch_frame_list) , (ctrl:ctrl), status_type_error) = NONE) /\
 (* arch_parser_ret: Note that this is a different clause from arch_control_ret due to the status *)
 (arch_exec (ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, ext_map, func_map)
            ((i, in_out_list, in_out_list', scope), g_scope_list,
             (arch_frame_list_regular [(funn, stmt, scopes_stack)]), ctrl,
             (status_pars_next (pars_next_pars_fin pars_fin))) =
  if (is_empty stmt) then
   (case EL i ab_list of
    | (arch_block_pbl x el) =>
     (case FLOOKUP pblock_map x of
      | SOME (pblock_parser x_d_list stmt pars_map) =>
(* TODO: Note that this function will always copy out parseError from a parser. Unclear if this is intended in the spec. *)
       (case copyout_pbl ((g_scope_list++scopes_stack), scope, (d_out::(MAP SND x_d_list)), ("parseError"::(MAP FST x_d_list))) of
        | SOME scope' =>
             SOME ((i+1, in_out_list, in_out_list', scope'), TAKE 1 g_scope_list,
                   arch_frame_list_empty, ctrl, status_running)
        | _ => NONE)
      | _ => NONE)
    | _ => NONE)
   else NONE)
 /\
 (arch_exec (ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, ext_map, func_map)
            ((i, in_out_list, in_out_list', scope), g_scope_list,
             (arch_frame_list_regular [(funn, stmt_empty, scopes_stack)]), ctrl, status_running) =
 (* arch_control_ret *)
  (case EL i ab_list of
   | (arch_block_pbl x el) =>
    (case FLOOKUP pblock_map x of
     | SOME (pblock_control x_d_list stmt stmt' tbl_map) =>
      (case copyout_pbl (g_scope_list, scope, (MAP SND x_d_list), (MAP FST x_d_list)) of
       | SOME scope' =>
        SOME ((i+1, in_out_list, in_out_list', scope'), (TAKE 1 g_scope_list),
               arch_frame_list_empty, ctrl, status_running)
       | _ => NONE)
     | _ => NONE)
   | _ => NONE)
 )
 /\
 (arch_exec (ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, ext_map, func_map)
            ((i, in_out_list, in_out_list', scope), g_scope_list,
             arch_frame_list_empty, ctrl, status_running) =
  (case EL i ab_list of
   (* arch_in *)
   | arch_block_inp =>
    (case input_f (in_out_list, scope) of
     | SOME (in_out_list'', scope') => 
      SOME ((i+1, in_out_list'', in_out_list', scope'), g_scope_list, arch_frame_list_empty,
             ctrl, status_running)
     | NONE => NONE)
   | (arch_block_pbl x el) =>
    (case FLOOKUP pblock_map x of
     (* arch_control_init *)
     | SOME (pblock_control x_d_list stmt stmt' tbl_map) =>
        (case copyin_pbl ((MAP FST x_d_list), (MAP SND x_d_list), el, scope) of
         | SOME scope' =>
          SOME ((i, in_out_list, in_out_list', scope), (g_scope_list++[scope']),
                arch_frame_list_regular [(funn_name x, stmt_seq stmt stmt', [])], ctrl, status_running)
         | _ => NONE)
     (* arch_parser_init *)
     | SOME (pblock_parser x_d_list stmt pars_map) =>
        (case FLOOKUP pars_map "start" of
         | SOME stmt' =>
          (case copyin_pbl ((MAP FST x_d_list), (MAP SND x_d_list), el, scope) of
           | SOME scope' =>
            (let block_global_scope = FUPDATE scope' (varn_name "parseError", (v_err "NoError", SOME (lval_varname (varn_name "parseError")))) in
              SOME ((i, in_out_list, in_out_list', scope), (g_scope_list++[block_global_scope]),
                    arch_frame_list_regular [(funn_name x, stmt_seq stmt stmt', [])], ctrl, status_running))
           | NONE => NONE)
         | NONE => NONE)
     | _ => NONE)
   (* arch_ffbl *)
   | (arch_block_ffbl x) =>
    (case FLOOKUP ffblock_map x of
     | SOME (ffblock_ff ff) =>
      (case ff scope of
       | SOME scope' =>
        SOME ((i+1, in_out_list, in_out_list', scope'), g_scope_list, arch_frame_list_empty, ctrl, status_running)
       | NONE => NONE)
     | NONE => NONE)
   (* arch_out *)
   | arch_block_out =>
    (case output_f (in_out_list', scope) of
     | SOME (in_out_list'', scope') =>
      SOME ((0, in_out_list, in_out_list'', scope'), g_scope_list, arch_frame_list_empty, ctrl,
            status_running)
     | NONE => NONE)
  )
 )
/\
 (* Operating on any other statement: arch_parser_exec, arch_control_exec *)
 (arch_exec (ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, ext_map, func_map)
            ((i, in_out_list, in_out_list', scope), g_scope_list, (arch_frame_list_regular frame_list), ctrl, status) =
  (case EL i ab_list of
   | (arch_block_pbl x el) =>
    (case FLOOKUP pblock_map x of
     | SOME (pblock_parser x_d_list stmt'' pars_map) =>
      (case pars_exec (ext_map, func_map, pars_map) (g_scope_list, frame_list, ctrl, status) of
       | SOME (g_scope_list', frame_list', ctrl', status') =>
        SOME ((i, in_out_list, in_out_list', scope), g_scope_list', (arch_frame_list_regular frame_list'), ctrl', status')
       | _ => NONE)
     | SOME (pblock_control x_d_list stmt'' stmt''' tbl_map) =>
      (case ctrl_exec (ext_map, func_map, tbl_map) (g_scope_list, frame_list, ctrl, status) of
       | SOME (g_scope_list', frame_list', ctrl', status') =>
        SOME ((i, in_out_list, in_out_list', scope), g_scope_list', (arch_frame_list_regular frame_list'), ctrl', status')
       | _ => NONE)
     | _ => NONE)
   | _ => NONE)
 )
/\
(arch_exec _ _ = NONE)
`;

(* Fuel-powered multi-step architectural-level executable semantics *)
val arch_multi_exec = Define `
 (arch_multi_exec actx (aenv, g_scope_list, arch_frame_list, ctrl, status) 0 =
  SOME (aenv, g_scope_list, arch_frame_list, ctrl, status))
  /\
 (arch_multi_exec actx (aenv, g_scope_list, arch_frame_list, ctrl, status) (SUC fuel) =
  case arch_exec actx (aenv, g_scope_list, arch_frame_list, ctrl, status) of
  | SOME (aenv', g_scope_list', arch_frame_list', ctrl', status') =>
   arch_multi_exec actx (aenv', g_scope_list', arch_frame_list', ctrl', status') fuel
  | NONE => NONE)
`;

        
(**********)
(*  Misc  *)
(**********)
        
(* Then, define the closure of the small step reduction. *)
val (stmt_clos_sem_rules, stmt_clos_sem_ind, stmt_clos_sem_cases) = Hol_reln`
(* Base clause: *)
(!ctx state state'.
 stmt_red ctx state state' ==> 
 stmt_clos_red ctx state state')
(* Inductive clause: *)
/\
(!ctx state state' state''.
 (stmt_red ctx state state' /\ 
  stmt_clos_red ctx state' state'') ==> 
 stmt_clos_red ctx state state'')
`;

(* Then, prove that the multi-step executable semantics is sound with respect to the
 * closure of the small-step reduction *)
Theorem stmt_multi_exec_sound_red:
 !ctx state state' fuel.
  stmt_multi_exec ctx state fuel = SOME state' ==>
  stmt_clos_red ctx state state'
Proof
 cheat
QED

(*
(* TODO: some kind of (multi-step) CakeML-adjusted executable semantics definition *)
Definition e_exec_cake:
 (e_exec_cake (e_unop unop_neg (e_v (v_bool b))) stacks status =
   SOME (e_v (v_bool ~b)))
  /\
 (e_exec_cake (e_unop unop_compl (e_v (v_bit bitv))) stacks status =
  SOME (e_v (v_bit (bitv_bl_unop bnot bitv))))
  \/gi
 (e_exec_cake (e_unop unop_neg_signed (e_v (v_bit bitv))) stacks status =
  SOME (e_v (v_bit (bitv_unop unop_neg_signed bitv))))
  /\
 (e_exec_cake (e_unop unop_un_plus (e_v (v_bit bitv))) stacks status =
  SOME (e_v (v_bit bitv)))
  /\
 (e_exec_cake _ stacks status = NONE)
End

(* TODO: At this point, expect to translate lists to lists and fmaps to mlmaps and make casts for all non-64-bit words *)
Theorem sem_expr_exe_cake_equiv:
 !e stacks.
  e_exec_cake e stacks status_running = e_exec_multi e stacks status_running
Proof
 cheat
QED
*)

val _ = export_theory ();
