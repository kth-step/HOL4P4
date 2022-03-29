open HolKernel boolLib Parse bossLib;

val _ = new_theory "p4_exec_sem";

open p4Syntax;
open ottTheory;
open p4Theory;

(* For EVAL-uating: *)
open blastLib bitstringLib;

(* Obtains a list of assumptions for a reduction clause *)
fun get_clause_assums thm =
 (strip_conj o fst o dest_imp o concl o SPEC_ALL) thm
;

(* Finds in a red_rules-theorem exported from ott the rule with name clause_name_str *)
fun find_clause thm clause_name_str =
 let
  val clause_name_str_tm = stringSyntax.fromMLstring clause_name_str
  val conj_thms = CONJUNCTS thm
 in
  List.find (
   (fn assums => isSome (List.find
    (fn tm =>
     if is_clause_name tm
     then term_eq (dest_clause_name tm) clause_name_str_tm
     else false)
    assums)
   ) o get_clause_assums) conj_thms
 end
;
val find_clause_e_red = find_clause e_red_rules
val find_clause_stmt_red = find_clause stmt_red_rules


Theorem e1_size_append:
 !e_l1 e_l2. e1_size (e_l1 ++ e_l2) = (e1_size e_l1 + e1_size e_l2)
Proof
 Induct_on `e_l1` >> (
  fs [e_size_def]
 )
QED

Theorem e1_size_mem:
 !e e_l. MEM e e_l ==> e_size e < e1_size e_l
Proof
 REPEAT STRIP_TAC >>
 fs [listTheory.MEM_SPLIT, e1_size_append, e_size_def]
QED

Theorem index_find_length:
 !l i f j e. (INDEX_FIND i f l = SOME (j, e)) ==> (j - i < LENGTH l)
Proof
 Induct_on `l` >> (
  fs [listTheory.INDEX_FIND_def]
 ) >>
 REPEAT STRIP_TAC >>
 fs [] >>
 Cases_on `f h` >> (
  fs []
 ) >>
 Q.PAT_X_ASSUM `!i f j e. _` (ASSUME_TAC o Q.SPECL [`SUC i`, `f`, `j`, `e`]) >>
 rfs []
QED

Theorem index_find_first:
 !l f e i j.
 (INDEX_FIND i f l = SOME (j, e)) ==>
 (f e /\ (!j'. (i <= j' /\ j' < j) ==> ~(f (EL (j' - i) l))))
Proof
 Induct_on `l` >> (
  fs [listTheory.INDEX_FIND_def]
 ) >>
 REPEAT STRIP_TAC >>
 fs [] >>
 Cases_on `f h` >> (
  fs []
 ) >> (
  Q.PAT_X_ASSUM `!f e i j. _` (ASSUME_TAC o Q.SPECL [`f`, `e`, `SUC i`, `j`]) >>
  rfs []
 ) >>
 Q.PAT_X_ASSUM `!j'. _` (ASSUME_TAC o Q.SPEC `j'`) >>
 subgoal `SUC i <= j'` >- (
  Cases_on `i = j'` >- (
   fs []
  ) >>
  fs []
 ) >>
 fs [] >>
 rfs [] >>
 subgoal `j' - i = (SUC (j' - SUC i))` >- (
  fs []
 ) >>
 fs [listTheory.EL_restricted]
QED

Theorem unred_arg_index_in_range:
 !d_l e_l i. unred_arg_index d_l e_l = SOME i ==> i < LENGTH e_l
Proof
 REPEAT STRIP_TAC >>
 fs [unred_arg_index_def, find_unred_arg_def] >>
 Cases_on `INDEX_FIND 0 (\(d,e). ~is_d_out d /\ ~is_const e) (ZIP (d_l,e_l))` >> (
  fs []
 ) >>
 Cases_on `x` >>
 IMP_RES_TAC index_find_length >>
 fs []
QED

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

Definition is_empty:
 (is_empty stmt_empty = T) /\
 (is_empty _ = F)
End

Definition get_ret_v:
 (get_ret_v (stmt_ret (e_v v)) = SOME v) /\
 (get_ret_v (stmt_seq (stmt_ret (e_v v)) stmt) = SOME v) /\
 (get_ret_v _ = NONE)
End

(*********************************)
(* Expression-related shorthands *)

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

Definition is_short_circuitable:
 (is_short_circuitable (e_v (v_bool F)) binop_bin_and = T) /\
 (is_short_circuitable (e_v (v_bool T)) binop_bin_or = T) /\
 (is_short_circuitable _ _ = F)
End

Definition e_exec_binop:
 (e_exec_binop (e_v v1) binop (e_v v2) = binop_exec binop v1 v2)
  /\
 (e_exec_binop _ _ _ = NONE)
End

(* Field access *)
Definition e_exec_acc:
 (e_exec_acc (e_acc (e_v (v_struct f_v_list)) (e_v (v_str f))) =
  case FIND (\(k, v). k = f) f_v_list of
  | SOME (f, v) => SOME (e_v v)
  | NONE => NONE)
  /\
 (e_exec_acc (e_acc (e_v (v_header boolv f_v_list)) (e_v (v_str f))) =
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
val e_exec = TotalDefn.tDefine "e_exec" `
 (************************************************)
 (* e_v is the fully reduced form of expressions *)
 (e_exec (ctx:ctx) (g_scope_list:g_scope_list) (scopes_stack:scopes_stack) (e_v v) =
  SOME (e_v v, ([]:frame_list)))
  /\
 (********************)
 (* Variable look-up *)
 (e_exec ctx g_scope_list scopes_stack (e_var x) =
  case lookup_vexp2 scopes_stack g_scope_list x of
  | SOME v => SOME (e_v v, [])
  | NONE => NONE)
  /\
 (******************************)
 (* Struct/header field access *)
 (e_exec ctx g_scope_list scopes_stack (e_acc e_struct e_field) =
  if is_v e_field
  then
   if is_v_str e_field
   then
    (if is_v e_struct
     then
      (case e_exec_acc (e_acc e_struct e_field) of
       | SOME e' => SOME (e', [])
       | NONE => NONE)
     else
      (case e_exec ctx g_scope_list scopes_stack e_struct of
       | SOME (e_struct', frame_list) => SOME (e_acc e_struct' e_field, frame_list)
       | NONE => NONE))
   else NONE
  else
   (case e_exec ctx g_scope_list scopes_stack e_field of
    | SOME (e_field', frame_list) => SOME (e_acc e_struct e_field', frame_list)
    | NONE => NONE))
  /\
 (************************)
 (* Function/extern call *)
 (e_exec (ty_map, ext_map, func_map, tbl_map) g_scope_list scopes_stack (e_call funn e_l) =
  (case lookup_funn_sig_body funn func_map ext_map of
    | SOME (stmt, x_d_l) =>
     (case unred_arg_index (MAP SND x_d_l) e_l of
      | SOME i =>
       (case e_exec (ty_map, ext_map, func_map, tbl_map) g_scope_list scopes_stack (EL i e_l) of
        | SOME (e', frame_list) => SOME (e_call funn (LUPDATE e' i e_l), frame_list)
        | NONE => NONE)
      | NONE =>
       (case copyin (MAP FST x_d_l) (MAP SND x_d_l) e_l g_scope_list scopes_stack of
        | SOME scope => 
         SOME (e_var varn_star, [(funn, stmt, [scope])])
        | NONE => NONE))
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
  if is_v e1
  then
   if is_short_circuitable e1 binop
   then SOME (e1, [])
   else if is_v e2
   then
    (case e_exec_binop e1 binop e2 of
     | SOME v => SOME (e_v v, [])
     | NONE => NONE)
   else
    (case e_exec ctx g_scope_list scopes_stack e2 of
     | SOME (e2', frame_list) => SOME (e_binop e1 binop e2', frame_list)
     | NONE => NONE)
  else
   (case e_exec ctx g_scope_list scopes_stack e1 of
    | SOME (e1', frame_list) => SOME (e_binop e1' binop e2, frame_list)
    | NONE => NONE))
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
 REPEAT STRIP_TAC >>
 IMP_RES_TAC unred_arg_index_in_range >>
 IMP_RES_TAC rich_listTheory.EL_MEM >>
 IMP_RES_TAC e1_size_mem >>
 fs []
);

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
 (*****************************************************)
 (* empty_stmt is the fully reduced form of statement *)
 (stmt_exec _ (g_scope_list, [(funn, stmt_empty, scopes_stack)], ctrl, status) =
  SOME (g_scope_list, [(funn, stmt_empty, scopes_stack)], ctrl, status)) /\
 (***************)
 (* Frame rules *)
 (stmt_exec (ty_map, ext_map, func_map, tbl_map) (g_scope_list, ((funn, stmt, scopes_stack)::((funn', stmt', scopes_stack')::frame_list'')), ctrl, status_running) =
   (case stmt_exec (ty_map, ext_map, func_map, tbl_map) (g_scope_list, [(funn, stmt, scopes_stack)], ctrl, status_running) of
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
 (stmt_exec (ty_map, ext_map, func_map, tbl_map) (g_scope_list, [(funn, stmt_app t_name e, scopes_stack)], ctrl, status_running) =
  (case get_v e of
   | SOME v =>
    (case FLOOKUP tbl_map t_name of
     | SOME (e_t, m_k) =>
      (case ctrl (t_name, v, m_k) of
       | SOME (f, f_args) =>
        SOME (g_scope_list, [(funn, stmt_ass lval_null (e_call (funn_name f) f_args), scopes_stack)], ctrl, status_running)
       | NONE => NONE)
     | NONE => NONE)
   | NONE =>
    (case e_exec (ty_map, ext_map, func_map, tbl_map) g_scope_list scopes_stack e of
     | SOME (e', frame_list) =>
      SOME (g_scope_list, frame_list++[(funn, stmt_app t_name e', scopes_stack)], ctrl, status_running)
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
 (stmt_exec ctx (g_scope_list, [(funn, stmt_ext ext, scopes_stack)], ctrl, status_running) =
  (case ext (g_scope_list, scopes_stack, ctrl) of
   | SOME (g_scope_list', scopes_stack', ctrl') =>
    SOME (g_scope_list', [(funn, stmt_empty, scopes_stack')], ctrl', status_running)
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

(* Only meant to skip certain soundness proof parts for now *)
Theorem stmt_ignore_pars_next:
 !ctx g_scope_list frame_list ctrl p state'.
  stmt_red ctx (g_scope_list, frame_list, ctrl, (status_pars_next p)) state'
Proof
cheat
QED

(* Note that these are definitions phrased for given statements *)
Definition e_exec_sound:
 (e_exec_sound e =
  !ctx g_scope_list scopes_stack e' frame_list.
  e_exec ctx g_scope_list scopes_stack e = SOME (e', frame_list) ==>
  e_red ctx g_scope_list scopes_stack e e' frame_list)
End

(* Note that this definition is phrased for given statements, not on the frame list, so soundness
 * of comp1 and comp2 rules are excluded *)
Definition stmt_exec_sound:
 (stmt_exec_sound stmt =
  !ctx g_scope_list funn scopes_stack ctrl status state'.
  stmt_exec ctx (g_scope_list, [(funn, stmt, scopes_stack)], ctrl, status) = SOME state' ==>
  stmt_red ctx (g_scope_list, [(funn, stmt, scopes_stack)], ctrl, status) state')
End

(* TODO: Is this cheating? *)
Definition l_sound:
 (l_sound (l: e list) = T)
End

Theorem e_v_exec_sound_red:
!v. e_exec_sound (e_v v)
Proof
cheat
QED

Theorem stmt_block_ip_exec_sound_red:
!s.
stmt_exec_sound s ==>
stmt_exec_sound (stmt_block_ip s)
Proof
cheat
QED

Theorem stmt_block_exec_sound_red:
!s.
stmt_exec_sound s ==>
stmt_exec_sound (stmt_block s)
Proof
cheat
QED

Theorem stmt_verify_exec_sound_red:
!e1 e2.
e_exec_sound e1 ==>
e_exec_sound e2 ==>
stmt_exec_sound (stmt_verify e1 e2)
Proof
fs [stmt_exec_sound, e_exec_sound] >>
REPEAT STRIP_TAC >>
pairLib.PairCases_on `state'` >>
rename1 `(g_scope_list',state'1,state'2,state'3)` >>
rename1 `(g_scope_list',frame_list',ctrl',status')` >>
Cases_on `status` >> (
 fs [stmt_exec, stmt_ignore_pars_next]
) >>
Cases_on `is_v e1` >> Cases_on `is_v e2` >| [
 (* First case *)
 fs [] >>
 Cases_on `stmt_exec_verify e1 e2` >> (
  fs [] >>
  rw []
 ) >>
 Cases_on `e1` >> Cases_on `e2` >> (
  fs [stmt_exec_verify] >>
  rw []
 ) >>
 rename1 `is_v_bool (e_v v1)` >>
 rename1 `is_v_err (e_v v2)` >>
 Cases_on `v1` >> Cases_on `v2` >> (
  fs [stmt_exec_verify] >>
  rw []
 ) >>
 Cases_on `x` >> (
  Cases_on `b` >> (
   fs [stmt_exec_verify]
  )
 ) >| [
  METIS_TAC [(valOf o find_clause_stmt_red) "stmt_verify_3", clause_name_def],

  METIS_TAC [(valOf o find_clause_stmt_red) "stmt_verify_4", clause_name_def]
 ],

 (* Second case - second operand unreduced *)
 fs [] >>
 Cases_on `e_exec ctx g_scope_list scopes_stack e2` >> (
  fs []
 ) >>
 Cases_on `x` >>
 fs [] >>
 rw [] >>
 Cases_on `e1` >> (
  fs [is_v] >>
  rw []
 ) >>
 Cases_on `v` >> (
  fs [is_v_bool] >>
  rw []
 ) >>
 METIS_TAC [((valOf o find_clause_stmt_red) "stmt_verify_e2"), clause_name_def],

 (* Third case - first operand unreduced *)
 fs [] >>
 Cases_on `e_exec ctx g_scope_list scopes_stack e1` >> (
  fs []
 ) >>
 Cases_on `x` >>
 fs [] >>
 rw [] >>
 METIS_TAC [((valOf o find_clause_stmt_red) "stmt_verify_e1"), clause_name_def],

 (* Fourth case - both operands unreduced *)
 fs [] >>
 Cases_on `e_exec ctx g_scope_list scopes_stack e1` >> (
  fs []
 ) >>
 Cases_on `x` >>
 fs [] >>
 rw [] >>
 METIS_TAC [((valOf o find_clause_stmt_red) "stmt_verify_e1"), clause_name_def]
]
QED

Theorem e_acc_exec_sound_red:
!e1 e2.
e_exec_sound e1 ==>
e_exec_sound e2 ==>
e_exec_sound (e_acc e1 e2)
Proof
fs [e_exec_sound] >>
REPEAT STRIP_TAC >>
Cases_on `is_v e1` >> Cases_on `is_v e2` >| [
 (* 1st case is base case *)
 Cases_on `e1` >>  Cases_on `e2` >> (
  fs [is_v]
 ) >>
 Cases_on `v` >> Cases_on `v'` >> (
  fs [e_exec, e_exec_acc, is_v]
 ) >> (
  Cases_on `FIND (\(k,v). k = s) l` >>
  fs [] >>
  Cases_on `x` >>
  fs [] >>
  rw []
 ) >| [
  irule ((valOf o find_clause_e_red) "e_s_acc"),

  irule ((valOf o find_clause_e_red) "e_h_acc")
 ] >> (
  fs [clause_name_def, listTheory.FIND_def] >>
  subgoal `(\(k,v). k = s) (q,r)` >- (
   Cases_on `z` >>
   fs [] >>
   rw [] >>
   IMP_RES_TAC (ISPECL [``(l':((string # v) list))``, ``(\(k,v). k = s):(string # v -> bool)``, ``(q,r):string # v``, ``0``] index_find_first) >>
   fs []
  ) >>
  fs []
 ),

 (* Second case is reduction of 2nd argument (field name) *)
 Cases_on `e_exec ctx g_scope_list scopes_stack e2` >> (
  fs [e_exec]
 ) >>
 Cases_on `x` >>
 fs [] >>
 subgoal `~fully_reduced e2` >- (
  Cases_on `e2` >> (
   fs [fully_reduced_def, is_v]
  )
 ) >>
 METIS_TAC [((valOf o find_clause_e_red) "e_acc_arg2"), clause_name_def],

 (* Third case is reduction of 1st argument (struct value) *)
 Cases_on `e_exec ctx g_scope_list scopes_stack e1` >> (
  fs [e_exec]
 ) >>
 Cases_on `x` >> Cases_on `e2` >> (
  fs [is_v]
 ) >>
 Cases_on `v` >> (
  fs [is_v_str]
 ) >>
 METIS_TAC [((valOf o find_clause_e_red) "e_acc_arg1"), clause_name_def],

 (* Fourth case determines case when both arguments are unreduced *)
 Cases_on `e_exec ctx g_scope_list scopes_stack e2` >> (
  fs [e_exec]
 ) >>
 Cases_on `x` >>
 fs [] >>
 subgoal `~fully_reduced e2` >- (
  Cases_on `e2` >> (
   fs [fully_reduced_def, is_v]
  )
 ) >>
 METIS_TAC [(valOf o find_clause_e_red) "e_acc_arg2", clause_name_def]
]
QED

Theorem e_binop_exec_sound_red:
!e1 e2 b.
e_exec_sound e1 ==>
e_exec_sound e2 ==>
e_exec_sound (e_binop e1 b e2)
Proof
fs [e_exec_sound] >>
REPEAT STRIP_TAC >>
Cases_on `is_v e1` >> Cases_on `is_v e2` >| [
 (* Both operands are fully reduced *)
 Cases_on `is_short_circuitable e1 b` >- (
  (* Short-circuit *)
  Cases_on `e1` >> (
   fs [is_v]
  ) >>
  Cases_on `v` >> (
   fs [is_short_circuitable]
  ) >>
  Cases_on `b'` >> Cases_on `b` >> (
   fs [is_short_circuitable, e_exec, is_v]
  ) >| [
  irule ((valOf o find_clause_e_red) "e_bin_or1") >>
  fs [clause_name_def],
  
  irule ((valOf o find_clause_e_red) "e_bin_and1") >>
  fs [clause_name_def]
  ]
 ) >>
 fs [] >>
 Cases_on `e_exec_binop e1 b e2` >> (
  fs [e_exec] >>
  rw []
 ) >>
 (* Different concrete cases *)
 Cases_on `b` >> (
  Cases_on `e1` >> (
   fs [is_v]
  ) >>
  Cases_on `e2` >> (
   fs [is_v]
  ) >>
  Cases_on `v` >> Cases_on `v'` >> (
   fs [e_exec_binop, binop_exec]
  ) >>
  rw []
 ) >| [
   Cases_on `bitv_binop binop_mul p p'` >> (
    fs []
   ) >>
   Cases_on `x` >> (
    fs []
   ) >>
   irule ((valOf o find_clause_e_red) "e_mul"),

   Cases_on `bitv_binop binop_div p p'` >> (
    fs []
   ) >>
   Cases_on `x` >> (
    fs []
   ) >>
   irule ((valOf o find_clause_e_red) "e_div"),

   Cases_on `bitv_binop binop_mod p p'` >> (
    fs []
   ) >>
   Cases_on `x` >> (
    fs []
   ) >>
   irule ((valOf o find_clause_e_red) "e_mod"),

   Cases_on `bitv_binop binop_add p p'` >> (
    fs []
   ) >>
   Cases_on `x` >> (
    fs []
   ) >>
   irule ((valOf o find_clause_e_red) "e_add"),

   Cases_on `bitv_binop binop_sub p p'` >> (
    fs []
   ) >>
   Cases_on `x` >> (
    fs []
   ) >>
   irule ((valOf o find_clause_e_red) "e_sub"),

   irule ((valOf o find_clause_e_red) "e_shl"),

   irule ((valOf o find_clause_e_red) "e_shr"),

   Cases_on `bitv_binpred binop_le p p'` >> (
    fs []
   ) >>
   Cases_on `x` >> (
    fs []
   ) >>
   irule ((valOf o find_clause_e_red) "e_le"),

   Cases_on `bitv_binpred binop_ge p p'` >> (
    fs []
   ) >>
   Cases_on `x` >> (
    fs []
   ) >>
   irule ((valOf o find_clause_e_red) "e_ge"),

   Cases_on `bitv_binpred binop_lt p p'` >> (
    fs []
   ) >>
   Cases_on `x` >> (
    fs []
   ) >>
   irule ((valOf o find_clause_e_red) "e_lt"),

   Cases_on `bitv_binpred binop_gt p p'` >> (
    fs []
   ) >>
   Cases_on `x` >> (
    fs []
   ) >>
   irule ((valOf o find_clause_e_red) "e_gt"),

   irule ((valOf o find_clause_e_red) "e_neq_bool"),

   irule ((valOf o find_clause_e_red) "e_neq"),

   irule ((valOf o find_clause_e_red) "e_neq_error"),

   irule ((valOf o find_clause_e_red) "e_eq_bool"),

   irule ((valOf o find_clause_e_red) "e_eq"),

   irule ((valOf o find_clause_e_red) "e_eq_error"),

   irule ((valOf o find_clause_e_red) "e_and"),

   irule ((valOf o find_clause_e_red) "e_xor"),

   irule ((valOf o find_clause_e_red) "e_or")
 ] >> (
  fs [clause_name_def]
 ),

 (* Second operand is not fully reduced *)
 Cases_on `is_short_circuitable e1 b` >- (
  (* Short-circuit *)
  fs [] >>
  Cases_on `e1` >> (
   fs [is_v]
  ) >>
  rw [] >>
  Cases_on `v` >> (
   fs [is_short_circuitable]
  ) >>
  Cases_on `b'` >> Cases_on `b` >> (
   fs [is_short_circuitable, e_exec, is_v]
  ) >| [
  irule ((valOf o find_clause_e_red) "e_bin_or1") >>
  fs [clause_name_def],
  
  irule ((valOf o find_clause_e_red) "e_bin_and1") >>
  fs [clause_name_def]
  ]
 ) >>
 Cases_on `e_exec ctx g_scope_list scopes_stack e2` >> (
  fs [e_exec]
 ) >>
 Cases_on `x` >> Cases_on `e1` >> (
  fs [is_v]
 ) >>
 METIS_TAC [((valOf o find_clause_e_red) "e_binop_arg2"), clause_name_def],

 (* First operand is not fully reduced *)
 Cases_on `e_exec ctx g_scope_list scopes_stack e1` >> (
  fs [e_exec]
 ) >>
 Cases_on `x` >>
 fs [] >>
 METIS_TAC [((valOf o find_clause_e_red) "e_binop_arg1"), clause_name_def],

 (* No operand is fully reduced *)
 Cases_on `e_exec ctx g_scope_list scopes_stack e1` >> (
  fs [e_exec]
 ) >>
 Cases_on `x` >>
 fs [] >>
 METIS_TAC [((valOf o find_clause_e_red) "e_binop_arg1"), clause_name_def]
]
QED

Theorem e_unop_exec_sound_red:
!e u.
e_exec_sound e ==>
e_exec_sound (e_unop u e)
Proof
fs [e_exec_sound] >>
REPEAT STRIP_TAC >>
Cases_on `is_v e` >| [
 Cases_on `e_exec_unop u e` >> (
  fs [e_exec] >>
  rw []
 ) >>
 Cases_on `e` >> (
  fs [is_v]
 ) >>
 (* Different concrete cases *)
 Cases_on `u` >> (
  Cases_on `v` >> (
   fs [e_exec_unop, unop_exec]
  ) >>
  rw []
 ) >| [
  irule ((valOf o find_clause_e_red) "e_neg_bool"),

  irule ((valOf o find_clause_e_red) "e_compl"),

  irule ((valOf o find_clause_e_red) "e_neg_signed"),

  irule ((valOf o find_clause_e_red) "e_un_plus")
 ] >>
 fs [clause_name_def],

 Cases_on `e_exec ctx g_scope_list scopes_stack e` >> (
  fs [e_exec]
 ) >>
 Cases_on `x` >>
 fs [] >>
 METIS_TAC [(valOf o find_clause_e_red) "e_unop_arg", clause_name_def]
]
QED

Theorem e_exec_sound_red:
!e. e_exec_sound e
Proof
`(!e. e_exec_sound e) /\ (!l. l_sound l)` suffices_by (
 fs []
) >>
irule e_induction >>
REPEAT STRIP_TAC >| [
 (* e list *)
 fs [l_sound],

 (* bitvector slice - not in exec sem yet *)
 fs [e_exec_sound, e_exec],

 (* Field access *)
 fs [e_acc_exec_sound_red],

 (* bitvector concatenation - not in exec sem yet *)
 fs [e_exec_sound, e_exec],

 (* Binary operation *)
 fs [e_binop_exec_sound_red],

 (* execution of e lists? *)
 fs [l_sound],

 (* Select expression *)
 (* TODO *)
 cheat,

 (* Unary operation *)
 fs [e_unop_exec_sound_red],

 (* List expression - not in exec sem yet *)
 fs [e_exec_sound, e_exec],

 (* Function/extern call *)
 (* TODO *)
 cheat,

 (* TODO: Constant value - how should this be handled in reductions? *)
 cheat,

 (* Variable lookup *)
 fs [e_exec_sound, e_exec] >>
 REPEAT STRIP_TAC >>
 Cases_on `lookup_vexp2 scopes_stack g_scope_list v` >> (
  fs []
 ) >>
 rw [] >>
 METIS_TAC [(valOf o find_clause_e_red) "e_lookup", clause_name_def]
]
QED

Theorem stmt_exec_sound_red:
!stmt. stmt_exec_sound stmt
Proof
ASSUME_TAC e_exec_sound_red >>
irule stmt_induction >>
REPEAT STRIP_TAC >| [
 (* TODO: Empty statement - how should this be handled in reductions? *)
 cheat,

 (* Return statement *)
 (* TODO *)
 cheat,

 (* Transition statement *)
 (* TODO *)
 cheat,

 (* Verify statement *)
 fs [stmt_verify_exec_sound_red],

 (* Extern *)
 (* TODO *)
 cheat,

 (* Apply statement *)
 (* TODO *)
 cheat,

 (* Assign statement *)
 (* TODO *)
 cheat,

 (* Sequence of statements *)
 (* TODO *)
 cheat,

 (* Conditional statement *)
 (* TODO *)
 cheat,

 (* Block entry *)
 fs [stmt_block_exec_sound_red],

 (* Block execution in-progress *)
 fs [stmt_block_ip_exec_sound_red],

 (* Declare statement *)
 (* TODO *)
 cheat
]
QED


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
 (pars_exec (ty_map, ext_map, func_map, pars_map) (g_scope_list, frame_list, ctrl, status_running) =
  (case stmt_exec (ty_map, ext_map, func_map, FEMPTY) (g_scope_list, frame_list, ctrl, status_running) of
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
 (arch_exec (actx:actx) ((aenv:aenv), (g_scope_list:g_scope_list) , (arch_frame_list:arch_frame_list) , (ctrl:ctrl), status_type_error) = NONE) /\
 (* arch_parser_ret: Note that this is a different clause from arch_control_ret due to the status *)
 (arch_exec (ab_list, pblock_map, ffblock_map, input_f, output_f, ty_map, ext_map, func_map)
            ((i, b, in_out_list, in_out_list', scope), g_scope_list,
             (arch_frame_list_regular [(funn, stmt, scopes_stack)]), ctrl,
             (status_pars_next (pars_next_pars_fin pars_fin))) =
  if b /\ (is_empty stmt) then
   (case EL i ab_list of
    | (arch_block_pbl x el) =>
     (case FLOOKUP pblock_map x of
      | SOME (pblock_parser x_d_list stmt pars_map) =>
       (case update_return_frame (MAP FST x_d_list) (MAP SND x_d_list) [scope] (g_scope_list++scopes_stack) of
        | SOME [scope'] =>
         (case lookup_vexp (g_scope_list++scopes_stack) (varn_name "parseError") of
          | SOME v =>
           (case assign [scope'] v (lval_varname (varn_name "parseError")) of
            | SOME [scope''] =>
             SOME ((i+1, F, in_out_list, in_out_list', scope''), TAKE 1 g_scope_list,
                   arch_frame_list_empty, ctrl, status_running)
            | _ => NONE)
          | _ => NONE)
        | _ => NONE)
      | _ => NONE)
    | _ => NONE)
   else NONE)
 /\
 (arch_exec (ab_list, pblock_map, ffblock_map, input_f, output_f, ty_map, ext_map, func_map)
            ((i, T, in_out_list, in_out_list', scope), g_scope_list,
             (arch_frame_list_regular [(funn, stmt_empty, scopes_stack)]), ctrl, status_running) =
 (* arch_control_ret *)
  (case EL i ab_list of
   | (arch_block_pbl x el) =>
    (case FLOOKUP pblock_map x of
     | SOME (pblock_control x_d_list stmt stmt' tbl_map) =>
      (case update_return_frame (MAP FST x_d_list) (MAP SND x_d_list) [scope] (g_scope_list++scopes_stack) of
       | SOME [scope'] =>
        SOME ((i+1, F, in_out_list, in_out_list', scope'), (TAKE 1 g_scope_list),
               arch_frame_list_empty, ctrl, status_running)
       | _ => NONE)
     | _ => NONE)
   | _ => NONE)
 )
 /\
 (arch_exec (ab_list, pblock_map, ffblock_map, input_f, output_f, ty_map, ext_map, func_map)
            ((i, F, in_out_list, in_out_list', scope), g_scope_list,
             arch_frame_list_empty, ctrl, status_running) =
  (* arch_in, arch_pbl_call, arch_ffbl_call, arch_out *)
  (case EL i ab_list of
   | arch_block_inp =>
    (case input_f (in_out_list, scope) of
     | SOME (in_out_list'', scope') => 
      SOME ((i+1, F, in_out_list'', in_out_list', scope'), g_scope_list, arch_frame_list_empty,
             ctrl, status_running)
     | NONE => NONE)
   | (arch_block_pbl x el) =>
    SOME ((i, T, in_out_list, in_out_list', scope), g_scope_list, arch_frame_list_pbl_call x el, ctrl, status_running)
   | (arch_block_ffbl x el) =>
    SOME ((i, F, in_out_list, in_out_list', scope), g_scope_list, arch_frame_list_ffbl_call x el, ctrl, status_running)
   | arch_block_out =>
    (case output_f (in_out_list', scope) of
     | SOME (in_out_list'', scope') =>
      SOME ((0, F, in_out_list, in_out_list'', scope'), g_scope_list, arch_frame_list_empty, ctrl,
            status_running)
     | NONE => NONE)
  )
 )
/\
 (* Operating on a stmt_pbl_call: arch_parser_init, arch_control_init, arch_pblock_args *)
 (* TODO: Would be nice to remove code duplication... *)
 (arch_exec (ab_list, pblock_map, ffblock_map, input_f, output_f, ty_map, ext_map, func_map)
            ((i, T, in_out_list, in_out_list', scope), g_scope_list,
             arch_frame_list_pbl_call f el, ctrl, status_running) =
  (case FLOOKUP pblock_map f of
   | SOME (pblock_control x_d_list stmt stmt' tbl_map) =>
    (case unred_arg_index (MAP SND x_d_list) el of
     | SOME i' => (* arch_pblock_args (case control) *)
      (case e_exec (ty_map, ext_map, func_map, tbl_map) g_scope_list [scope] (EL i' el) of
       (* Note that this excludes function calls *)
       | SOME (e', []) =>
        SOME ((i, T, in_out_list, in_out_list', scope), g_scope_list, arch_frame_list_pbl_call f (LUPDATE e' i' el), ctrl, status_running)
       | _ => NONE)
     | NONE => (* arch_control_init *)
      (case all_arg_update_for_newscope (MAP FST x_d_list) (MAP SND x_d_list) el [scope] of
       | SOME scope' =>
        SOME ((i, T, in_out_list, in_out_list', scope), (g_scope_list++[scope']),
              arch_frame_list_regular [(funn_name f, stmt_seq stmt stmt', [])], ctrl, status_running)
       | _ => NONE)
    )
   | SOME (pblock_parser x_d_list stmt pars_map) =>
    (case (unred_arg_index (MAP SND x_d_list) el) of
     | SOME i' => (* arch_pblock_args (case parser) *)
      (case e_exec (ty_map, ext_map, func_map, FEMPTY) g_scope_list [scope] (EL i' el) of
       (* Note that this excludes function calls *)
       | SOME (e', []) =>
        SOME ((i, T, in_out_list, in_out_list', scope), g_scope_list, 
              arch_frame_list_pbl_call f (LUPDATE e' i' el), ctrl, status_running)
       | _ => NONE)
     | NONE => (* arch_parser_init *)
      (case FLOOKUP pars_map "start" of
       | SOME stmt' =>
        (case all_arg_update_for_newscope (MAP FST x_d_list) (MAP SND x_d_list) el [scope] of
         | SOME scope' =>
          (let block_global_scope_sing = initialise [scope'] (varn_name "parseError") (v_err "NoError") in
            SOME ((i, T, in_out_list, in_out_list', scope), (g_scope_list++block_global_scope_sing),
                  arch_frame_list_regular [(funn_name f, stmt_seq stmt stmt', [])], ctrl, status_running))
         | NONE => NONE)
       | NONE => NONE)
    )
   | _ => NONE)
 )
 /\
 (* Operating on a stmt_ffbl_call: arch_ffblock_exec, arch_ffblock_args *)
 (arch_exec (ab_list, pblock_map, ffblock_map, input_f, output_f, ty_map, ext_map, func_map)
            ((i, F, in_out_list, in_out_list', scope), g_scope_list, arch_frame_list_ffbl_call f el,
             ctrl, status_running) =
  (case FLOOKUP ffblock_map f of
   | SOME (ffblock_ff ff x_d_list) =>
    (case unred_arg_index (MAP SND x_d_list) el of
     | SOME i' =>
      (case e_exec (ty_map, ext_map, func_map, FEMPTY) g_scope_list [scope] (EL i' el) of
       (* Note that this excludes function calls *)
       | SOME (e', []) =>
          SOME ((i, F, in_out_list, in_out_list', scope), g_scope_list, 
                arch_frame_list_ffbl_call f (LUPDATE e' i' el), ctrl, status_running)
       | NONE => NONE)
     | NONE =>
      (case ff (el, scope) of
       | SOME scope' =>
        SOME ((i+1, F, in_out_list, in_out_list', scope'), g_scope_list,
              arch_frame_list_empty, ctrl, status_running)
       | _ => NONE)
   | _ => NONE)
  )
 )
 /\
 (* Operating on any other statement: arch_parser_exec, arch_control_exec *)
 (arch_exec (ab_list, pblock_map, ffblock_map, input_f, output_f, ty_map, ext_map, func_map)
            ((i, T, in_out_list, in_out_list', scope), g_scope_list, (arch_frame_list_regular frame_list), ctrl, status) =
  (case EL i ab_list of
   | (arch_block_pbl x el) =>
    (case FLOOKUP pblock_map x of
     | SOME (pblock_parser x_d_list stmt'' pars_map) =>
      (case pars_exec (ty_map, ext_map, func_map, pars_map) (g_scope_list, frame_list, ctrl, status) of
       | SOME (g_scope_list', frame_list', ctrl', status') =>
        SOME ((i, T, in_out_list, in_out_list', scope), g_scope_list', (arch_frame_list_regular frame_list'), ctrl', status')
       | _ => NONE)
     | SOME (pblock_control x_d_list stmt'' stmt''' tbl_map) =>
      (case ctrl_exec (ty_map, ext_map, func_map, tbl_map) (g_scope_list, frame_list, ctrl, status) of
       | SOME (g_scope_list', frame_list', ctrl', status') =>
        SOME ((i, T, in_out_list, in_out_list', scope), g_scope_list', (arch_frame_list_regular frame_list'), ctrl', status')
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
