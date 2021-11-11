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


val sum_size_def = Define `
 (sum_size (INL ((ctx:ctx), e, (stacks:stacks), (status:status))) = e_size e) /\
 (sum_size (INR ((ctx:ctx), stmt, (stacks:stacks), (status:status))) = stmt_size stmt)
`;

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
 Cases_on `INDEX_FIND 0 (\(d,e). is_d_none_in d /\ ~is_const e) (ZIP (d_l,e_l))` >> (
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

Definition is_var:
 (is_var (e_var x) = T) /\
 (is_var _ = F)
End

Definition is_empty:
 (is_empty stmt_empty = T) /\
 (is_empty _ = F)
End

(*****************************)
(* Status-related shorthands *)

Definition e_exec_return:
 (e_exec_return (e_func_exec stmt_empty) stacks v = SOME (e_v v, stacks, status_running)) /\
 (e_exec_return _ _ _ = NONE)
End

Definition stmt_exec_return:
 (stmt_exec_return (e_func_exec stmt_empty) stacks v = SOME (e_v v, stacks, status_running)) /\
 (stmt_exec_return _ _ _ = NONE)
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
 (* TODO: This might generalize easily... *)
 (binop_exec binop_neq (v_bit bitv1) (v_bit bitv2) =
  SOME (v_bool (bitv1 <> bitv2)))
 /\
 (binop_exec binop_neq (v_bool b1) (v_bool b2) =
  SOME (v_bool (b1 <> b2)))
 /\
 (binop_exec binop_eq (v_bit bitv1) (v_bit bitv2) =
  SOME (v_bool (bitv1 = bitv2)))
 /\
 (binop_exec binop_eq (v_bool b1) (v_bool b2) =
  SOME (v_bool (b1 = b2)))
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
 (is_short_circuitable (v_bool F) binop_bin_and = T) /\
 (is_short_circuitable (v_bool T) binop_bin_or = T) /\
 (is_short_circuitable _ _ = F)
End

Definition short_circuit:
 (short_circuit binop_bin_and stacks status = SOME (e_v (v_bool F), stacks, status)) /\
 (short_circuit binop_bin_or stacks status = SOME (e_v (v_bool T), stacks, status)) /\
 (short_circuit _ _ _ = NONE)
End

Definition short_circuit:
 (short_circuit binop_bin_and stacks status = SOME (e_v (v_bool F), stacks, status)) /\
 (short_circuit binop_bin_or stacks status = SOME (e_v (v_bool T), stacks, status)) /\
 (short_circuit _ _ _ = NONE)
End

Definition e_exec_binop:
 (e_exec_binop (e_v v1) binop (e_v v2) = binop_exec binop v1 v2)
  /\
 (e_exec_binop _ _ _ = NONE)
End

(* Field access *)
Definition e_exec_acc:
 (e_exec_acc (e_acc (e_v (v_struct f_v_list)) (e_var f)) stacks status =
  case FIND (\(k, v). k = f) f_v_list of
  | SOME (f, v) => SOME (e_v v, stacks, status)
  | NONE => NONE)
  /\
 (e_exec_acc (e_acc (e_v (v_header boolv f_v_list)) (e_var f)) stacks status =
  case FIND (\(k, v). k = f) f_v_list of
  | SOME (f, v) => SOME (e_v v, stacks, status)
  | NONE => NONE)
  /\
 (e_exec_acc _ _ _ = NONE)
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
 (stmt_exec_ass lval (e_v v) frame =
  assign frame v lval)
  /\
 (stmt_exec_ass _ _ _ = NONE)
End

Definition stmt_exec_verify:
 (stmt_exec_verify (e_v (v_bool T)) (e_v (v_err x)) =
  SOME stmt_empty)
  /\
 (stmt_exec_verify (e_v (v_bool F)) (e_v (v_err x)) =
  SOME (stmt_seq (stmt_ass (lval_varname "parseError") ((e_v (v_err x)))) (stmt_trans (e_var "Reject"))))
  /\
 (stmt_exec_verify _ _ = NONE)
End

Definition stmt_exec_trans:
 (stmt_exec_trans (e_var x) =
  if x = "accept"
  then SOME (status_pars_next (pars_next_pars_fin pars_finaccept))
  else if x = "reject"
  then SOME (status_pars_next (pars_next_pars_fin pars_finreject))
  else SOME (status_pars_next (pars_next_trans x)))
  /\
 (stmt_exec_trans _ = NONE)
End

Definition stmt_exec_ret:
 (stmt_exec_ret frame call_stack (func_map:func_map) (e_v v) =
  case call_stack of
  | ((frame', called_function_name_bot)::call_stack') => NONE
  | ((frame', called_function_name_function_name f)::call_stack') =>
   (case FLOOKUP func_map f of
   | SOME (_, x_d_l) =>
    (case update_return_frame (MAP FST x_d_l) (MAP SND x_d_l) ((HD frame)::frame') frame of
     | SOME frame'' => SOME (stmt_empty, (stacks_tup frame'' call_stack'), status_return v)
     | NONE => NONE)
   | NONE => NONE)
  | [] => NONE) /\
 (stmt_exec_ret _ _ _ _ = NONE)
End

(* TODO: Write explicit NONE-reducing clauses for operands of wrong types?
 *       This would reduce warnings *)
(* TotalDefn.tDefine "e_stmt_exec" *)
(* TotalDefn.multiDefine *)
(* Hol_defn "e_stmt_exec" *)
val e_stmt_exec_def = TotalDefn.tDefine "e_stmt_exec" `
 (******************************************)
 (* Clauses for special statuses *)
 (e_exec _ e stacks status_type_error = NONE)
  /\
 (e_exec _ e stacks (status_return v) =
  e_exec_return e stacks v)
  /\
 (* TODO: Should expressions with status pars_next x be reduced
  * to some value, with status preserved? *)
 (e_exec _ e stacks (status_pars_next x) =
  SOME (e_v v_bot, stacks, status_pars_next x))
  /\
 (* e_v is the fully reduced form of expression *)
 (e_exec _ (e_v v) stacks status =
  SOME (e_v v, stacks, status))
  /\
 (* Note that at this point, status_running is the sole remaining
  * possible status argument for all other clauses *)
 (********************)
 (* Variable look-up *)
 (e_exec _ (e_var x) (stacks_tup curr_stack_frame call_stack) status_running =
  SOME (e_v (lookup_vexp curr_stack_frame (e_var x)), stacks_tup curr_stack_frame call_stack, status_running))
  /\
 (***********************)
 (* Struct/header field access *)
 (e_exec ctx (e_acc e_struct e_field) stacks status =
  if is_var e_field
  then
   if is_v e_struct
   then
    (case e_exec_acc (e_acc e_struct e_field) stacks status of
     | SOME res => SOME res
     | NONE => NONE)
   else
    (case e_exec ctx e_struct stacks status of
     | SOME (e_struct', stacks', status') => SOME (e_acc e_struct' e_field, stacks', status')
     | NONE => NONE)
  else
   (case e_exec ctx e_field stacks status of
    | SOME (e_field', stacks', status') => SOME (e_acc e_struct e_field', stacks', status')
    | NONE => NONE))
  /\
 (*************************)
 (* Function call-related *)
 (e_exec ((type_map, ext_map, func_map, pars_map, t_map, ctrl):ctx) (e_func_call f e_l) (stacks_tup curr_stack_frame call_stack) status =
  case FLOOKUP func_map f of
  | SOME (stmt, x_d_l) =>
    (case unred_arg_index (MAP SND x_d_l) e_l of
     | SOME i  =>
      (case e_exec ((type_map, ext_map, func_map, pars_map, t_map, ctrl):ctx) (EL i e_l) (stacks_tup curr_stack_frame call_stack) status of
       | SOME (e', stacks', status') => SOME (e_func_call f (LUPDATE e' i e_l), stacks', status')
       | NONE => NONE)
     | NONE =>
      SOME (e_func_exec stmt,
	    stacks_tup ([EL 0 curr_stack_frame]++[all_arg_update_for_newscope (MAP FST x_d_l) (MAP SND x_d_l) e_l curr_stack_frame])
		       ((TL curr_stack_frame, called_function_name_function_name f)::call_stack),
	    status))
  | NONE => NONE)
  /\
 (e_exec ctx (e_func_exec stmt) stacks status =
  case stmt_exec ctx stmt stacks status of
  | SOME (stmt', stacks', status') => SOME (e_func_exec stmt', stacks', status')
  | NONE => NONE)
  /\
 (******************)
 (* Extern-related *)
 (e_exec ((type_map, ext_map, func_map, pars_map, t_map, ctrl):ctx) (e_ext_call x f e_l) (stacks_tup curr_stack_frame call_stack) status =
  case FLOOKUP ext_map f of
  | SOME (ext, x_d_l) =>
    (case unred_arg_index (MAP SND x_d_l) e_l of
     | SOME i  =>
      (case e_exec ((type_map, ext_map, func_map, pars_map, t_map, ctrl):ctx) (EL i e_l) (stacks_tup curr_stack_frame call_stack) status of
       | SOME (e', stacks', status') => SOME (e_ext_call x f (LUPDATE e' i e_l), stacks', status')
       | NONE => NONE)
     | NONE =>
      (case ext (x, e_l, state_tup (stacks_tup curr_stack_frame call_stack) status) of
       | SOME (state_tup stacks' status') => 
	SOME (e_v v_bot, stacks', status')
       | NONE => NONE
      )
    )
  | NONE => NONE)
  /\
 (********************)
 (* Unary arithmetic *)
 (e_exec ctx (e_unop unop e) stacks status =
  if is_v e
  then 
   (case e_exec_unop unop e of
    | SOME v => SOME (e_v v, stacks, status)
    | NONE => NONE)
  else
   (case e_exec ctx e stacks status of
    | SOME (e', stacks', status') => SOME (e_unop unop e', stacks', status')
    | NONE => NONE))
  /\
 (*********************)
 (* Binary arithmetic *)
 (e_exec ctx (e_binop e1 binop e2) stacks status =
  if is_v e1
  then
   if is_v e2
   then 
    (case e_exec_binop e1 binop e2 of
     | SOME v => SOME (e_v v, stacks, status)
     | NONE => NONE)
   else
    (case e_exec ctx e2 stacks status of
     | SOME (e2', stacks', status') => SOME (e_binop e1 binop e2', stacks', status')
     | NONE => NONE)
  else
   (case e_exec ctx e1 stacks status of
    | SOME (e1', stacks', status') => SOME (e_binop e1' binop e2, stacks', status')
    | NONE => NONE))
  /\
 (**********)
 (* Select *)
 (e_exec ctx (e_select e v_x_l x) stacks status =
  if is_v e
  then
    (case e_exec_select e v_x_l x of
     | SOME x' => SOME (e_var x', stacks, status)
     | NONE => NONE)
  else
   (case e_exec ctx e stacks status of
    | SOME (e', stacks', status') => SOME (e_select e' v_x_l x, stacks', status')
    | NONE => NONE))
  /\
 (e_exec _ _ _ _ = NONE)
  /\
 (**************)
 (* Statements *)
 (**************)
 (******************************************)
 (* Catch-all clauses for special statuses *)
 (stmt_exec _ stmt stacks status_type_error = NONE)
  /\
(* TODO: Commented out, for now. Maybe some way can be found to avoid
 * duplication of clauses for return status...
 (stmt_exec _ stmt stacks (status_return v) =
  SOME (stmt_empty, stacks, status_return v))
  /\
*)
 (stmt_exec _ stmt stacks (status_pars_next x) =
  SOME (stmt_empty, stacks, status_pars_next x))
  /\
 (* empty_stmt is the fully reduced form of statement *)
 (stmt_exec _ stmt_empty stacks status = SOME (stmt_empty, stacks, status)) /\
 (*************************)
 (* Function call-related *)
 (stmt_exec ((type_map, ext_map, func_map, pars_map, t_map, ctrl):ctx) (stmt_ret e) (stacks_tup curr_stack_frame call_stack) status =
  if is_v e
  then
   stmt_exec_ret curr_stack_frame call_stack func_map e
  else
   (case e_exec ((type_map, ext_map, func_map, pars_map, t_map, ctrl):ctx) e (stacks_tup curr_stack_frame call_stack) status of
    | SOME (e', stacks', status') => SOME (stmt_ret e', stacks', status')
    | NONE => NONE))
  /\
 (**************)
 (* Assignment *)
 (stmt_exec ctx (stmt_ass lval e) (stacks_tup curr_stack_frame call_stack) status =
  if is_v e
  then
   (case stmt_exec_ass lval e curr_stack_frame of
    | SOME (curr_stack_frame') => SOME (stmt_empty, stacks_tup curr_stack_frame' call_stack, status)
    | NONE => NONE)
  else
   (case e_exec ctx e (stacks_tup curr_stack_frame call_stack) status of
    | SOME (e', stacks', status') => SOME (stmt_ass lval e', stacks', status')
    | NONE => NONE))
  /\
 (**********)
 (* Verify *)
 (stmt_exec ctx (stmt_verify e1 e2) stacks status =
  if is_v e1
  then
   if is_v e2
   then
    (case stmt_exec_verify e1 e2 of
     | SOME stmt => SOME (stmt, stacks, status)
     | NONE => NONE)
   else
    (case e_exec ctx e2 stacks status of
     | SOME (e2', stacks', status') => SOME (stmt_verify e1 e2', stacks', status')
     | NONE => NONE)
  else
   (case e_exec ctx e1 stacks status of
    | SOME (e1', stacks', status') => SOME (stmt_verify e1' e2, stacks', status')
    | NONE => NONE))
  /\
 (**************)
 (* Transition *)
 (**************)
 (stmt_exec ctx (stmt_trans e) stacks status =
  if is_var e
  then
   (case stmt_exec_trans e of
    | SOME status' => SOME (stmt_empty, stacks, status')
    | NONE => NONE)
  else
   (case e_exec ctx e stacks status of
    | SOME (e', stacks', status') => SOME (stmt_trans e', stacks', status')
    | NONE => NONE))
  /\
 (* Sequence *)
 (stmt_exec ctx (stmt_seq stmt1 stmt2) stacks status =
  if is_empty stmt1
  then SOME (stmt2, stacks, status)
  else
   (case stmt_exec ctx stmt1 stacks status of
    | SOME (stmt1', stacks', status') => SOME (stmt_seq stmt1' stmt2, stacks', status')
    | NONE => NONE))
  /\
 (stmt_exec _ _ _ _ = NONE)
`
(WF_REL_TAC `measure sum_size` >>
 fs [sum_size_def, e_size_def] >>
 REPEAT STRIP_TAC >>
 IMP_RES_TAC unred_arg_index_in_range >>
 IMP_RES_TAC rich_listTheory.EL_MEM >>
 IMP_RES_TAC e1_size_mem >>
 fs [])
;

(* Only meant to skip certain soundness proof parts for now *)
Theorem ignore_pars_next:
 !ctx e e' stacks stacks' p status'.
  e_red ctx e stacks (status_pars_next p) e' stacks' status'
Proof
cheat
QED

(* Then, some kind of theorem that states equivalence
 * between executable semantics and ott-exported reduction rules.
 * For sketch, only soundness and not completeness *)
(* TODO: Completeness *)
Theorem e_exec_sound_red:
 !ctx (e:e) (e':e) stacks stacks' status status'.
  e_exec ctx e stacks status = SOME (e', stacks', status') ==>
  e_red ctx e stacks status e' stacks' status'
Proof
(* NOTE: Use something like

   (valOf o find_clause_e_red) "e_neg_bool"

   to find clauses in Ott-exported reduction rules.

   Should be around 9 subgoals with the below, corresponding
   roughly to the different expressions:
*)
STRIP_TAC >>
Induct_on `e` >> Cases_on `status` >> (
 (* TODO: Remove ignore_pars_next *)
 fs [e_stmt_exec_def, e_exec_return, ignore_pars_next]
) >| [
 (* TODO: e_v to e_v - should this be among the inference rules? *)
 cheat,

 (* Variable lookup - how is variable name related to reduced expression? *)
 Cases_on `stacks` >>
 fs [e_stmt_exec_def] >>
 REPEAT STRIP_TAC >>
 irule ((valOf o find_clause_e_red) "e_lookup") >>
 fs [clause_name_def], 

 (* Field access *)
 REPEAT STRIP_TAC >>
 Cases_on `stacks` >>
 Cases_on `is_v e` >> Cases_on `is_var e'` >- (
  (* 1st case is base case *)
  Cases_on `e` >>  Cases_on `e'` >> (
   fs [is_v, is_var, e_stmt_exec_def]
  ) >>
  Cases_on `v` >> (
   fs [e_stmt_exec_def, e_exec_acc]
  ) >> (
   Cases_on `FIND (\(k,v). k = s) l'`
  ) >> (
   fs []
  ) >> (
   Cases_on `x`
  ) >> (
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
  )
 ) >- (
  (* Second case is reduction of 2nd argument (field name) *)
  fs [] >>
  Cases_on `e_exec ctx e' (stacks_tup l l0) status_running` >> (
   fs []
  ) >>
  Cases_on `x` >> Cases_on `r` >>
  fs [] >>
  rw [] >>
  irule ((valOf o find_clause_e_red) "e_acc_arg2") >>
  fs [clause_name_def]
 ) >| [
  (* Third case is reduction of 1st argument (struct value) *)
  fs [] >>
  Cases_on `e_exec ctx e (stacks_tup l l0) status_running` >> (
   fs []
  ) >>
  Cases_on `x` >> Cases_on `r` >>
  fs [] >>
  rw [] >>
  Cases_on `e'` >> (
   fs [is_var]
  ) >>
  irule ((valOf o find_clause_e_red) "e_acc_arg1") >>
  fs [clause_name_def],

  (* Fourth (inductive) case determines case when both arguments are unreduced *)
  fs [] >>
  Cases_on `e_exec ctx e' (stacks_tup l l0) status_running` >> (
   fs []
  ) >>
  Cases_on `x` >> Cases_on `r` >>
  fs [] >>
  rw [] >>
  irule ((valOf o find_clause_e_red) "e_acc_arg2") >>
  RES_TAC >>
  fs [clause_name_def]
 ],

 (* Unary operations *)
 cheat,

 (* Binary operations *)
 cheat,

 (* Function call *)
 cheat,

 (* Function body execution *)
 cheat,

 (* Function body return *)
 cheat,

 (* Extern call *)
 cheat,

 (* Select expression *)
 cheat
]
QED

Theorem stmt_exec_sound_red:
 !ctx (stmt:stmt) (stmt':stmt) stacks stacks' status status'.
  stmt_exec ctx stmt stacks status = SOME (stmt', stacks', status) ==>
   stmt_red ctx stmt (state_tup stacks status) stmt' (state_tup stacks' status')
Proof
cheat
QED

(* Then, define an executable semantics which performs execution until out of fuel. *)
(* Note that all concrete operations remain the same *)
val [e_multi_exec, stmt_multi_exec] = TotalDefn.multiDefine `
 (e_multi_exec _ e stacks status 0 =
  SOME (e, stacks, status))
  /\
 (e_multi_exec ctx e stacks status (SUC fuel) =
  case e_exec ctx e stacks status of
  | SOME (e', stacks', status') => e_multi_exec ctx e' stacks' status' fuel
  | NONE => NONE)
 /\
 (stmt_multi_exec _ stmt stacks status 0 =
  SOME (stmt, stacks, status))
 /\
 (stmt_multi_exec ctx stmt stacks status (SUC fuel) =
  case stmt_exec ctx stmt stacks status of
  | SOME (stmt', stacks', status') => stmt_multi_exec ctx stmt' stacks' status' fuel
  | NONE => NONE)
`;

(* TEST

val bl0 = mk_v_bitii (0, 32);
val bl1 = mk_v_bitii (1, 32);
val bl2 = mk_v_bitii (16384, 32);

val func_map = ``FEMPTY |+ ("f_x", (stmt_seq (stmt_ass (lval_varname "x_inout") (e_v (^bl1))) (stmt_ret (e_v v_bot))), ["x_inout", d_inout])``;
val ctx = pairSyntax.list_mk_pair [``FEMPTY:type_map``, func_map, ``FEMPTY:pars_map``, ``FEMPTY:t_map``, ``FEMPTY:ctrl``];

val stacks = ``stacks_tup ([FEMPTY |+ ("x", ((^bl0), NONE))]:scope list) ([]:call_stack)``;
val status = ``status_running``;

(* Nested unary operations *)
val e_un = ``(e_unop unop_compl (e_unop unop_compl (e_v (^bl1))))``;
EVAL ``e_multi_exec (^ctx) (^e_un) (^stacks) (^status) 20``;

(* Single statements *)
EVAL ``stmt_multi_exec (^ctx) (stmt_ass lval_null (^e_un)) (^stacks) (^status) 20``;

(* TODO: Simplifying multiple updates to the same finite map? *)
EVAL ``stmt_multi_exec (^ctx) (stmt_ass (lval_varname "x") (^e_un)) (^stacks) (^status) 20``;

(* Sequence of statements *)
EVAL ``stmt_multi_exec (^ctx) (stmt_seq (stmt_ass (lval_varname "x") (^e_un)) (stmt_ass (lval_varname "x") (e_v (^bl2)) )) (^stacks) (^status) 20``;

(* Function call *)
EVAL ``stmt_multi_exec (^ctx) (stmt_ass lval_null (e_func_call "f_x" [e_var "x"])) (^stacks) (^status) 20``;

(* Nested binary operations *)
EVAL ``e_multi_exec (^ctx) (e_binop (e_v (^bl1)) binop_add (e_v (^bl2))) (^stacks) (^status) 20``;

(* Stack assignment *)
val stacks' = ``stacks_tup ([FEMPTY |+ ("x", ((v_struct [("f", (^bl0))]), NONE))]:scope list) ([]:call_stack)``;

EVAL ``stmt_multi_exec (^ctx) (stmt_ass (lval_field (lval_varname "x") "f") (e_v (^bl1))) (^stacks') (^status) 20``;

*)
        
(* Then, define the closure of the small step reduction. *)

val (e_clos_sem_rules, e_clos_sem_ind, e_clos_sem_cases) = Hol_reln`
(* Base clause: *)
(! ctx (e:e) stacks (e':e) (stacks':stacks).
( ( e_red ctx e stacks status_running e' stacks' status_running )) ==> 
( ( e_clos_red ctx e stacks status_running e' stacks' status_running )))
(* Inductive clause: *)
/\ (! ctx (e:e) stacks (e':e) (stacks':stacks) (e'':e) (stacks'':stacks).
(( ( e_red ctx e stacks status_running e' stacks' status_running )) /\ 
( ( e_clos_red ctx e' stacks' status_running e'' stacks'' status_running ))) ==> 
( ( e_clos_red ctx e stacks status_running e'' stacks'' status_running )))
`;

val (stmt_clos_sem_rules, stmt_clos_sem_ind, stmt_clos_sem_cases) = Hol_reln`
(* Base clause: *)
(! ctx (stmt:stmt) (state:state) (stmt':stmt) (state':state).
( ( stmt_red ctx stmt state stmt' state' )) ==> 
( ( stmt_clos_red ctx stmt state stmt' state' )))
(* Inductive clause: *)
/\ (! ctx (stmt:stmt) (state:state) (stmt':stmt) (state':state) (stmt'':stmt) (state'':state).
(( ( stmt_red ctx stmt state stmt' state' )) /\ 
( ( stmt_clos_red ctx stmt' state' stmt'' state'' ))) ==> 
( ( stmt_clos_red ctx stmt state stmt'' state'' )))
`;

(* Then, prove that the multi-step executable semantics is sound with respect to the
 * closure of the small-step reduction *)

Theorem e_multi_exec_sound_red:
 !ctx (e:e) (e':e) stacks status stacks' status' fuel.
  e_multi_exec ctx  e stacks status fuel = SOME (e', stacks', status') ==>
  e_clos_red ctx e stacks status e' stacks' status'
Proof
 cheat
QED

Theorem stmt_multi_exec_sound_red:
 !ctx (stmt:stmt) (stmt':stmt) stacks status stacks' status' fuel.
  stmt_multi_exec ctx stmt stacks status fuel = SOME (stmt', stacks', status') ==>
  stmt_clos_red ctx stmt (state_tup stacks status) stmt' (state_tup stacks' status')
Proof
 cheat
QED

(* The executable semantics of the parser is defined in terms of the executable semantics of
 * statements *)
val pars_exec_def = Define `
 (pars_exec (type_map,ext_map,func_map,pars_map,t_map,ctrl) stmt stacks status =
  case stmt_exec (type_map,ext_map,func_map,pars_map,t_map,ctrl) stmt stacks status of
  | SOME (stmt', stacks', status_pars_next (pars_next_trans x)) =>
   (case FLOOKUP pars_map x of
    | SOME stmt'' => SOME (stmt', stacks', status_running)
    | NONE => NONE)
  | SOME (stmt_empty, stacks', status_running) =>
   SOME (stmt_trans (e_var "reject"), stacks', status_running)
  | SOME (stmt', stacks', status') =>
   SOME (stmt', stacks', status')
  | NONE => NONE
)
`;

(* Fuel-powered multi-step executable semantics for parsers *)
val pars_multi_exec = Define `
 (pars_multi_exec _ stmt stacks status 0 =
  SOME (stmt, stacks, status))
  /\
 (pars_multi_exec ctx stmt stacks status (SUC fuel) =
  case pars_exec ctx stmt stacks status of
  | SOME (stmt', stacks', status') => pars_multi_exec ctx stmt' stacks' status' fuel
  | NONE => NONE)
`;




(* Then, some kind of (multi-step) CakeML-adjusted executable semantics definition *)
(* TODO:
Definition e_exec_cake:
 (e_exec_cake (e_unop unop_neg (e_v (v_bool b))) stacks status =
   SOME (e_v (v_bool ~b)))
  /\
 (e_exec_cake (e_unop unop_compl (e_v (v_bit bitv))) stacks status =
  SOME (e_v (v_bit (bitv_bl_unop bnot bitv))))
  /\
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
