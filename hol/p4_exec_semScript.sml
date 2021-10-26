open HolKernel boolLib Parse bossLib;

val _ = new_theory "p4_exec_sem";

open p4Theory;
open ottTheory;
(* For EVAL-uating: *)
open blastLib bitstringLib;

(* TODO: Move to ottSyntax *)
val (clause_name_tm,  mk_clause_name, dest_clause_name, is_clause_name) =
  syntax_fns1 "ott"  "clause_name";

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

(***************************)

(* Examples of mutually recursive definitions:

val _ = Hol_datatype ` 
test_status =
   regular
 | finished
`;
val _ = Hol_datatype ` 
test_type =
   num of num
 | list2 of test_type list => test_type list
 | list1 of test_type list
 | list1_done of test_type list
 | list1_s of test_type list => test_status
`;

(***********************)
(* Using WIP function + new production: *)
val find_wip_def = Define `
  (find_wip (list1 l) =
    case (INDEX_FIND 0 (\tt. (tt = (num 0))) l) of
    | SOME (i, tt) => SOME i
    | NONE => NONE) /\
  (find_wip (list1_s l _) =
    case (INDEX_FIND 0 (\tt. (tt = (num 0))) l) of
    | SOME (i, tt) => SOME i
    | NONE => NONE)
`;
TotalDefn.multiDefine `
 (test_func1 (num (0:num))   = num 0) /\
 (test_func1 (num (SUC n))   = test_func2 (num n)) /\
 (test_func1 (list1 [])    = list1 []) /\
 (test_func1 (list1_done l)    = (list1_done l)) /\
 (test_func1 (list1 l) =
  case find_wip (list1 l) of
  | SOME i => (list1 (LUPDATE (test_func1 (EL i l)) i l))
  | NONE => (list1_done l)) /\
 (test_func2 (num (0:num)) = num 0) /\
 (test_func2 (num (SUC n)) = test_func1 (num n))
`; (* TERMINATION PROOF NEEDED! *)

(*************************)
(* Using also special status: *)
TotalDefn.multiDefine `
 (test_func1 (num (0:num))   = num 0) /\
 (test_func1 (num (SUC n))   = test_func2 (num n)) /\
 (test_func1 (list1_s l finished)      = list1 []) /\
 (test_func1 (list1_s l regular) =
  case find_wip (list1 l) of
  | SOME i => (list1_s (LUPDATE (test_func1 (EL i l)) i l) regular)
  | NONE => (list1_s l finished)) /\
 (test_func2 (num (0:num)) = num 0) /\
 (test_func2 (num (SUC n)) = test_func1 (num n))
`; (* TERMINATION PROOF NEEDED! *)

(********************)
(* Using two lists: *)
val is_wip_def = Define `
  (is_wip (num 0) = F) /\
  (is_wip _ = T)
`;
TotalDefn.multiDefine `
 (test_func1 (num (0:num))    = num 0) /\
 (test_func1 (num (SUC n))    = test_func2 (num n)) /\
 (test_func1 (list2 [] l)     = list2 [] l) /\
 (test_func1 (list2 (h::t) l) = if (is_wip h)
                                then (list2 ((test_func1 h)::t) l)
                                else list2 t (h::l)) /\
 (test_func2 (num (0:num)) = num 0) /\
 (test_func2 (num (SUC n)) = test_func1 (num n))
`; (* OK! *)

*)

(* NOTE: e_red is a small-step semantics *)

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
(*
 (binop_exec binop_bin_and (v_bool F) (v_bool b) =
  SOME (v_bool F))
 /\
 (binop_exec binop_bin_and (v_bool T) (v_bool b) =
  SOME (v_bool b))
 /\
*)
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

(* TODO: Write explicit NONE-reducing clauses for operands of wrong types?
 *       This would reduce the number of clauses pattern completion needs to add *)
(* TODO: Use "get_value" that obtains an option value from an expression? *)
(* 11 expressions, 11 statements => 22 clauses in definition, at minimum *)
(* TotalDefn.tDefine "e_stmt_exec" *)
(* TotalDefn.multiDefine *)
(* Hol_defn "e_stmt_exec" *)
val e_stmt_exec_defn = TotalDefn.tDefine "e_stmt_exec" `
 (* e_v is the fully reduced form of expression *)
 (e_exec _ (e_v v) stacks status =
  SOME ((e_v v), stacks, status))
  /\
 (********************)
 (* Variable look-up *)
 (e_exec _ (e_var x) (stacks_tup curr_stack_frame call_stack) status_running =
  SOME ((e_v (lookup_vexp curr_stack_frame (e_var x))), stacks_tup curr_stack_frame call_stack, status_running))
  /\
 (***********************)
 (* Struct field access *)
 (e_exec _ (e_acc (e_v (v_struct f_v_list)) (e_var f)) stacks status_running =
  case FIND (\(k, v). k = f) f_v_list of
  | SOME (f, v) => SOME (e_v v, stacks, status_running)
  | NONE => NONE)
  /\
 (e_exec ctx (e_acc e (e_var f)) stacks status_running =
  case e_exec ctx e stacks status_running of
  | SOME (e', stacks', status') => SOME (e_acc e' (e_var f), stacks', status')
  | NONE => NONE)
  /\
 (*************************)
 (* Function call-related *)
 (e_exec ((type_map, func_map, pars_map, t_map, ctrl):ctx) (e_func_call f e_l) (stacks_tup curr_stack_frame call_stack) status =
  case FLOOKUP func_map f of
  | SOME (stmt, x_d_l) =>
    (case unred_arg_index (MAP SND x_d_l) e_l of
     | SOME i  =>
      (case e_exec ((type_map, func_map, pars_map, t_map, ctrl):ctx) (EL i e_l) (stacks_tup curr_stack_frame call_stack) status of
       | SOME (e', stacks', status') => SOME (e_func_call f (LUPDATE e' i e_l), stacks', status')
       | NONE => NONE)
     | NONE =>
      SOME (e_func_exec stmt,
	    stacks_tup ([EL 0 curr_stack_frame]++[all_arg_update_for_newscope (MAP FST x_d_l) (MAP SND x_d_l) e_l curr_stack_frame])
		       ((TL curr_stack_frame, called_function_name_function_name f)::call_stack),
	    status))
  | NONE => NONE)
  /\
 (e_exec _ (e_func_exec stmt_empty) stacks (status_return v) =
  SOME (e_v v, stacks, status_running))
  /\
 (e_exec ctx (e_func_exec stmt) stacks status =
  case stmt_exec ctx stmt stacks status of
  | SOME (stmt', stacks', status') => SOME (e_func_exec stmt', stacks', status')
  | NONE => NONE)
  /\
 (********************)
 (* Unary arithmetic *)
 (e_exec _ (e_unop unop (e_v v)) stacks status =
  case unop_exec unop v of
  | SOME v => SOME (e_v v, stacks, status)
  | NONE => NONE)
  /\
 (*****************************************)
 (* Argument reduction of unary operation *)
 (e_exec ctx (e_unop unop e) stacks status =
  case e_exec ctx e stacks status of
  | SOME (e', stacks', status') => SOME ((e_unop unop e'), stacks', status')
  | NONE => NONE)
  /\
(* TEST: Single rule for unary arithmetic
 (e_exec ctx (e_unop unop e) stacks status =
  case e of
  | (e_v v) =>
   (case unop_exec unop v of
    | SOME v' => SOME (e_v v', stacks, status)
    | NONE => NONE)
  (* This will become 10 different cases *)
  | _ =>
   (case e_exec ctx e stacks status of
    | SOME (e', stacks', status') => SOME (e_unop unop e', stacks', status')
    | NONE => NONE))
  /\
*)
 (*********************)
 (* Binary arithmetic *)
 (e_exec _ (e_binop (e_v v1) binop (e_v v2)) stacks status =
  case binop_exec binop v1 v2 of
  | SOME v => SOME (e_v v, stacks, status)
  | NONE => NONE)
  /\
 (******************************************)
 (* Argument reduction of binary operation *)
 (e_exec ctx (e_binop (e_v v) binop e1) stacks status =
  if is_short_circuitable v binop
  then short_circuit binop stacks status
  else
   (case e_exec ctx e1 stacks status of
    | SOME (e2, stacks', status') => SOME (e_binop (e_v v) binop e2, stacks', status')
    | NONE => NONE))
  /\
 (e_exec ctx (e_binop e1 binop e2) stacks status =
  case e_exec ctx e1 stacks status of
  | SOME (e3, stacks', status') => SOME (e_binop e3 binop e2, stacks', status')
  | NONE => NONE)
  /\
 (e_exec _ _ stacks status = NONE)
  /\
 (**************)
 (* Statements *)
 (**************)
 (* empty_stmt is the fully reduced form of statement *)
 (stmt_exec _ stmt_empty stacks status = SOME (stmt_empty, stacks, status)) /\
 (*************************)
 (* Function call-related *)
 (stmt_exec ((type_map, func_map, pars_map, t_map, ctrl):ctx) (stmt_ret (e_v v)) (stacks_tup curr_stack_frame call_stack) status_running =
  case call_stack of
  | ((curr_stack_frame', called_function_name_bot)::call_stack') => NONE
  | ((curr_stack_frame', called_function_name_function_name f)::call_stack') =>
   (case FLOOKUP func_map f of
   | SOME (stmt, x_d_l) => SOME (stmt_empty,
				(stacks_tup (update_return_frame (MAP FST x_d_l) (MAP SND x_d_l) ((HD curr_stack_frame)::curr_stack_frame') curr_stack_frame)
					    call_stack'),
				status_return v)
   | NONE => NONE)
  | [] => NONE)
  /\
 (stmt_exec ctx (stmt_ret e) stacks status =
  case e_exec ctx e stacks status of
  | SOME (e', stacks', status') => SOME (stmt_ret e', stacks', status')
  | NONE => NONE)
  /\
(*
 (stmt_exec ((type_map, func_map, pars_map, t_map, ctrl):ctx) (stmt_ret e) (stacks_tup curr_stack_frame call_stack) status =
  case e of
  | (e_v v) => 
   (case call_stack of
    | ((curr_stack_frame', called_function_name_bot)::call_stack') => NONE
    | ((curr_stack_frame', called_function_name_function_name f)::call_stack') =>
     (case FLOOKUP func_map f of
     | SOME (stmt, x_d_l) => SOME (stmt_empty,
				  (stacks_tup (update_return_frame (MAP FST x_d_l) (MAP SND x_d_l) ((HD curr_stack_frame)::curr_stack_frame') curr_stack_frame)
					      call_stack'),
				  status_return v)
     | NONE => NONE)
    | [] => NONE)
  | e' =>
   (case e_exec ((type_map, func_map, pars_map, t_map, ctrl):ctx) e (stacks_tup curr_stack_frame call_stack) status of
    | SOME (e', stacks', status') => SOME (stmt_ret e', stacks', status')
    | NONE => NONE))
  /\
*)
 (**************)
 (* Assignment *)
 (stmt_exec _ (stmt_ass (lval_varname x) (e_v v)) (stacks_tup curr_stack_frame call_stack) status =
  SOME (stmt_empty, (stacks_tup  (assign curr_stack_frame v x) call_stack), status))
  /\
 (stmt_exec _ (stmt_ass (lval_field lval f) (e_v v)) (stacks_tup curr_stack_frame call_stack) status =
  case lookup_lval curr_stack_frame lval of
  | (v_struct (f_v_list)) =>
   SOME (stmt_ass lval (e_v (v_struct (LUPDATE (f, v) (THE (INDEX_OF f (MAP FST f_v_list))) f_v_list))), stacks_tup curr_stack_frame call_stack, status)
  | _ => NONE
  )
  /\
 (stmt_exec _ (stmt_ass lval_null (e_v v)) stacks status =
  SOME (stmt_empty, stacks, status))
  /\
 (stmt_exec ctx (stmt_ass lval e) stacks status =
  case e_exec ctx e stacks status of
  | SOME (e', stacks', status') => SOME (stmt_ass lval e', stacks', status')
  | NONE => NONE)
  /\
 (************)
 (* Sequence *)
 (stmt_exec _ ((stmt_seq stmt_empty stmt):stmt) stacks (status_return v) =
  SOME (stmt_empty, stacks, status_return v))
  /\
 (stmt_exec _ ((stmt_seq stmt_empty stmt):stmt) stacks status =
  SOME (stmt, stacks, status))
  /\
 (stmt_exec ctx ((stmt_seq stmt1 stmt2):stmt) stacks status =
  case stmt_exec ctx stmt1 stacks status of
  | SOME (stmt1', stacks', status') => SOME (stmt_seq stmt1' stmt2, stacks', status')
  | NONE => NONE)
  /\
 (stmt_exec _ _ stacks status = NONE)
`
(WF_REL_TAC `measure sum_size` >>
 fs [sum_size_def, e_size_def] >>
 REPEAT STRIP_TAC >>
 IMP_RES_TAC unred_arg_index_in_range >>
 IMP_RES_TAC rich_listTheory.EL_MEM >>
 IMP_RES_TAC e1_size_mem >>
 fs [])
;

(* Then, some kind of theorem that states equivalence
 * between executable semantics and ott-exported reduction rules.
 * For sketch, only soundness and not completeness *)
(* TODO: Completeness *)
Theorem e_exec_sound_red:
 !ctx (e:e) (e':e) stacks stacks' status status'.
  e_exec ctx e stacks status = SOME (e', stacks', status) ==>
  e_red ctx e stacks status e' stacks' status'
Proof
(* OLD version:
 Cases_on `e` >> Cases_on `e'` >> (
  fs [e_exec]
 ) >>
 Cases_on `u` >> Cases_on `v` >> (
  fs [e_exec]
 ) >| (map (irule o valOf o find_clause_e_red)
  ["e_neg_bool", "e_compl", "e_neg_signed", "e_un_plus"]
 ) >> (
  fs [clause_name_def]
 )
*)
cheat
QED

Theorem stmt_exec_sound_red:
 !ctx (stmt:stmt) (stmt':stmt) stacks stacks' status status'.
  stmt_exec ctx stmt stacks status = SOME (stmt', stacks', status) ==>
  stmt_red ctx stmt (state_tup stacks status) stmt' (state_tup stacks' status')
Proof
cheat
QED

Definition is_red:
 (is_red (e_v v) = T) /\
 (is_red _ = F)
End

(* Then, define an executable semantics which performs execution until finished. *)
(* Note that all concrete operations remain the same *)
val [e_multi_exec, stmt_multi_exec] = TotalDefn.multiDefine `
 (e_multi_exec _ e stacks status 0 =
  SOME (e, stacks, status))
  /\
 (e_multi_exec ctx e stacks status (SUC gas) =
  case e_exec ctx e stacks status of
  | SOME (e', stacks', status') => e_multi_exec ctx e' stacks' status' gas
  | NONE => NONE)
 /\
 (stmt_multi_exec _ stmt stacks status 0 =
  SOME (stmt, stacks, status))
 /\
 (stmt_multi_exec ctx stmt stacks status (SUC gas) =
  case stmt_exec ctx stmt stacks status of
  | SOME (stmt', stacks', status') => stmt_multi_exec ctx stmt' stacks' status' gas
  | NONE => NONE)
`;

(* TEST

val bl0 = ``(w2v (0w:word32), 32)``;
val bl1 = ``(w2v (1w:word32), 32)``;
val bl2 = ``(w2v (16384w:word32), 32)``;

(* TODO: Add to ctx *)
val func_map = ``FEMPTY |+ ("f_x", (stmt_seq (stmt_ass (lval_varname "x_inout") (e_v (v_bit (^bl1)))) (stmt_ret (e_v v_bot))), ["x_inout", d_inout])``;

val stacks = ``stacks_tup ([FEMPTY |+ ("x", ((v_bit (^bl0)), NONE))]:scope list) ([]:call_stack)``
val status = ``status_running``

(* Nested unary operations *)
val e_un = ``(e_unop unop_compl (e_unop unop_compl (e_v (v_bit (^bl1)))))``;
EVAL ``e_multi_exec (^func_map) (^e_un) (^stacks) (^status) 20``;

(* Single statements *)
EVAL ``stmt_multi_exec (^func_map) (stmt_ass lval_null (^e_un)) (^stacks) (^status) 20``;

(* TODO: Simplifying multiple updates to the same finite map? *)
EVAL ``stmt_multi_exec (^func_map) (stmt_ass (lval_varname "x") (^e_un)) (^stacks) (^status) 20``;

(* Sequence of statements *)
EVAL ``stmt_multi_exec (^func_map) (stmt_seq (stmt_ass (lval_varname "x") (^e_un)) (stmt_ass (lval_varname "x") (e_v (v_bit (^bl2))) )) (^stacks) (^status) 20``;

(* Function call *)
EVAL ``stmt_multi_exec (^func_map) (stmt_ass lval_null (e_func_call "f_x" [e_var "x"])) (^stacks) (^status) 20``;

(* Nested binary operations *)
EVAL ``e_multi_exec (^func_map) (e_binop (e_v (v_bit (^bl1))) binop_add (e_v (v_bit (^bl2)))) (^stacks) (^status) 20``;

(* Stack assignment *)
val stacks' = ``stacks_tup ([FEMPTY |+ ("x", ((v_struct [("f", (v_bit (^bl0)))]), NONE))]:scope list) ([]:call_stack)``;

EVAL ``stmt_multi_exec ctx (stmt_ass (lval_field (lval_varname "x") "f") (e_v (v_bit (^bl1)))) (^stacks') (^status) 20``;

(*************************)
(*   From VSS Example    *)
(*************************)

val ip_v0_ok = ``(w2v (4w:word4), 4)``;
(* TODO: Syntax function to construct struct terms? *)
val stacks = ``stacks_tup ([FEMPTY |+ ("p", (v_struct [("ip", (v_struct [("version", (v_bit (^ip_v0_ok)))]))], NONE))]:scope list) ([]:call_stack)``;
val status = ``status_running``;
val e_ip_v = ``(e_acc (e_acc (e_var "p") (e_var "ip")) (e_var "version"))``;
val e_4w4 = ``e_v (v_bit (w2v (4w:word4), 4))``;
val e_ip_v_eq_4w4 = ``e_binop (^e_ip_v) binop_eq (^e_4w4)``;

(* p.ip.version == 4w4 *)
EVAL ``e_multi_exec ctx (^e_ip_v_eq_4w4) (^stacks) (^status) 20``;

(* verify(p.ip.version == 4w4, error.IPv4IncorrectVersion); *)
EVAL ``stmt_multi_exec ctx (stmt_verify ) (^stacks) (^status) 20``;

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
 !ctx (e:e) (e':e) stacks status stacks' status' gas.
  e_multi_exec ctx  e stacks status gas = SOME (e', stacks', status') ==>
  e_clos_red ctx e stacks status e' stacks' status'
Proof
 cheat
QED

Theorem stmt_multi_exec_sound_red:
 !ctx (stmt:stmt) (stmt':stmt) stacks status stacks' status' gas.
  stmt_multi_exec ctx stmt stacks status gas = SOME (stmt', stacks', status') ==>
  stmt_clos_red ctx stmt (state_tup stacks status) stmt' (state_tup stacks' status')
Proof
 cheat
QED

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

(* TODO: At this point, expect to translate lists to lists and fmaps to mlmaps *)
Theorem sem_expr_exe_cake_equiv:
 !e stacks.
  e_exec_cake e stacks status_running = e_exec_multi e stacks status_running
Proof
 cheat
QED
*)

val _ = export_theory ();
