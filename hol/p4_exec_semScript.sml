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
val bl0 = ``(w2v (0w:word32), 32)``;
val bl1 = ``(w2v (1w:word32), 32)``;
val bl2 = ``(w2v (16384w:word32), 32)``;

val func_map = ``FEMPTY |+ ("f_x", (stmt_seq (stmt_ass (lval_varname "x_inout") (e_v (v_bit (^bl1)))) (stmt_ret (e_v v_bot))), ["x_inout", d_inout])``;

(* First, some kind of executable semantics definition *)
(* No state modification, for now *)
(* TODO: Write explicit NONE-reducing clauses for operands of wrong types?
 *       This would reduce the number of clauses pattern completion needs to add *)
val e_stmt_exec = TotalDefn.multiDefine`
 (* e_v is the fully reduced form of expression *)
 (e_exec (e_v v) (stacks:stacks) (status:status) =
  SOME ((e_v v), stacks, status))
  /\
 (********************)
 (* Variable look-up *)
 (e_exec (e_var x) (stacks_tup curr_stack_frame call_stack) status_running =
  SOME ((e_v (lookup_vexp curr_stack_frame (e_var x))), stacks_tup curr_stack_frame call_stack, status_running))
  /\
 (*************************)
 (* Function call-related *)
(* TODO: Fix func_map in this definition... *)
 (e_exec (e_func_call_red f e_l) (stacks_tup curr_stack_frame call_stack) status_running =
  case FLOOKUP (^func_map) f of
  | SOME (stmt, x_d_l) =>
    SOME (e_func_exec stmt,
	  stacks_tup ([EL 0 curr_stack_frame]++[all_arg_update_for_newscope (MAP FST x_d_l) (MAP SND x_d_l) e_l curr_stack_frame])
		     ((TL curr_stack_frame, called_function_name_function_name f)::call_stack),
	  status_running)
  | NONE => NONE)
  /\
 (e_exec (e_func_exec stmt_empty) stacks (status_return v) =
  SOME (e_v v, stacks, status_running))
  /\
 (e_exec (e_func_exec stmt) stacks (status:status) =
  case stmt_exec stmt stacks status of
  | SOME (stmt', stacks', status') => SOME (e_func_exec stmt', stacks', status')
  | NONE => NONE)
  /\
 (***************************************)
 (* Argument reduction of function call *)
(* TODO: Fix func_map in this definition... *)
 (e_exec (e_func_call f (e_l_hd::e_l_tl) e_l') stacks status =
  case FLOOKUP (^func_map) f of
  | SOME (stmt, x_d_l) =>
   if check_arg_red (MAP SND x_d_l) e_l_hd (LENGTH e_l')
   then SOME (e_func_call f e_l_tl (e_l_hd::e_l'), stacks, status)
   else
     (case e_exec e_l_hd stacks status of
      | SOME (e', stacks', status') => SOME (e_func_call f (e'::e_l_tl) e_l', stacks', status')
      | NONE => NONE)
  | NONE => NONE)
  /\
 (e_exec (e_func_call f [] e_l) stacks status =
  SOME (e_func_call_red f e_l, stacks, status))
  /\
 (********************)
 (* Unary arithmetic *)
 (e_exec (e_unop unop_neg (e_v (v_bool b))) (stacks:stacks) (status:status) =
  SOME ((e_v (v_bool ~b)), stacks, status))
  /\
 (e_exec (e_unop unop_compl (e_v (v_bit bitv))) stacks status =
  SOME ((e_v (v_bit (bitv_bl_unop bnot bitv))), stacks, status))
  /\
 (e_exec (e_unop unop_neg_signed (e_v (v_bit bitv))) stacks status =
  SOME ((e_v (v_bit (bitv_unop unop_neg_signed bitv))), stacks, status))
  /\
 (e_exec (e_unop unop_un_plus (e_v (v_bit bitv))) stacks status =
  SOME ((e_v (v_bit bitv)), stacks, status))
  /\
 (*****************************************)
 (* Argument reduction of unary operation *)
 (e_exec (e_unop unop e) (stacks:stacks) (status:status) =
  case e_exec e stacks status of
  | SOME (e', stacks', status') => SOME ((e_unop unop e'), stacks', status')
  | NONE => NONE)
  /\
 (*********************)
 (* Binary arithmetic *)
(*
 (e_exec (e_binop (e_v (v_bit bitv1)) binop_mul (e_v (v_bit bitv2))) (stacks:stacks) (status:status) =
  case bitv_binop binop_mul bitv1 bitv2 of
  | SOME bitv3 => SOME (e_v (v_bit bitv3))
  | NONE => NONE)
  /\
 (e_exec (e_binop (e_v (v_bit bitv1)) binop_div (e_v (v_bit bitv2))) (stacks:stacks) (status:status) =
  case bitv_binop binop_div bitv1 bitv2 of
  | SOME bitv3 => SOME (e_v (v_bit bitv3))
  | NONE => NONE)
  /\
 (e_exec (e_binop (e_v (v_bit bitv1)) binop_mod (e_v (v_bit bitv2))) (stacks:stacks) (status:status) =
  case bitv_binop binop_mod bitv1 bitv2 of
  | SOME bitv3 => SOME (e_v (v_bit bitv3))
  | NONE => NONE)
  /\
 (e_exec (e_binop (e_v (v_bit bitv1)) binop_add (e_v (v_bit bitv2))) (stacks:stacks) (status:status) =
  case bitv_binop binop_add bitv1 bitv2 of
  | SOME bitv3 => SOME (e_v (v_bit bitv3))
  | NONE => NONE)
  /\
 (e_exec (e_binop (e_v (v_bit bitv1)) binop_sub (e_v (v_bit bitv2))) (stacks:stacks) (status:status) =
  case bitv_binop binop_sub bitv1 bitv2 of
  | SOME bitv3 => SOME (e_v (v_bit bitv3))
  | NONE => NONE)
  /\
 (e_exec (e_binop (e_v (v_bit bitv1)) binop_shl (e_v (v_bit bitv2))) (stacks:stacks) (status:status) =
  SOME (e_v (v_bit (bitv_bl_binop shiftl bitv1 ((\(bl, n). (v2n bl, n)) bitv2)) )))
  /\
 (e_exec (e_binop (e_v (v_bit bitv1)) binop_shr (e_v (v_bit bitv2))) (stacks:stacks) (status:status) =
  SOME (e_v (v_bit (bitv_bl_binop shiftr bitv1 ((\(bl, n). (v2n bl, n)) bitv2)) )))
  /\
 (e_exec (e_binop (e_v (v_bit bitv1)) binop_le (e_v (v_bit bitv2))) (stacks:stacks) (status:status) =
  case bitv_binpred binop_le bitv1 bitv2 of
  | SOME b => SOME (e_v (v_bool b))
  | NONE => NONE)
  /\
 (e_exec (e_binop (e_v (v_bit bitv1)) binop_ge (e_v (v_bit bitv2))) (stacks:stacks) (status:status) =
  case bitv_binpred binop_ge bitv1 bitv2 of
  | SOME b => SOME (e_v (v_bool b))
  | NONE => NONE)
  /\
 (e_exec (e_binop (e_v (v_bit bitv1)) binop_lt (e_v (v_bit bitv2))) (stacks:stacks) (status:status) =
  case bitv_binpred binop_lt bitv1 bitv2 of
  | SOME b => SOME (e_v (v_bool b))
  | NONE => NONE)
  /\
 (e_exec (e_binop (e_v (v_bit bitv1)) binop_gt (e_v (v_bit bitv2))) (stacks:stacks) (status:status) =
  case bitv_binpred binop_gt bitv1 bitv2 of
  | SOME b => SOME (e_v (v_bool b))
  | NONE => NONE)
  /\
 (e_exec (e_binop (e_v (v_bit bitv1)) binop_neq (e_v (v_bit bitv2))) (stacks:stacks) (status:status) = SOME (e_v (v_bool (bitv1 <> bitv2))))
  /\
 (e_exec (e_binop (e_v (v_bit bitv1)) binop_eq (e_v (v_bit bitv2))) (stacks:stacks) (status:status) = SOME (e_v (v_bool (bitv1 = bitv2))))
  /\
 (e_exec (e_binop (e_v (v_bit bitv1)) binop_and (e_v (v_bit bitv2))) (stacks:stacks) (status:status) = SOME (e_v (v_bit (bitv_bl_binop band bitv1 bitv2))))
  /\
 (e_exec (e_binop (e_v (v_bit bitv1)) binop_xor (e_v (v_bit bitv2))) (stacks:stacks) (status:status) = SOME (e_v (v_bit (bitv_bl_binop bxor bitv1 bitv2))))
  /\
 (e_exec (e_binop (e_v (v_bit bitv1)) binop_or (e_v (v_bit bitv2))) (stacks:stacks) (status:status) = SOME (e_v (v_bit (bitv_bl_binop bor bitv1 bitv2))))
  /\
 (e_exec (e_binop (e_v (v_bool F)) binop_bin_and (e_v (v_bool b))) (stacks:stacks) (status:status) = SOME (e_v (v_bool F)))
  /\
 (e_exec (e_binop (e_v (v_bool T)) binop_bin_and (e_v (v_bool b))) (stacks:stacks) (status:status) = SOME (e_v (v_bool b)))
  /\
 (e_exec (e_binop (e_v (v_bool T)) binop_bin_or (e_v (v_bool b))) (stacks:stacks) (status:status) = SOME (e_v (v_bool T)))
  /\
 (e_exec (e_binop (e_v (v_bool F)) binop_bin_or (e_v (v_bool b))) (stacks:stacks) (status:status) = SOME (e_v (v_bool b)))
  /\
 (******************************************)
 (* Argument reduction of binary operation *)
 (e_exec (e_binop (e_v v) binop e1) (stacks:stacks) (status:status) =
  case e_exec e1 stacks status of
  | SOME e2 => SOME (e_binop (e_v v) binop e2)
  | NONE => NONE)
  /\
 (e_exec (e_binop e1 binop e2) (stacks:stacks) (status:status) =
  case e_exec e1 stacks status of
  | SOME e3 => SOME (e_binop e3 binop e2)
  | NONE => NONE)
  /\
*)
 (e_exec _ stacks status = NONE)
  /\
 (**************)
 (* Statements *)
 (**************)
 (* empty_stmt is the fully reduced form of statement *)
 (stmt_exec stmt_empty stacks status = SOME (stmt_empty, stacks, status)) /\
 (*************************)
 (* Function call-related *)
(* TODO: Fix func_map in this definition... *)
 (stmt_exec (stmt_ret (e_v v)) (stacks_tup curr_stack_frame call_stack) status_running =
  case call_stack of
  | ((curr_stack_frame', called_function_name_function_name f)::call_stack') =>
   (case FLOOKUP (^func_map) f of
   | SOME (stmt, x_d_l) => SOME (stmt_empty,
				(stacks_tup (update_return_frame (MAP FST x_d_l) (MAP SND x_d_l) ((HD curr_stack_frame)::curr_stack_frame') curr_stack_frame)
					    call_stack'),
				status_return v)
   | NONE => NONE)
  | [] => NONE)
  /\
 (stmt_exec (stmt_ret e) stacks (status:status) =
  case e_exec e stacks status of
  | SOME (e', stacks', status') => SOME (stmt_ret e', stacks', status')
  | NONE => NONE)
  /\
 (**************)
 (* Assignment *)
 (stmt_exec ((stmt_ass (lval_varname x) (e_v v)):stmt) (stacks_tup curr_stack_frame call_stack) (status:status) =
  SOME (stmt_empty, (stacks_tup  (assign curr_stack_frame v x) call_stack), status))
  /\
 (stmt_exec ((stmt_ass lval_null (e_v v)):stmt) stacks (status:status) =
  SOME (stmt_empty, stacks, status))
  /\
 (stmt_exec ((stmt_ass lval e):stmt) stacks (status:status) =
  case e_exec e stacks status of
  | SOME (e', stacks', status') => SOME (stmt_ass lval e', stacks', status')
  | NONE => NONE)
  /\
 (************)
 (* Sequence *)
 (stmt_exec ((stmt_seq stmt_empty stmt):stmt) stacks (status_return v) =
  SOME (stmt_empty, stacks, status_return v))
  /\
 (stmt_exec ((stmt_seq stmt_empty stmt):stmt) stacks (status:status) =
  SOME (stmt, stacks, status))
  /\
 (stmt_exec ((stmt_seq stmt1 stmt2):stmt) stacks (status:status) =
  case stmt_exec stmt1 stacks status of
  | SOME (stmt1', stacks', status') => SOME (stmt_seq stmt1' stmt2, stacks', status')
  | NONE => NONE)
  /\
 (stmt_exec (_:stmt) (stacks:stacks) (status:status) = NONE)
`;

(* Then, some kind of theorem that states equivalence
 * between executable semantics and ott-exported reduction rules.
 * For sketch, only soundness and not completeness *)
(* TODO: Completeness *)
Theorem e_exec_sound_red:
 !(e:e) (e':e) stacks stacks' status status'.
  e_exec e stacks status = SOME (e', stacks', status) ==>
  e_red e stacks status e' stacks' status'
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
 !(stmt:stmt) (stmt':stmt) stacks stacks' status status'.
  stmt_exec stmt stacks status = SOME (stmt', stacks', status) ==>
  stmt_red stmt (state_tup stacks status) stmt' (state_tup stacks' status')
Proof
cheat
QED

Definition is_red:
 (is_red (e_v v) = T) /\
 (is_red _ = F)
End

(* TODO: Instead of matching, put logic allowing only certain types of e_v in
 *       helper functions? *)
(* Then, define an executable semantics which performs execution until finished. *)
(* Note that all concrete operations remain essentially the same *)
val [e_multi_exec, stmt_multi_exec] = TotalDefn.multiDefine `
 (* Case out of gas *)
 (e_multi_exec (e:e) (stacks:stacks) (status:status) 0 =
  SOME (e, stacks, status))
  /\
 (* e_v is the fully reduced form of expression *)
 (e_multi_exec (e_v v) stacks status (SUC gas) =
  e_exec (e_v v) stacks status)
  /\
 (e_multi_exec (e_var x) stacks status (SUC gas) =
  e_exec (e_var x) stacks status)
  /\
 (e_multi_exec (e_func_call_red f e_l) stacks status (SUC gas) =
  case e_exec (e_func_call_red f e_l) stacks status of
  | SOME (e', stacks', status') => e_multi_exec e' stacks' status' gas
  | NONE => NONE)
  /\
 (* Base case for function execution *)
 (e_multi_exec (e_func_exec stmt_empty) stacks status (SUC gas) =
  e_exec (e_func_exec stmt_empty) stacks status)
  /\
 (e_multi_exec (e_func_exec stmt) stacks status (SUC gas) =
  case stmt_exec stmt stacks status of
  | SOME (stmt', stacks', status') => e_multi_exec (e_func_exec stmt') stacks' status' gas
  | NONE => NONE)
  /\
 (*******************************)
 (* Function argument reduction *)
 (e_multi_exec (e_func_call f [] e_l') stacks status (SUC gas) =
  e_multi_exec (e_func_call_red f e_l') stacks status gas)
  /\
 (e_multi_exec (e_func_call f e_l e_l') stacks status (SUC gas) =
  case e_exec (e_func_call f e_l e_l') stacks status of
   | SOME (efc', stacks', status') => e_multi_exec efc' stacks' status' gas
   | NONE => NONE)
  /\
 (********************)
 (* Unary arithmetic *)
 (e_multi_exec (e_unop unop (e_v v)) stacks status (SUC gas) =
  e_exec (e_unop unop (e_v v)) stacks status)
  /\
 (*********************)
 (* Binary arithmetic *)
 (e_multi_exec (e_binop (e_v v1) binop (e_v v2)) stacks status (SUC gas) =
  e_exec (e_binop (e_v v1) binop (e_v v2)) stacks status)
  /\
 (***************************)
 (* Unary operand reduction *)
 (e_multi_exec (e_unop unop e) (stacks:stacks) (status:status) (SUC gas) =
  case e_multi_exec e stacks status gas of
  | SOME (ev, stacks', status') => e_exec (e_unop unop ev) stacks' status'
  | NONE => NONE)
  /\
 (****************************)
 (* Binary operand reduction *)
(* Two clauses:
 (e_multi_exec (e_binop (e_v v1) binop e2) (stacks:stacks) (status:status) =
  case e_multi_exec e2 stacks status of
  | SOME (e_v v2) => e_exec (e_binop (e_v v1) binop (e_v v2)) stacks status
  | SOME _ => NONE
  | NONE => NONE)
  /\
 (e_multi_exec (e_binop e1 binop e2) (stacks:stacks) (status:status) =
  case e_multi_exec e1 stacks status of
  | SOME (e_v v1) => e_multi_exec (e_binop (e_v v1) binop e2) stacks status
  | SOME _ => NONE
  | NONE => NONE)
  /\
*)
(* One clause, with matching:
 (e_multi_exec (e_binop e1 binop e2) (stacks:stacks) (status:status) =
  case e_multi_exec e1 stacks status of
  | SOME (e_v v1) =>
   (case e_multi_exec e2 stacks status of
   | SOME (e_v v2) => e_exec (e_binop (e_v v1) binop (e_v v2)) stacks status
   | SOME _ => NONE
   | NONE => NONE)
  | SOME _ => NONE
  | NONE => NONE)
  /\
*)
(* One clause, with conditions: *)
 (e_multi_exec (e_binop e1 binop e2) (stacks:stacks) (status:status) (SUC gas) =
  case e_multi_exec e1 stacks status gas of
  | SOME (ev1, stacks', status') =>
   if is_red ev1
   then
    (case e_multi_exec e2 stacks' status' gas of
     | SOME (ev2, stacks'', status'') =>
      if is_red ev2
      then e_exec (e_binop ev1 binop ev2) stacks'' status''
      else NONE
     | NONE => NONE)
   else NONE
  | NONE => NONE)
  /\
 (* TODO: Ideally, the default case here should be "e_exec e stacks status",
  *       with all the recursive clauses needed defined above. *)
 (e_multi_exec _ _ _ _ = NONE) /\
 (**************)
 (* Statements *)
 (**************)
 (* Case out of gas *)
 (stmt_multi_exec stmt stacks status 0 =
  SOME (stmt, stacks, status)) /\
 (* stmt_empty is the fully reduced form of statement *)
 (stmt_multi_exec stmt_empty (stacks:stacks) (status:status) gas =
  stmt_exec stmt_empty stacks status) /\
 (**********)
 (* Return *)
 (stmt_multi_exec (stmt_ret e) stacks status (SUC gas) =
  case e_multi_exec e stacks status gas of
  | SOME (ev, stacks', status') => stmt_exec (stmt_ret ev) stacks' status'
  | NONE => NONE)
  /\
 (**************)
 (* Assignment *)
 (stmt_multi_exec ((stmt_ass lval e):stmt) stacks (status:status) (SUC gas) =
  case e_multi_exec e stacks status gas of
  | SOME (ev, stacks', status') => stmt_exec (stmt_ass lval ev) stacks' status'
  | NONE => NONE)
  /\
 (************)
 (* Sequence *)
 (stmt_multi_exec (stmt_seq stmt1 stmt2) stacks status (SUC gas) =
  case stmt_multi_exec stmt1 stacks status gas of
  | SOME (empty_stmt, stacks', status') => stmt_multi_exec stmt2 stacks' status' gas
  | NONE => NONE)
  /\
 (stmt_multi_exec _ _ _ _ = NONE)
`;

(* TEST

val stacks = ``stacks_tup ([FEMPTY |+ ("x", ((v_bit (^bl0)), NONE))]:scope list) ([]:call_stack)``
val status = ``status_running``

(* Nested unary operations *)
val e_un = ``(e_unop unop_compl (e_unop unop_compl (e_v (v_bit (^bl1)))))``;
EVAL ``e_multi_exec (^e_un) (^stacks) (^status) 20``;

(* Single statements *)
EVAL ``stmt_multi_exec (stmt_ass lval_null (^e_un)) (^stacks) (^status) 20``;

(* TODO: Simplifying multiple updates to the same finite map? *)
EVAL ``stmt_multi_exec (stmt_ass (lval_varname "x") (^e_un)) (^stacks) (^status) 20``;

(* Sequence of statements *)
EVAL ``stmt_multi_exec (stmt_seq (stmt_ass (lval_varname "x") (^e_un)) (stmt_ass (lval_varname "x") (e_v (v_bit (^bl2))) )) (^stacks) (^status) 20``;

(* Function call *)
(* TODO: Debug "assign" *)
EVAL ``stmt_multi_exec (stmt_ass lval_null (e_func_call "f_x" [e_var "x"] [])) (^stacks) (^status) 20``;

(* Nested binary operations *)
EVAL ``e_multi_exec (e_binop (e_v (v_bit (^bl1))) binop_add (e_v (v_bit (^bl2)))) (^stacks) (^status) 20``
   
*)
        
(* Then, define the closure of the small step reduction. *)

val (e_clos_sem_rules, e_clos_sem_ind, e_clos_sem_cases) = Hol_reln`
(* Base clause: *)
(! (e:e) (stacks:stacks) (e':e) (stacks':stacks).
( ( e_red e stacks status_running e' stacks' status_running )) ==> 
( ( e_clos_red e stacks status_running e' stacks' status_running )))
(* Inductive clause: *)
/\ (! (e:e) (stacks:stacks) (e':e) (stacks':stacks) (e'':e) (stacks'':stacks).
(( ( e_red e stacks status_running e' stacks' status_running )) /\ 
( ( e_clos_red e' stacks' status_running e'' stacks'' status_running ))) ==> 
( ( e_clos_red e stacks status_running e'' stacks'' status_running )))
`;

val (stmt_clos_sem_rules, stmt_clos_sem_ind, stmt_clos_sem_cases) = Hol_reln`
(* Base clause: *)
(! (stmt:stmt) (state:state) (stmt':stmt) (state':state).
( ( stmt_red stmt state stmt' state' )) ==> 
( ( stmt_clos_red stmt state stmt' state' )))
(* Inductive clause: *)
/\ (! (stmt:stmt) (state:state) (stmt':stmt) (state':state) (stmt'':stmt) (state'':state).
(( ( stmt_red stmt state stmt' state' )) /\ 
( ( stmt_clos_red stmt' state' stmt'' state'' ))) ==> 
( ( stmt_clos_red stmt state stmt'' state'' )))
`;

(* Then, prove that the multi-step executable semantics is sound with respect to the
 * closure of the small-step reduction *)

Theorem e_multi_exec_sound_red:
 !(e:e) (e':e) stacks status stacks' status' gas.
  e_multi_exec e stacks status gas = SOME (e', stacks', status') ==>
  e_clos_red e stacks status e' stacks' status'
Proof
 cheat
QED

Theorem stmt_multi_exec_sound_red:
 !(stmt:stmt) (stmt':stmt) stacks status stacks' status' gas.
  stmt_multi_exec stmt stacks status gas = SOME (stmt', stacks', status') ==>
  stmt_clos_red stmt (state_tup stacks status) stmt' (state_tup stacks' status')
Proof
 cheat
QED

(* Then, some kind of (multi-step) CakeML-adjusted executable semantics definition *)
(* TODO:
Definition e_exec_cake:
 (e_exec_cake (e_unop unop_neg (e_v (v_bool b))) (stacks:stacks) (status:status) =
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
