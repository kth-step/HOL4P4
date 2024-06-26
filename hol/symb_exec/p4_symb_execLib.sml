structure p4_symb_execLib :> p4_symb_execLib = struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

open pairSyntax listSyntax numSyntax computeLib hurdUtils;

open p4Theory p4_exec_semTheory p4Syntax p4_exec_semSyntax;
open p4_coreTheory;
open symb_execTheory symb_execSyntax p4_symb_execTheory;

open evalwrapLib p4_testLib;
open symb_execLib;

open optionSyntax;

val ERR = mk_HOL_ERR "p4_symb_exec"

fun dbg_print debug_flag string =
 if debug_flag
 then print string
 else ()
;

fun get_b_func_map i ab_list pblock_map =
 let
  val arch_block = el ((int_of_term i) + 1) (fst $ dest_list ab_list)
 in
  if is_arch_block_pbl arch_block
  then
   let
    val arch_block_name = fst $ dest_arch_block_pbl arch_block
   in
    case List.find (fn (name, data) => term_eq name arch_block_name) ((map dest_pair) $ fst $ dest_list pblock_map) of
      SOME (_, pblock) =>
     SOME $ #3 $ dest_pblock pblock
    | NONE => NONE
   end
  else NONE
 end
;

(* TODO: Rename to stmt_get_substmt? *)
fun stmt_get_next stmt =
 if is_stmt_empty stmt
 then stmt
 else if is_stmt_ass stmt
 then stmt
 else if is_stmt_cond stmt
 then stmt
 else if is_stmt_block stmt
 then stmt_get_next $ snd $ dest_stmt_block stmt
 else if is_stmt_ret stmt
 then stmt
 else if is_stmt_seq stmt
 then stmt_get_next $ fst $ dest_stmt_seq stmt
 else if is_stmt_trans stmt
 then stmt
 else if is_stmt_app stmt
 then stmt
 else if is_stmt_ext stmt
 then stmt
 else raise (ERR "stmt_get_next" ("Unsupported statement: "^(term_to_string stmt)))
;

fun astate_get_top_stmt astate =
 let
  val (_, _, arch_frame_list, _) = dest_astate astate
 in
  if is_arch_frame_list_empty arch_frame_list
  then NONE
  else SOME $ el 1 $ fst $ dest_list $ #2 $ dest_frame $ el 1 $ fst $ dest_list $ dest_arch_frame_list_regular arch_frame_list
 end
;

datatype branch_data =
   no_branch
 | conditional of term
 | select of term * (term list) * term
 | apply of term * term;

(* Returns the information needed to perform a branch *)
fun astate_get_branch_data astate =
 case astate_get_top_stmt astate of
   SOME stmt =>
  let
   val stmt' = stmt_get_next stmt
  in
   if is_stmt_cond stmt'
   then conditional $ #1 $ dest_stmt_cond stmt'
   else if is_stmt_trans stmt'
   then
    let
     val e = dest_stmt_trans stmt'
    in
     if is_e_select e
     then select $ (fn (a,b,c) => (a,fst $ dest_list b,c)) $ dest_e_select e
     else no_branch
    end 
   else if is_stmt_app stmt' 
   (* TODO: Should also work for lists of expressions of length more than 1 *)
   then apply $ dest_stmt_app stmt'
   else no_branch
  end
 | NONE => no_branch
;

(* TODO: OPTIMIZE: This should be done once in pre-processing, not at every step *)
fun get_f_maps (astate, actx) =
 let
  val (ab_list, pblock_map, _, _, _, _, _, _, ext_fun_map, func_map) = dest_actx actx
  val (aenv, _, _, _) = dest_astate astate
  val (i, _, _, _) = dest_aenv aenv
  val b_func_map_opt = get_b_func_map i ab_list pblock_map
 in
  case get_b_func_map i ab_list pblock_map of
    SOME b_func_map => (func_map, b_func_map, ext_fun_map)
  (* TODO: Get rid of term parsing *)
  | NONE => (func_map, “[]:b_func_map”, ext_fun_map)
 end
;

(* TODO: Get rid of EVAL-ing HOL4 definition for computation? *)
fun get_funn_dirs funn (func_map, b_func_map, ext_fun_map) =
 let
  val funn_sig_opt = rhs $ concl $ EVAL $ mk_lookup_funn_sig (funn, func_map, b_func_map, ext_fun_map)
 in
  if is_some funn_sig_opt
  then
   (map (snd o dest_pair)) $ fst $ dest_list $ dest_some funn_sig_opt
  else raise (ERR "get_funn_dirs" ("Signature of funn not found in function maps: "^(term_to_string funn)))
 end
;

(* TODO: Get rid of EVAL re-use of HOL4 definition? *)
fun is_arg_red (arg, dir) =
 if (is_d_out dir orelse is_d_inout dir)
 then term_eq T (rhs $ concl $ EVAL $ mk_is_e_lval arg) (* Must be lval *)
 else is_e_v arg (* Must be constant *)
;


fun e_get_next_subexp_syntax_f (func_map, b_func_map, ext_fun_map) e =
 if is_e_v e
 then NONE
 else if is_e_var e
 then SOME (fn e => e)
 else if is_e_list e
 then
  let
   val e_list = dest_e_list e
  in
   (case e_get_next_subexp_syntax_f_list (func_map, b_func_map, ext_fun_map) (fst $ dest_list e_list) 0 of
      SOME (f, i) => SOME (f o el (i+1) o fst o dest_list o dest_e_list)
    | NONE => NONE)
  end
 else if is_e_acc e
 then
  let
   val (e', x) = dest_e_acc e
  in
   if is_e_v e'
   then SOME (fn e => e)
   else
    (case e_get_next_subexp_syntax_f (func_map, b_func_map, ext_fun_map) e' of
       SOME f => SOME (f o fst o dest_e_acc)
     | NONE => NONE)
  end
 else if is_e_unop e
 then
  let
   val (unop, e') = dest_e_unop e
  in
   if is_e_v e'
   then SOME (fn e => e)
   else
    (case e_get_next_subexp_syntax_f (func_map, b_func_map, ext_fun_map) e' of
       SOME f => SOME (f o snd o dest_e_unop)
     | NONE => NONE)
  end
 else if is_e_cast e
 then
  let
   val (cast, e') = dest_e_cast e
  in
   if is_e_v e'
   then SOME (fn e => e)
   else
    (case e_get_next_subexp_syntax_f (func_map, b_func_map, ext_fun_map) e' of
       SOME f => SOME (f o snd o dest_e_cast)
     | NONE => NONE)
  end
 else if is_e_binop e
 then
  let
   val (e', binop, e'') = dest_e_binop e
  in
   if is_e_v e'
   then
    if is_e_v e''
    then SOME (fn e => e)
    else
     (case e_get_next_subexp_syntax_f (func_map, b_func_map, ext_fun_map) e'' of
        SOME f => SOME (f o #3 o dest_e_binop)
      | NONE => NONE)
   else
    (case e_get_next_subexp_syntax_f (func_map, b_func_map, ext_fun_map) e' of
       SOME f => SOME (f o #1 o dest_e_binop)
     | NONE => NONE)
  end
 else if is_e_concat e
 then
  let
   val (e', e'') = dest_e_concat e
  in
   if is_e_v e'
   then
    if is_e_v e''
    then SOME (fn e => e)
    else
     (case e_get_next_subexp_syntax_f (func_map, b_func_map, ext_fun_map) e'' of
        SOME f => SOME (f o snd o dest_e_concat)
      | NONE => NONE)
   else
    (case e_get_next_subexp_syntax_f (func_map, b_func_map, ext_fun_map) e' of
       SOME f => SOME (f o fst o dest_e_concat)
     | NONE => NONE)
  end
 else if is_e_slice e
 then
  let
   val (e', e'', e''') = dest_e_slice e
  in
   if is_e_v e'
   then
    if is_e_v e''
    then
     if is_e_v e'''
     then SOME (fn e => e)
     else
      (case e_get_next_subexp_syntax_f (func_map, b_func_map, ext_fun_map) e''' of
         SOME f => SOME (f o #3 o dest_e_slice)
       | NONE => NONE)
    else
     (case e_get_next_subexp_syntax_f (func_map, b_func_map, ext_fun_map) e'' of
        SOME f => SOME (f o #2 o dest_e_slice)
      | NONE => NONE)
   else
    (case e_get_next_subexp_syntax_f (func_map, b_func_map, ext_fun_map) e' of
       SOME f => SOME (f o #1 o dest_e_slice)
     | NONE => NONE)
  end
 else if is_e_call e
 then
  let
   val (funn, e_list) = dest_e_call e
   val d_list = get_funn_dirs funn (func_map, b_func_map, ext_fun_map)
  in
   (case e_get_next_subexp_syntax_f_args (func_map, b_func_map, ext_fun_map) (zip (fst $ dest_list e_list) d_list) 0 of
      SOME (f, i) => SOME (f o el (i+1) o fst o dest_list o snd o dest_e_call)
    | NONE => SOME (fn e => e))
  end
 else if is_e_select e
 then
  let
   val (e', v_x_list, x) = dest_e_select e
  in
   if is_e_v e'
   then SOME (fn e => e)
   else
    (case e_get_next_subexp_syntax_f (func_map, b_func_map, ext_fun_map) e' of
       SOME f => SOME (f o #1 o dest_e_select)
     | NONE => NONE)
  end
 else if is_e_struct e
 then
  let
   val x_e_list = dest_e_struct e
  in
   (case e_get_next_subexp_syntax_f_list (func_map, b_func_map, ext_fun_map) ((map (snd o dest_pair)) $ fst $ dest_list x_e_list) 0 of
      SOME (f, i) => SOME (f o el (i+1) o (map (snd o dest_pair)) o fst o dest_list o dest_e_struct)
    | NONE => NONE)
  end
 else if is_e_header e
 then
  let
   val (boolv, x_e_list) = dest_e_header e
  in
   (case e_get_next_subexp_syntax_f_list (func_map, b_func_map, ext_fun_map) ((map (snd o dest_pair)) $ fst $ dest_list x_e_list) 0 of
      SOME (f, i) => SOME (f o el (i+1) o (map (snd o dest_pair)) o fst o dest_list o snd o dest_e_header)
    | NONE => NONE)
  end
 else raise (ERR "e_get_next_subexp_syntax_f" ("Unsupported expression: "^(term_to_string e)))

and e_get_next_subexp_syntax_f_list (func_map, b_func_map, ext_fun_map) []     _ = NONE
  | e_get_next_subexp_syntax_f_list (func_map, b_func_map, ext_fun_map) (h::t) i =
   (case e_get_next_subexp_syntax_f (func_map, b_func_map, ext_fun_map) h of
      SOME f => SOME (f, i)
    | NONE => e_get_next_subexp_syntax_f_list (func_map, b_func_map, ext_fun_map) t (i+1))
and e_get_next_subexp_syntax_f_args (func_map, b_func_map, ext_fun_map) []     _ = NONE
  | e_get_next_subexp_syntax_f_args (func_map, b_func_map, ext_fun_map) ((arg, dir)::t) i =
   if is_arg_red (arg, dir)
   then e_get_next_subexp_syntax_f_args (func_map, b_func_map, ext_fun_map) t (i+1)
   else
    (case e_get_next_subexp_syntax_f (func_map, b_func_map, ext_fun_map) arg of
       SOME f => SOME (f, i)
     | NONE => e_get_next_subexp_syntax_f_args (func_map, b_func_map, ext_fun_map) t (i+1))
;

fun get_next_subexp (func_map, b_func_map, ext_fun_map) e =
 case e_get_next_subexp_syntax_f (func_map, b_func_map, ext_fun_map) e of
   SOME f => SOME (f e)
 | NONE => NONE
;

(* Can use the SML function "free_vars" to check if expression to be
 * reduced contains any free variables. We should probably only perform
 * a branch if the next smallest subexpression to be reduced includes
 * a free variable. But even this subexpression reduction should be OK for
 * certain expressions: for example, bit slicing and casting if all
 * free variables involved are Booleans. *)
(* TODO: Check for exceptions *)
fun next_subexp_has_free_vars (func_map, b_func_map, ext_fun_map) e =
 case e_get_next_subexp_syntax_f (func_map, b_func_map, ext_fun_map) e of
   SOME f => not $ null $ free_vars $ f e
 | NONE => false
;

(* (debugging from astate_get_next_e_syntax_f)
val stmt = (el 1 stmt_stack')
*)
fun stmt_get_next_e_syntax_f (func_map, b_func_map, ext_fun_map) stmt =
 if is_stmt_empty stmt
 then NONE
 else if is_stmt_ass stmt
 then 
  let
   val (lval, e) = dest_stmt_ass stmt
  in
   if is_e_v e
   then NONE
   else SOME (snd o dest_stmt_ass)
  end
 else if is_stmt_cond stmt
 then
  let
   val (e, stmt', stmt'') = dest_stmt_cond stmt
  in
   if is_e_v e
   then NONE
   else SOME (#1 o dest_stmt_cond)
  end
 else if is_stmt_block stmt
 then NONE
(*
  let
   val (t_scope, stmt') = dest_stmt_block stmt
  in
   (case stmt_get_next_e_syntax_f (func_map, b_func_map, ext_fun_map) stmt' of
      SOME f => SOME (f o snd o dest_stmt_block)
    | NONE => NONE)
  end
*)
 else if is_stmt_ret stmt
 then 
  let
   val e = dest_stmt_ret stmt
  in
   if is_e_v e
   then NONE
   else SOME dest_stmt_ret
  end
 else if is_stmt_seq stmt
 then
  let
   val (stmt', stmt'') = dest_stmt_seq stmt
  in
   (case stmt_get_next_e_syntax_f (func_map, b_func_map, ext_fun_map) stmt' of
      SOME f => SOME (f o fst o dest_stmt_seq)
    | NONE => NONE)
  end
 else if is_stmt_trans stmt
 then 
  let
   val e = dest_stmt_trans stmt
  in
   if is_e_v e
   then NONE
   else SOME dest_stmt_trans
  end
 else if is_stmt_app stmt
 then
  let
   val (x, e_list) = dest_stmt_app stmt
  in
   (* TODO: A little overkill. Make a stmt_get_next_e_syntax_f_list instead *)
   (case e_get_next_subexp_syntax_f_list (func_map, b_func_map, ext_fun_map) (fst $ dest_list e_list) 0 of
      SOME (f, i) => SOME (el (i+1) o fst o dest_list o snd o dest_stmt_app)
    | NONE => NONE)
  end
 else if is_stmt_ext stmt
 then NONE
 else raise (ERR "stmt_get_next_e_syntax_f" ("Unsupported statement: "^(term_to_string stmt)))
;


fun get_next_e (func_map, b_func_map, ext_fun_map) stmt =
 case stmt_get_next_e_syntax_f (func_map, b_func_map, ext_fun_map) stmt of
   SOME f => SOME (f stmt)
 | NONE => NONE
;

fun get_first_frame_components frame_list =
 (* To avoid warnings *)
  case strip_pair (el 1 frame_list) of
    [funn, stmt_stack, scope_list] => (funn, stmt_stack, scope_list)
  | _ => raise (ERR "astate_get_next_e_syntax_f" ("Unknown frame format: "^(term_to_string (el 1 frame_list))))
;

fun astate_get_next_e_syntax_f (func_map, b_func_map, ext_fun_map) astate =
 let
  val (aenv, g_scope_list, arch_frame_list, status) = dest_astate astate
 in
  if is_arch_frame_list_empty arch_frame_list
  then NONE
  else
   let
    val frame_list = fst $ dest_list $ dest_arch_frame_list_regular arch_frame_list
   in
    if null frame_list
    then NONE
    else
     let
      val (funn, stmt_stack, scope_list) = get_first_frame_components frame_list
      val stmt_stack' = fst $ dest_list stmt_stack
     in
      if null stmt_stack'
      then NONE
      else
      (case stmt_get_next_e_syntax_f (func_map, b_func_map, ext_fun_map) (el 1 stmt_stack') of
(*
val SOME next_e_syntax_f = stmt_get_next_e_syntax_f (func_map, b_func_map, ext_fun_map) (el 1 stmt_stack')
*)
         SOME next_e_syntax_f =>
        SOME (next_e_syntax_f o (el 1) o fst o dest_list o (el 2) o strip_pair o (el 1) o fst o dest_list o dest_arch_frame_list_regular o #3 o dest_astate)
       | NONE => NONE)
     end
   end
 end
;


fun astate_get_next_e (func_map, b_func_map, ext_fun_map) astate =
 let
  val (aenv, g_scope_list, arch_frame_list, status) = dest_astate astate
 in
  if is_arch_frame_list_empty arch_frame_list
  then NONE
  else
   let
    val frame_list = fst $ dest_list $ dest_arch_frame_list_regular arch_frame_list
   in
    if null frame_list
    then NONE
    else
     let
      val (funn, stmt_stack, scope_list) = get_first_frame_components frame_list
      val stmt_stack' = fst $ dest_list stmt_stack
     in
      if null stmt_stack'
      then NONE
      else get_next_e (func_map, b_func_map, ext_fun_map) (el 1 stmt_stack')
     end
   end
 end
;


(* Symbolic executor should do similar things as eval_under_assum, but on every iteration
 * check if conditional is next to be reduced, then next_e_has_free_vars.
 *
 * Handler consists of:
 * get_branch_cond: Function that tells if to perform branch. Returns NONE if no, SOME cond
 * if yes, where cond is the condition (a term) to branch upon. Only needs the current
 * step_thm as parameter.
 *
 * comp_thm: Theorem which composes step theorems
 *
 * take_regular_step: Function that returns a new step theorem. The core problem to solve
 * when implementing this is deciding what to eval/rewrite.
 *
 * new free variable introduction *)

(* eval_under_assum used like:
   eval_under_assum v1model_arch_ty ctx init_astate stop_consts_rewr stop_consts_never ctxt nsteps_max;
 * ctxt is a static evaluation context with theorems to rewrite with (use ASSUME on terms)
 * stop_consts_rewr and stop_consts_never are used for handling externs - telling the
 * evaluation when to halt
 * 
 * *)

(* RESTR_EVAL_RULE constants: *)
val p4_stop_eval_consts =
 [(* “word_1comp”, (* Should be OK? ¬v2w [x; F; T] = v2w [¬x; T; F] *) *)
  “word_2comp”,
  “word_mul”,
  “word_div”,
  “word_mod”,
  “word_add”,
  “saturate_add”,
  “word_sub”,
  “saturate_sub”,
  “word_lsl_bv”, (* TODO: OK to evaluate if second operand has no free variables *)
  “word_lsr_bv”, (* TODO: OK to evaluate if second operand has no free variables *)
  (* “word_and”, (* Should be OK? w2v (v2w [x; F; T] && v2w [y; F; T]) = [x ∧ y; F; T] *) *)
  (* “word_xor”, (* Should be OK? w2v (v2w [x; F; T] ⊕ v2w [y; F; T]) = [x ⇎ y; F; F] *) *)
  (* “word_or”, (* Should be OK? w2v (v2w [x; F; T] ‖ v2w [y; F; T]) = [x ∨ y; F; T] *) *)
  “word_ls”,
  “word_hs”,
  “word_lo”,
  “word_hi”
];

(* TODO: Move *)
fun dest_v_struct_fields strct =
 (map (snd o dest_pair)) $ fst $ dest_list $ dest_v_struct strct
;

(* This simplifies a key until only the match_all application can be reduced next *)
val key_conv = rhs o concl o (SIMP_CONV std_ss [listTheory.MAP, optionTheory.THE_DEF, BETA_THM, listTheory.ZIP, v_of_e_def]);

(* Function that decides whether to branch or not: returns NONE if no branch should
 * be performed, otherwise SOME of a list of cases and a theorem stating the disjunction
 * between them *)
fun p4_should_branch step_thm =
 let
  val (path_tm, astate) = the_final_state_hyp_imp step_thm
 in
  case astate_get_branch_data astate of
    (* Branch point: conditional statement *)
    conditional branch_cond =>
   if is_e_v branch_cond andalso not $ null $ free_vars branch_cond
   then
    let
     val branch_cond' = dest_v_bool $ dest_e_v branch_cond
    in
     SOME (SPEC branch_cond' disj_list_EXCLUDED_MIDDLE)
    end
   else NONE
    (* Branch point: select expression (in transition statement) *)
    (* TODO: For value sets, this needs to be generalised slightly, similar to the apply case *)
  | select (e, keys, def) =>
    if is_e_v e andalso not $ null $ free_vars e
    then
     let
      val sel_val = dest_e_v e
     in
      if is_v_bit sel_val
      then
       let
        val sel_bit = dest_v_bit sel_val
       in
        let
         (* The branch cases for equality with the different keys *)
         val key_branch_conds = map (fn key => mk_eq (sel_bit, key)) keys
         (* Default branch: i.e., neither of the above hold *)
         val def_branch_cond = list_mk_conj $ map (fn key_eq => mk_neg key_eq) key_branch_conds
         (* TODO: OPTIMIZE: Prove this nchotomy theorem using a template theorem and simple
          * specialisation or rewrites, and not in-place with tactics *)
         val disj_thm = prove(mk_disj_list (key_branch_conds@[def_branch_cond]), REWRITE_TAC [disj_list_def] >> metis_tac[])
        in
         SOME disj_thm
        end
       end
      else raise (ERR "p4_should_branch" ("Unsupported select value type: "^(term_to_string sel_val)))
     end
    else NONE
    (* Branch point: table application *)
  | apply (tbl_name, e) =>
(*
val apply (tbl_name, e) = apply (“"t"”, “[e_v (v_bit ([e1; e2; e3; e4; e5; e6; e7; T],8))]”)
*)
    if (hurdUtils.forall is_e_v) (fst $ dest_list e) andalso not $ null $ free_vars e
    then
     let
      (* 1. Extract ctrl from ascope *)
      val ctrl = #4 $ dest_ascope $ #4 $ dest_aenv $ #1 $ dest_astate astate
      (* 2. Extract key sets from ascope using tbl_name *)
      val tbl_opt = rhs $ concl $ EVAL “ALOOKUP ^ctrl ^tbl_name”
     in
      if is_some tbl_opt
      then
       let
	val tbl = dest_some tbl_opt
	(* 3. Construct different branch cases for all the key sets
	 *    N.B.: Can now be logically overlapping! *)
	(* The branch cases for equality with the different table entry keys *)
        (* TODO: Ensure this obtains the entries in correct order - here be dragons in case of
         * funny priorities in the table *)
	val keys = fst $ dest_list $ rhs $ concl $ EVAL “MAP FST $ MAP FST ^tbl”
	val key_branch_conds = map (fn key => key_conv $ mk_comb (key, e)) keys
	val key_branch_conds_neg = map mk_neg $ rev key_branch_conds

	val key_branch_conds' = snd $ foldl (fn (a,(b,c)) => (if null b then b else tl b , (if length b = 1 then a else mk_conj ((list_mk_conj (tl b)), a))::c) ) (key_branch_conds_neg, []) (rev key_branch_conds)


	(* 4. Construct default branch case: i.e., neither of the above hold *)
	val def_branch_cond = list_mk_conj key_branch_conds_neg
	(* 5. Construct disjunction theorem, which now is not a strict disjunction *)
         (* TODO: OPTIMIZE: Prove this nchotomy theorem using a template theorem and simple
          * specialisation or rewrites, and not in-place with tactics *)
        val disj_thm = prove(mk_disj_list (key_branch_conds'@[def_branch_cond]), REWRITE_TAC [disj_list_def] >> metis_tac[])
       in
        SOME disj_thm
       end
      else raise (ERR "p4_should_branch" ("Table not found in ctrl: "^(term_to_string tbl_name)))
     end
    else NONE
  | no_branch => NONE
 end
;

(*
fun term_to_debug_string tm =
 let
  val tm_str_opt = String.fromString $ term_to_string tm
 in
  if isSome tm_str_opt
  then valOf tm_str_opt
  else ("\n\n (ERROR: Could not convert escape characters, printing term verbatim) \n\n"^(term_to_string tm))
 end
;
*)

val (match_all_tm,  mk_match_all, dest_match_all, is_match_all) =
  syntax_fns1 "p4_aux" "match_all";

fun p4_regular_step_get_err_msg path_cond step_thm =
 let
  (* Get number of steps *)
  val (assl, exec_thm) = dest_imp $ concl step_thm
  val (exec_tm, res_opt) = dest_eq exec_thm
  val (_, _, nsteps) = dest_arch_multi_exec exec_tm
  (* TODO: Print path condition? *)
  (* TODO: Get next stmt to be reduced in proper format *)
(* DEBUG: *)
  val _ = print "\n\nDEBUG OUTPUT: State prior to failure is:\n";
  val _ = print $ term_to_string $ dest_some res_opt;
  val _ = print "\n\nDEBUG OUTPUT: Path condition prior to failure is:\n";
  val _ = print $ term_to_string $ concl path_cond;
  val _ = print "\n\n";

  val next_state_str =
   if is_some res_opt
   then (term_to_string $ dest_some res_opt)
   else "NONE"
 in
  (("error encountered at (regular) step "^(term_to_string nsteps))^".")
(*
  (("error encountered at step "^(term_to_string nsteps))^(". State prior to failure is: ")^((next_state_str)^(" \n\n and path condition is: "^(term_to_debug_string $ concl path_cond))))
*)
 end
;

fun p4_eval_ctxt_gen (stop_consts1, stop_consts2, mk_exec) path_cond astate =
 eval_ctxt_gen stop_consts1 stop_consts2 path_cond (mk_exec astate)
;

(* TODO: Expression reduction debug output *)
fun dbg_print_e_red (func_map, b_func_map, ext_fun_map) e =
 (* Note no e_v case *)
 if is_e_var e
 then print (String.concat ["\nReducing variable...\n\n"])
 else if is_e_list e
 (* TODO: No reductions for list *)
 then raise (ERR "dbg_print_e_red" ("Unsupported expression: "^(term_to_string e)))
 else if is_e_acc e
 then
  let
   val (e', x) = dest_e_acc e
  in
   if is_e_v e'
   then print (String.concat ["\nReducing field access...\n\n"])
   else dbg_print_e_red (func_map, b_func_map, ext_fun_map) e'
  end
 else if is_e_unop e
 then
  let
   val (unop, e') = dest_e_unop e
  in
   if is_e_v e'
   then print (String.concat ["\nReducing unary operation...\n\n"])
   else dbg_print_e_red (func_map, b_func_map, ext_fun_map) e'
  end
 else if is_e_cast e
 then
  let
   val (cast, e') = dest_e_cast e
  in
   if is_e_v e'
   then print (String.concat ["\nReducing cast...\n\n"])
   else dbg_print_e_red (func_map, b_func_map, ext_fun_map) e'
  end
 else if is_e_binop e
 then
  let
   val (e', binop, e'') = dest_e_binop e
  in
   if is_e_v e'
   then
    if is_e_v e''
    then print (String.concat ["\nReducing binary operation...\n\n"])
    else dbg_print_e_red (func_map, b_func_map, ext_fun_map) e''
   else dbg_print_e_red (func_map, b_func_map, ext_fun_map) e'
  end
 else if is_e_concat e
 then
  let
   val (e', e'') = dest_e_concat e
  in
   if is_e_v e'
   then
    if is_e_v e''
    then print (String.concat ["\nReducing bit-string concatenation...\n\n"])
    else dbg_print_e_red (func_map, b_func_map, ext_fun_map) e''
   else dbg_print_e_red (func_map, b_func_map, ext_fun_map) e'
  end
 else if is_e_slice e
 then
  let
   val (e', e'', e''') = dest_e_slice e
  in
   if is_e_v e'
   then
    if is_e_v e''
    then
     if is_e_v e'''
     then print (String.concat ["\nReducing bit-string slicing operation...\n\n"])
     else dbg_print_e_red (func_map, b_func_map, ext_fun_map) e'''
    else dbg_print_e_red (func_map, b_func_map, ext_fun_map) e''
   else dbg_print_e_red (func_map, b_func_map, ext_fun_map) e'
  end
 else if is_e_call e
 then
  let
   val (funn, e_list) = dest_e_call e
   val d_list = get_funn_dirs funn (func_map, b_func_map, ext_fun_map)
  in
   if dbg_print_arg_list_red (func_map, b_func_map, ext_fun_map) (zip (fst $ dest_list e_list) d_list)
   then print (String.concat ["\nReducing function call...\n\n"])
   else ()
  end
 else if is_e_select e
 then
  let
   val (e', v_x_list, x) = dest_e_select e
  in
   if is_e_v e'
   then print (String.concat ["\nReducing select expression...\n\n"])
   else dbg_print_e_red (func_map, b_func_map, ext_fun_map) e'
  end
 else if is_e_struct e
 then
  let
   val x_e_list = dest_e_struct e
  in
   if dbg_print_e_list_red (func_map, b_func_map, ext_fun_map) ((map (snd o dest_pair)) $ fst $ dest_list x_e_list)
   then print (String.concat ["\nReducing struct expression...\n\n"])
   else ()
  end
 else if is_e_header e
 then
  let
   val (boolv, x_e_list) = dest_e_header e
  in
   if dbg_print_e_list_red (func_map, b_func_map, ext_fun_map) ((map (snd o dest_pair)) $ fst $ dest_list x_e_list)
   then print (String.concat ["\nReducing header expression...\n\n"])
   else ()
  end
 else raise (ERR "dbg_print_e_red" ("Unsupported expression: "^(term_to_string e)))
and dbg_print_e_list_red (func_map, b_func_map, ext_fun_map) [] =
   true
  | dbg_print_e_list_red (func_map, b_func_map, ext_fun_map) (h::t) =
   if is_e_v h
   then dbg_print_e_list_red (func_map, b_func_map, ext_fun_map) t
   else
    let
     val _ = dbg_print_e_red (func_map, b_func_map, ext_fun_map) h
    in
     false
    end
and dbg_print_arg_list_red (func_map, b_func_map, ext_fun_map) [] =
   true
  | dbg_print_arg_list_red (func_map, b_func_map, ext_fun_map) ((arg,dir)::t) =
   if is_arg_red (arg, dir)
   then dbg_print_arg_list_red (func_map, b_func_map, ext_fun_map) t
   else
    let
     val _ = dbg_print_e_red (func_map, b_func_map, ext_fun_map) arg
    in
     false
    end
;

(* TODO: Add # seq nestings to debug output *)
fun dbg_print_stmt_red (func_map, b_func_map, ext_fun_map) stmt =
 if is_stmt_empty stmt
 then print (String.concat ["\nReducing empty statement...\n\n"])
 else if is_stmt_ass stmt
 then
  let
   val (lval, e) = dest_stmt_ass stmt
  in
   if is_e_v e
   then print (String.concat ["\nReducing assignment...\n\n"])
   else dbg_print_e_red (func_map, b_func_map, ext_fun_map) e
  end
 else if is_stmt_cond stmt
 then
  let
   val (e, stmt', stmt'') = dest_stmt_cond stmt
  in
   if is_e_v e
   then print (String.concat ["\nReducing conditional statement...\n\n"])
   else dbg_print_e_red (func_map, b_func_map, ext_fun_map) e
  end
 else if is_stmt_block stmt
 then print (String.concat ["\nReducing block statement...\n\n"])
 else if is_stmt_ret stmt
 then 
  let
   val e = dest_stmt_ret stmt
  in
   if is_e_v e
   then print (String.concat ["\nReducing return statement...\n\n"])
   else dbg_print_e_red (func_map, b_func_map, ext_fun_map) e
  end
 else if is_stmt_seq stmt
 then
  let
   val (stmt', stmt'') = dest_stmt_seq stmt
  in
   dbg_print_stmt_red (func_map, b_func_map, ext_fun_map) stmt'
  end
 else if is_stmt_trans stmt
 then 
  let
   val e = dest_stmt_trans stmt
  in
   if is_e_v e
   then print (String.concat ["\nReducing transition statement...\n\n"])
   else dbg_print_e_red (func_map, b_func_map, ext_fun_map) e
  end
 else if is_stmt_app stmt
 then
  let
   val (x, e_list) = dest_stmt_app stmt
  in
   (* TODO: A little overkill. Make a stmt_get_next_e_syntax_f_list instead *)
   (case dbg_print_e_list_red (func_map, b_func_map, ext_fun_map) (fst $ dest_list e_list) of
      true => ()
    | false => print (String.concat ["\nReducing apply statement...\n\n"]))
  end
 else if is_stmt_ext stmt
 then print (String.concat ["\nReducing extern statement...\n\n"])
 else raise (ERR "dbg_print_stmt_red" ("Unsupported statement: "^(term_to_string stmt)))
;

fun p4_regular_step (debug_flag, ctx_def, ctx, eval_ctxt) comp_thm (path_cond, step_thm) =
 let
  (* DEBUG *)
  val _ = dbg_print debug_flag (String.concat ["\nCommencing regular step from state with path condition: ",
				(term_to_string $ concl path_cond),
				"\n"])

  (* DEBUG *)
  val time_start = Time.now();

  (* We can't let evaluation open match_all, or we won't be able to use our path condition,
   * where branch cases for table application are phrased in terms of match_all *)
(* OLD:
  val table_stop_consts = [match_all_tm]
  val astate = the_final_state_imp step_thm
  val multi_exec_tm = mk_arch_multi_exec (ctx, astate, 1);
  val step_thm2 =
   eval_ctxt_gen (stop_consts_rewr@stop_consts_never@p4_stop_eval_consts@table_stop_consts)
                 (stop_consts_never@p4_stop_eval_consts) path_cond
                 multi_exec_tm;
*)

  val astate = the_final_state_imp step_thm
  val (func_map, b_func_map, ext_fun_map) = get_f_maps (astate, ctx)

  (* DEBUG *)
  val _ =
   if debug_flag
   then
    case astate_get_top_stmt astate of
       NONE => ()
     | SOME stmt => dbg_print_stmt_red (func_map, b_func_map, ext_fun_map) stmt
   else ()

    val step_thm2 = eval_ctxt path_cond astate
    (* DEBUG *)
    val _ = dbg_print debug_flag (String.concat ["evaluation-in-context: ",
				  (LargeInt.toString $ Time.toMilliseconds ((Time.now()) - time_start)),
				  " ms\n"])

  (* DEBUG:
  val stop_consts1 = (stop_consts_rewr@stop_consts_never@p4_stop_eval_consts@table_stop_consts);
  val stop_consts2 = (stop_consts_never@p4_stop_eval_consts);
  val ctxt = path_cond;
  val tm = (mk_arch_multi_exec (ctx, astate, 1));
  *)
    (* No timing printed for the below, it takes less than 0 ms *)
    (* TODO: Do this in a nicer way... *)
  (* ???
    val next_e_opt = astate_get_next_e (func_map, b_func_map, ext_fun_map) astate
  *)
    val extra_rewr_thms =
     (case astate_get_next_e_syntax_f (func_map, b_func_map, ext_fun_map) astate of
  (*
  val SOME next_e_syntax_f = astate_get_next_e_syntax_f (func_map, b_func_map, ext_fun_map) astate
  *)
	NONE => [] (* Reduction did not even consider reducing an e *)
      | SOME next_e_syntax_f =>
       (case e_get_next_subexp_syntax_f (func_map, b_func_map, ext_fun_map) (next_e_syntax_f astate) of
  (*
  val SOME next_subexp_syntax_f = e_get_next_subexp_syntax_f (func_map, b_func_map, ext_fun_map) (next_e_syntax_f astate)
  *)
	  SOME next_subexp_syntax_f =>
	 let
	  val next_subexp = next_subexp_syntax_f (next_e_syntax_f astate)
	 in
	  if (null $ free_vars $ next_subexp) andalso (not $ is_e_call next_subexp)
	  then (* Reduction from a subexp without free variables *)
	   let
	    (* Then, get the resulting subexp *)
	    val subexp_red_res =
	     next_subexp_syntax_f $ next_e_syntax_f $ the_final_state_imp step_thm2
	    (* Evaluate the subexp without restrictions *)
	    val subexp_red_res_EVAL = EVAL subexp_red_res
	   in
	    (* Now, rewrite with this result *)
	    [subexp_red_res_EVAL]
	   end
	  else [] (* Reduction from e_call, or a subexp with free variables *)
	 end
	| NONE => []))
   in
    let

     (* DEBUG *)
     val time_start = Time.now();

     val res =
      SIMP_RULE simple_arith_ss extra_rewr_thms
       (MATCH_MP (MATCH_MP comp_thm (PURE_REWRITE_RULE [GSYM ctx_def] step_thm)) (PURE_REWRITE_RULE [GSYM ctx_def] step_thm2))

  (* TEST:
     val res =
      SIMP_RULE simple_arith_ss extra_rewr_thms
       (PURE_REWRITE_RULE [(PURE_REWRITE_RULE [GSYM ctx_def] step_thm2), REFL_CLAUSE, Once IMP_CLAUSES]
	(SPECL ((fn (a,b,c,d) => [``1:num``,a,b,c,d]) $ dest_astate $ the_final_state_imp step_thm2) (MATCH_MP comp_thm (PURE_REWRITE_RULE [GSYM ctx_def] step_thm))))
  *)

     (* DEBUG *)
     val _ = dbg_print debug_flag (String.concat ["step_thm composition: ",
				   (LargeInt.toString $ Time.toMilliseconds ((Time.now()) - time_start)),
				   " ms\n"])
    in
     res
    end
    handle (HOL_ERR exn) =>
     raise (if (is_none $ rhs $ snd $ dest_imp $ concl step_thm2)
	   then (ERR "p4_regular_step" ("Unexpected reduction to NONE from frame list: "^(term_to_string $ #3 $ dest_astate $ the_final_state_imp step_thm)))
	   else (HOL_ERR exn))
  end
  handle (HOL_ERR exn) => raise (ERR "p4_regular_step" (p4_regular_step_get_err_msg path_cond step_thm)) (* (wrap_exn "p4_symb_exec" "p4_regular_step" (HOL_ERR exn)) *)
;

(* Function that decides whether a HOL4P4 program is finished or not *)
fun p4_is_finished step_thm =
 let
  val astate = the_final_state_imp step_thm
  val (aenv, _, _, _) = dest_astate astate
  val (i, io_list, _, _) = dest_aenv aenv
 in
  (* Whenever the result of taking one step is at block index 0 with no further input
   * in the input queue, we're finished *)
  if int_of_term i = 0 andalso null $ fst $ dest_list io_list
  then true
  else false
 end
;

(* The main symbolic execution.
 * Here, the static ctxt and the dynamic path condition have been merged. *)
fun p4_symb_exec debug_flag arch_ty (ctx_def, ctx) init_astate stop_consts_rewr stop_consts_never path_cond fuel =
 let
  val comp_thm = INST_TYPE [Type.alpha |-> arch_ty] arch_multi_exec_comp_n_tl_assl
  val init_step_thm = eval_ctxt_gen (stop_consts_rewr@stop_consts_never) stop_consts_never path_cond (mk_arch_multi_exec (ctx, init_astate, 0))

  val table_stop_consts = [match_all_tm]
  val eval_ctxt = p4_eval_ctxt_gen ((stop_consts_rewr@stop_consts_never@p4_stop_eval_consts@table_stop_consts), (stop_consts_never@p4_stop_eval_consts), (fn astate => mk_arch_multi_exec (ctx, astate, 1)))
  val regular_step = p4_regular_step (debug_flag, ctx_def, ctx, eval_ctxt) comp_thm
 in
(* DEBUG:
val lang_regular_step = p4_regular_step (debug_flag, ctx_def, ctx, eval_ctxt) comp_thm;
val lang_init_step_thm = init_step_thm;
val lang_should_branch = p4_should_branch;
val lang_is_finished = p4_is_finished;
*)
  symb_exec (regular_step, init_step_thm, p4_should_branch, p4_is_finished) path_cond fuel
 end
  handle (HOL_ERR exn) => raise (wrap_exn "p4_symb_exec" "p4_symb_exec" (HOL_ERR exn))
;

(* This takes a list of n-step theorems resulting from executing the P4 program (with IDs)
 * as well as a path tree structure, and uses this to merge all the branches using a
 * depth-first strategy.
 * The result is a single contract phrased in terms of p4_contract_def, with the
 * initial path condition as precondition *)
local
fun p4_unify_path_tree' id_ctthm_list (node (id, path_disj_thm, [])) [] =
   (case List.find (fn (id', ct_thm) => id = id') id_ctthm_list of
     SOME (id'', thm) => thm
   | NONE => raise (ERR "p4_unify_path_tree" ("Could not find contract with id: "^(int_to_string id))))
  | p4_unify_path_tree' id_ctthm_list (node (id, path_disj_thm, [])) path_tree_list_leafs =
   (* Unify *)
   let
    (* The idea is to use p4_symb_exec_unify_n_gen to unify all
     * paths resulting from a single branch (i.e. in the list of a node in path_tree). *)
    val path_tree_list_leafs_thm =
     if length path_tree_list_leafs = 1
     then hd path_tree_list_leafs
     else foldl (fn (thm, thm') => CONJ thm' thm)
	   (hd path_tree_list_leafs)
	   (tl path_tree_list_leafs)
    val path_cond_tm = fst $ dest_symb_branch_cases $ concl path_disj_thm
    val p4_contract_list_thm =
     PURE_REWRITE_RULE [SPEC path_cond_tm p4_contract_list_GSYM_REWR,
                        SPEC path_cond_tm p4_contract_list_REWR,
                        listTheory.APPEND] path_tree_list_leafs_thm
   in
     MATCH_MP (MATCH_MP p4_symb_exec_unify_n_gen path_disj_thm) p4_contract_list_thm
   end
  | p4_unify_path_tree' id_ctthm_list (node (id, path_disj_thm, (h::t))) path_tree_list_leafs =
(* DEBUG: Two iterations, for debugging a simple branch:
val (node (id, path_disj_thm, (h::t))) = path_tree;
val ctthm' = p4_unify_path_tree' id_ctthm_list h []
val path_tree_list_leafs = ([ctthm'])

val (node (id, path_disj_thm, (h::t))) = (node (id, path_disj_thm, t));
val ctthm' = p4_unify_path_tree' id_ctthm_list h []
val path_tree_list_leafs = (path_tree_list_leafs@[ctthm'])

(* Two more, for multi-case: *)
val (node (id, path_disj_thm, (h::t))) = (node (id, path_disj_thm, t));
val ctthm' = p4_unify_path_tree' id_ctthm_list h []
val path_tree_list_leafs = (path_tree_list_leafs@[ctthm'])

val (node (id, path_disj_thm, (h::t))) = (node (id, path_disj_thm, t));
val ctthm' = p4_unify_path_tree' id_ctthm_list h []
val path_tree_list_leafs = (path_tree_list_leafs@[ctthm'])
*)
   (* Recursive call *)
   let
    val ctthm' = p4_unify_path_tree' id_ctthm_list h []
   in
    p4_unify_path_tree' id_ctthm_list (node (id, path_disj_thm, t)) (path_tree_list_leafs@[ctthm'])
   end
  | p4_unify_path_tree' _ _ _ = raise (ERR "p4_unify_path_tree" "Unknown path tree format")
in 
fun p4_unify_path_tree id_ctthm_list path_tree =
 p4_unify_path_tree' id_ctthm_list path_tree []
  handle (HOL_ERR exn) => raise (wrap_exn "p4_symb_exec" "p4_unify_path_tree" (HOL_ERR exn));
end
;

(* Proves that postcond holds for the final state of a step_thm *)
fun p4_prove_postcond rewr_thms postcond step_thm =
 let
  val prel_res_thm = HO_MATCH_MP symb_exec_add_postcond step_thm
  val (hypo, step_tm) = dest_imp $ concl step_thm
  val res_state_tm = dest_some $ snd $ dest_eq step_tm
  (* TODO: OPTIMIZE: srw_ss??? *)
  val postcond_thm = EQT_ELIM $ SIMP_CONV (srw_ss()) rewr_thms $ mk_imp (hypo, mk_comb (postcond, res_state_tm))
 in
  MATCH_MP prel_res_thm postcond_thm
 end
;

(* This function is the main workhorse for proving contracts on HOL4P4 programs.
 * The parameters are:
 *
 * arch_ty: the architecture hol_type, e.g. p4_v1modelLib.v1model_arch_ty
 *
 * ctx: a term containing the HOL4P4 environment (static information held in semantics)
 *
 * init_astate: a term containing the initial HOL4P4 architecture-level state,
 *
 * stop_consts_rewr: definitions for which eval_ctxt_gen stops and allows rewriting, as
 * terms
 *
 * stop_consts_never: definitions which eval_ctxt_gen never should unfold
 *
 * path_cond: the initial path condition, which can be thought of as a precondition, stated
 * as a theorem, e.g. ASSUME (b8 = T).
 *
 * n_max: the maximum number of steps the symbolic execution can take per branch.
 *
 * postcond: the postcondition, a term which is a predicate on the architectural state *)
(* Note: precondition strengthening is probably not needed, since initial path condition is
 * provided freely *)
fun p4_symb_exec_prove_contract debug_flag arch_ty ctx init_astate stop_consts_rewr stop_consts_never path_cond n_max postcond =
 let

  (* DEBUG *)
  val time_start = Time.now();

  val ctx_name = "ctx"
  val ctx_def = hd $ Defn.eqns_of $ Defn.mk_defn ctx_name (mk_eq(mk_var(ctx_name, type_of ctx), ctx))

  (* Perform symbolic execution until all branches are finished *)
  val (path_tree, path_cond_step_list) =
   p4_symb_exec debug_flag arch_ty (ctx_def, ctx) init_astate stop_consts_rewr stop_consts_never path_cond n_max;

  (* DEBUG *)
  val _ = dbg_print debug_flag (String.concat ["\nFinished entire symbolic execution stage in ", (LargeInt.toString $ Time.toSeconds ((Time.now()) - time_start)), "s, trying to prove postcondition...\n\n"]);
  val time_start = Time.now();

  (* Prove postcondition holds for all resulting states in n-step theorems *)
  val id_step_post_thm_list =
   map (fn (a,b,c) => (a, p4_prove_postcond [packet_has_port_def] postcond c)) path_cond_step_list

  (* DEBUG *)
  val _ = dbg_print debug_flag (String.concat ["\nFinished proof of postcondition for all step theorems in ", (LargeInt.toString $ Time.toSeconds ((Time.now()) - time_start)), "s, trying to rewrite step theorems to contract format...\n\n"]);
  val time_start = Time.now();

  (* Rewrite n-step theorems to a contract format *)
  val id_ctthm_list = map (fn (a,b) => (a, MATCH_MP p4_symb_exec_to_contract b)) id_step_post_thm_list

  (* DEBUG *)
  val _ = dbg_print debug_flag (String.concat ["\nFinished rewriting step theorems to contract format in ", (LargeInt.toString $ Time.toSeconds ((Time.now()) - time_start)), "s, trying to unify contracts...\n\n"]);
  val time_start = Time.now();

  (* Unify all contracts *)
  val unified_ct_thm = p4_unify_path_tree id_ctthm_list path_tree;

  (* DEBUG *)
  val _ = dbg_print debug_flag (String.concat ["\nFinished unification of all contracts in ", (LargeInt.toString $ Time.toSeconds ((Time.now()) - time_start)), "s.\n\n"]);

 in
  unified_ct_thm
 end
;

fun dest_step_thm step_thm =
 dest_astate $ dest_some $ snd $ dest_eq $ snd $ dest_imp $ concl step_thm
;

fun p4_debug_symb_exec arch_ty ctx init_astate stop_consts_rewr stop_consts_never path_cond fuel =
 let
  val ctx_name = "ctx"
  val ctx_def = hd $ Defn.eqns_of $ Defn.mk_defn ctx_name (mk_eq(mk_var(ctx_name, type_of ctx), ctx))

  val (path_tree, state_list) = p4_symb_exec true arch_ty (ctx_def, ctx) init_astate stop_consts_rewr stop_consts_never path_cond fuel
  val state_list_tms = map (fn (path_id, path_cond, step_thm) => (path_id, path_cond, dest_step_thm step_thm)) state_list
 in
  (path_tree, state_list_tms)
 end
;

fun p4_debug_symb_exec_frame_lists arch_ty ctx init_astate stop_consts_rewr stop_consts_never path_cond fuel =
 let
  val (path_tree, state_list_tms) = p4_debug_symb_exec arch_ty ctx init_astate stop_consts_rewr stop_consts_never path_cond fuel
  val arch_frame_list_tms = map (fn (path_id, path_cond, (tm1, tm2, tm3, tm4)) => tm3) state_list_tms
 in
  (path_tree, arch_frame_list_tms)
 end
;

end
