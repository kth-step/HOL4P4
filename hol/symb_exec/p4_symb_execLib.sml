structure p4_symb_execLib :> p4_symb_execLib = struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

open pairSyntax listSyntax numSyntax computeLib hurdUtils;

open p4Theory p4_exec_semTheory p4Syntax p4_exec_semSyntax;

open symb_execTheory p4_symb_execTheory;

open evalwrapLib p4_testLib;

open optionSyntax;

val ERR = mk_HOL_ERR "p4_symb_exec"

(* TODO: Rename "branch condition"? Is this terminology OK? *)

(* TODO: The below two are also found in p4_testLib.sml - put elsewhere? *)
fun the_final_state_imp step_thm =
 let
  val step_thm_tm = concl step_thm
 in
  dest_some $ snd $ dest_eq $ 
   (if is_imp step_thm_tm
    then snd $ dest_imp $ step_thm_tm
    else step_thm_tm)
 end
val simple_arith_ss = pure_ss++numSimps.REDUCE_ss

fun get_actx step_thm =
 let
  val step_thm_tm = concl step_thm
 in
  #1 $ dest_arch_multi_exec $ fst $ dest_eq $ 
   (if is_imp step_thm_tm
    then snd $ dest_imp $ step_thm_tm
    else step_thm_tm)
 end

(* TODO: Move to syntax library *)
fun dest_frame frame =
 case spine_pair frame of
    [funn, stmt_stack, scope_list] => (funn, stmt_stack, scope_list)
  | _ => raise (ERR "dest_frame" ("Unsupported frame shape: "^(term_to_string frame)))
;
fun dest_actx actx =
 case spine_pair actx of
    [ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_fun_map, func_map] => (ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_fun_map, func_map)
  | _ => raise (ERR "dest_actx" ("Unsupported actx shape: "^(term_to_string actx)))
;
fun dest_astate astate =
 case spine_pair astate of
    [aenv, g_scope_list, arch_frame_list, status] => (aenv, g_scope_list, arch_frame_list, status)
  | _ => raise (ERR "dest_astate" ("Unsupported astate shape: "^(term_to_string astate)))
;
(* TODO: Fix this hack *)
fun dest_aenv aenv =
 let
  val (i, aenv') = dest_pair aenv
  val (io_list, aenv'') = dest_pair aenv'
  val (io_list', ascope) = dest_pair aenv''
 in
  (i, io_list, io_list', ascope)
 end
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
     if is_pblock_regular pblock 
     then SOME $ #2 $ dest_pblock_regular pblock
     else NONE
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

fun astate_get_cond astate =
 case astate_get_top_stmt astate of
   SOME stmt =>
  let
   val stmt' = stmt_get_next stmt
  in
   if is_stmt_cond stmt'
   then SOME $ #1 $ dest_stmt_cond stmt'
   else NONE
  end
 | NONE => NONE
;

(* TODO: This should be done in pre-processing, not at every step *)
fun get_f_maps step_thm =
 let
  val astate = the_final_state_imp step_thm
  val actx = get_actx step_thm
  val (ab_list, pblock_map, _, _, _, _, _, _, ext_fun_map, func_map) = dest_actx actx
  val (aenv, _, _, _) = dest_astate astate
  val (i, _, _, _) = dest_aenv aenv
  val b_func_map_opt = get_b_func_map i ab_list pblock_map
 in
  case get_b_func_map i ab_list pblock_map of
    SOME b_func_map => (func_map, b_func_map, ext_fun_map)
  | NONE => (func_map, “[]:b_func_map”, ext_fun_map)
 end
;

(* TODO: Get rid of EVAL hack *)
fun get_funn_dirs funn (func_map, b_func_map, ext_fun_map) =
 let
  val funn_sig_opt = rhs $ concl $ EVAL “lookup_funn_sig ^funn ^func_map ^b_func_map ^ext_fun_map”
 in
  if is_some funn_sig_opt
  then
    fst $ dest_list $ rhs $ concl $ EVAL “MAP SND ^(dest_some funn_sig_opt)”
  else raise (ERR "get_funn_dirs" ("Signature of funn not found in function maps: "^(term_to_string funn)))
 end
;

(* TODO: Get rid of EVAL hack *)
fun is_arg_red (arg, dir) =
 if is_d_out dir
 then term_eq T (rhs $ concl $ EVAL “is_e_lval ^arg”) (* Must be lval *)
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
    | NONE => NONE)
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
 then
  let
   val (t_scope, stmt') = dest_stmt_block stmt
  in
   (case stmt_get_next_e_syntax_f (func_map, b_func_map, ext_fun_map) stmt' of
      SOME f => SOME (f o snd o dest_stmt_block)
    | NONE => NONE)
  end
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
      val [funn, stmt_stack, scope_list] = strip_pair (el 1 frame_list)
      val stmt_stack' = fst $ dest_list stmt_stack
     in
      if null stmt_stack'
      then NONE
      else
      (case stmt_get_next_e_syntax_f (func_map, b_func_map, ext_fun_map) (el 1 stmt_stack') of
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
      val [funn, stmt_stack, scope_list] = strip_pair (el 1 frame_list)
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

(* Function that decides whether to branch or not *)
(* TODO: This is a P4-specific function that has been factored out, make it an argument of
 * the generic symb_exec *)
fun p4_should_branch step_thm =
  case astate_get_cond $ the_final_state_imp step_thm of
    SOME branch_cond =>
   if is_e_v branch_cond andalso not $ null $ free_vars branch_cond
   then SOME (dest_v_bool $ dest_e_v branch_cond)
   else NONE
  | NONE => NONE
;

fun p4_regular_step ctx stop_consts_rewr stop_consts_never comp_thm (path_cond, step_thm) =
 let
  val astate = the_final_state_imp step_thm
  val step_thm2 =
   eval_ctxt_gen (stop_consts_rewr@stop_consts_never@p4_stop_eval_consts)
                 (stop_consts_never@p4_stop_eval_consts) path_cond
                 (mk_arch_multi_exec (ctx, astate, 1));
  (* TODO: This could take only astate and actx as args *)
  val (func_map, b_func_map, ext_fun_map) = get_f_maps step_thm
  (* TODO: Do this in a nicer way... *)
  val next_e_opt = astate_get_next_e (func_map, b_func_map, ext_fun_map) astate
  val extra_rewr_thms =
   (case astate_get_next_e_syntax_f (func_map, b_func_map, ext_fun_map) astate of
      NONE => [] (* Reduction did not even consider reducing an e *)
    | SOME next_e_syntax_f =>
     (case e_get_next_subexp_syntax_f (func_map, b_func_map, ext_fun_map) (next_e_syntax_f astate) of
        SOME next_subexp_syntax_f =>
       let
        val next_subexp = next_subexp_syntax_f (next_e_syntax_f astate)
       in
        if null $ free_vars $ next_subexp
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
        else [] (* Reduction from a subexp with free variables *)
       end
      | NONE =>
       (* e_call was reduced *)
       []))
 in
  SIMP_RULE simple_arith_ss extra_rewr_thms
   (MATCH_MP (MATCH_MP comp_thm step_thm) step_thm2)
 end
;

(* Function that decides whether we are finished or not *)
(* TODO: This is a P4-specific function that has been factored out, make it an argument of
 * the generic symb_exec *)
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

local
(* Symbolic execution with branching on if-then-else
 * Width-first scheduling (positive case first)
 * Note that branching consumes one step of fuel
 * Here, the static ctxt and the dynamic path condition have been merged.
 * Currently, the path condition is stripped down as much as possible from p4-specific stuff
 * (another design priority could be legibility and keeping the connection to the P4 constructs). *)
fun symb_exec' arch_ty ctx stop_consts_rewr stop_consts_never comp_thm [] finished_list =
 finished_list
  | symb_exec' arch_ty ctx stop_consts_rewr stop_consts_never comp_thm
               ((path_cond, step_thm, 0)::t) finished_list =
   symb_exec' arch_ty ctx stop_consts_rewr stop_consts_never comp_thm t
              (finished_list@[(path_cond, step_thm)])
  | symb_exec' arch_ty ctx stop_consts_rewr stop_consts_never comp_thm
               ((path_cond, step_thm, fuel)::t) finished_list =
   (* Check if we should branch or take regular step
    * p4_should_branch can be made an argument: it takes the current step theorem
    * and returns a term with the branch condition, with which you can split the
    * path condition *)
   (case p4_should_branch step_thm of
     SOME branch_cond =>
     (* Branch + prune *)
     let
      (* Get new path conditions for the positive and negative cases *)
      val path_cond_pos = CONJ path_cond (ASSUME branch_cond)
      val path_cond_neg = CONJ path_cond (ASSUME $ mk_neg branch_cond)
      (* Check if the new path conditions contradict themselves *)
      val is_path_cond_pos_F = Feq $ concl (SIMP_RULE std_ss [] path_cond_pos)
      val is_path_cond_neg_F = Feq $ concl (SIMP_RULE std_ss [] path_cond_neg)
      (* Prune away symbolic states with contradictory path_cond, otherwise add them to
       * end of procesing queue. Positive case goes before negative. *)
      val next_astate_pos =
       if is_path_cond_pos_F
       then []
       else [(path_cond_pos, DISCH_CONJUNCTS_ALL $ REWRITE_RULE [path_cond_pos] step_thm, fuel-1)]
      val next_astate_neg =
       if is_path_cond_neg_F
       then []
       else [(path_cond_neg, DISCH_CONJUNCTS_ALL $ REWRITE_RULE [path_cond_neg] step_thm, fuel-1)]
     in
      symb_exec' arch_ty ctx stop_consts_rewr stop_consts_never comp_thm
                 (t@(next_astate_pos@next_astate_neg)) finished_list
     end
    | NONE =>
     (* Do not branch - compute one regular step *)
     let
      val next_step_thm =
       p4_regular_step ctx stop_consts_rewr stop_consts_never comp_thm (path_cond, step_thm)
     in
      if p4_is_finished next_step_thm
      then
       symb_exec' arch_ty ctx stop_consts_rewr stop_consts_never comp_thm
		  t (finished_list@[(path_cond, next_step_thm)])
      else
       symb_exec' arch_ty ctx stop_consts_rewr stop_consts_never comp_thm
		  (t@[(path_cond, next_step_thm, fuel-1)]) finished_list
     end)
in
fun symb_exec arch_ty ctx init_astate stop_consts_rewr stop_consts_never path_cond fuel =
 let
  (* TODO: Also branch check here? *)
  val step_thm =
   eval_ctxt_gen (stop_consts_rewr@stop_consts_never) stop_consts_never path_cond (mk_arch_multi_exec (ctx, init_astate, 1));
  (* TODO: Make arch_multi_exec_comp_n_tl_assl "init_comp_thm" and an argument *)
  val comp_thm = INST_TYPE [Type.alpha |-> arch_ty] arch_multi_exec_comp_n_tl_assl;
 in
  if fuel = 1
  then [(path_cond, step_thm)]
  else symb_exec' arch_ty ctx stop_consts_rewr stop_consts_never comp_thm [(path_cond, step_thm, (fuel-1))] []
 end
end;

fun p4_prove_postcond rewr_thms postcond step_thm =
 let
  val prel_res_thm = HO_MATCH_MP symb_exec_add_postcond step_thm
  (* TODO: srw_ss??? *)
  val postcond_thm = EQT_ELIM $ SIMP_CONV (srw_ss()) rewr_thms $ mk_comb (postcond, the_final_state_imp step_thm)
 in
  MATCH_MP prel_res_thm postcond_thm
 end
;

(* TODO: Note that the resulting contract has the initial assumption as precondition, i.e. no precondition
 * strengthening takes place. *)
fun p4_symb_exec_prove_contract arch_ty ctx init_astate stop_consts_rewr stop_consts_never path_cond n_max postcond =
 let
  val path_cond_step_list =
   symb_exec arch_ty ctx init_astate stop_consts_rewr stop_consts_never path_cond n_max;
  (* Add postcondition *)
  val step_post_thm_list = map (p4_prove_postcond [packet_has_port_def] postcond o snd) path_cond_step_list
  (* Rewrite to a contract format *)
  val ct_thm_list = map (MATCH_MP p4_symb_exec_to_contract) step_post_thm_list
  (* TODO: Make a general unification strategy - this only works for 1 or 2 elements *)
  val unified_ct_thm =
   if length ct_thm_list = 1
   then el 1 ct_thm_list
   else MATCH_MP (MATCH_MP p4_symb_exec_unify (el 1 ct_thm_list)) (el 2 ct_thm_list)
 in
  unified_ct_thm
 end
;

end
