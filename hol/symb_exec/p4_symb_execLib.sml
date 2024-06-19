structure p4_symb_execLib :> p4_symb_execLib = struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

open pairSyntax listSyntax numSyntax computeLib hurdUtils;

open p4Theory p4_exec_semTheory p4Syntax p4_exec_semSyntax;
open p4_coreTheory;
open symb_execTheory symb_execSyntax p4_symb_execTheory p4_bigstepTheory;

open evalwrapLib p4_testLib bitstringLib;
open symb_execLib;

open optionSyntax listSyntax (* wordsSyntax *);

val ERR = mk_HOL_ERR "p4_symb_exec"

(* Prefix used by the symbolic execution when inserting free HOL4 variables *)
val p4_symb_arg_prefix = "a";

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

fun arch_frame_list_get_top_funn_stmt arch_frame_list =
 if is_arch_frame_list_empty arch_frame_list
 then NONE
 else
  let
   val top_frame = el 1 $ fst $ dest_list $ dest_arch_frame_list_regular arch_frame_list
   val (funn, stmt_stack, _) = dest_frame top_frame
  in
   SOME (funn, el 1 $ fst $ dest_list stmt_stack)
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
   then apply $ dest_stmt_app stmt'
   else no_branch
  end
 | NONE => no_branch
;

(* TODO: Get rid of term parsing *)
val b_func_map_entry_ty = “:(string # stmt # (string # d) list)”;

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
  | NONE => (func_map, mk_list ([], b_func_map_entry_ty), ext_fun_map)
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
(* DEBUG
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

(* TODO: Not sure if opening wordsSyntax and fixing the below causes some weirdness *)
(*
(* RESTR_EVAL_RULE constants: *)
val p4_stop_eval_consts_unary =
 [(* “word_1comp”, (* Should be OK? ¬v2w [x; F; T] = v2w [¬x; T; F] *) *)
  word_2comp_tm
 ];
val p4_stop_eval_consts_binary =
 [word_mul_tm,
  word_div_tm,
  word_mod_tm,
  word_add_tm,
  saturate_add_tm,
  word_sub_tm,
  saturate_sub_tm,
  word_lsl_bv_tm, (* TODO: OK to evaluate if second operand has no free variables *)
  word_lsr_bv_tm, (* TODO: OK to evaluate if second operand has no free variables *)
  (* “word_and”, (* Should be OK? w2v (v2w [x; F; T] && v2w [y; F; T]) = [x ∧ y; F; T] *) *)
  (* “word_xor”, (* Should be OK? w2v (v2w [x; F; T] ⊕ v2w [y; F; T]) = [x ⇎ y; F; F] *) *)
  (* “word_or”, (* Should be OK? w2v (v2w [x; F; T] ‖ v2w [y; F; T]) = [x ∨ y; F; T] *) *)
  word_ls_tm,
  word_hs_tm,
  word_lo_tm,
  word_hi_tm
];
*)

(* RESTR_EVAL_RULE constants: *)
val p4_stop_eval_consts_unary =
 [(* “word_1comp”, (* Should be OK? ¬v2w [x; F; T] = v2w [¬x; T; F] *) *)
  “word_2comp”
 ];
val p4_stop_eval_consts_binary =
 [“word_mul”,
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

val p4_stop_eval_consts = p4_stop_eval_consts_unary@p4_stop_eval_consts_binary;

(* TODO: Move *)
fun dest_v_struct_fields strct =
 (map (snd o dest_pair)) $ fst $ dest_list $ dest_v_struct strct
;

(* This simplifies a key until only the match_all application can be reduced next *)
val key_conv = rhs o concl o (SIMP_CONV std_ss [listTheory.MAP, optionTheory.THE_DEF, BETA_THM, listTheory.ZIP, v_of_e_def]);


(* TODO: Fix code duplication *)
fun get_fv_arg_of_tau tau fv_index =
 if is_tau_bool tau
 then (mk_e_v $ mk_v_bool $ mk_var (p4_symb_arg_prefix^(Int.toString fv_index), bool),
       fv_index + 1)
 else if is_tau_bit tau
 then
  let
   val width = dest_tau_bit tau
  in
   (mk_e_v $ mk_v_bit (mk_pair (fixedwidth_freevars_fromindex (p4_symb_arg_prefix, fv_index, width), term_of_int width)), fv_index + width)
  end
 else if is_tau_xtl tau
 then
  let
   val (struct_ty_tm, x_tau'_l) = (fn (a,b) => (a, map dest_pair $ fst $ dest_list b)) $ dest_tau_xtl tau
  in
   if is_struct_ty_struct struct_ty_tm
   then
    let
     val (x_v_l', new_fv_index) = foldl (fn (x_tau', (x_v_list, fv_index')) => ((fn (v', fv_index'') => ((fst x_tau', v')::x_v_list, fv_index'')) (get_fv_arg_of_tau (snd x_tau') fv_index'))) ([],fv_index) x_tau'_l
    in
     (mk_e_v $ mk_v_struct_list x_v_l', new_fv_index)
    end
   else if is_struct_ty_header struct_ty_tm
   then
    let
     val (x_v_l', new_fv_index) = foldl (fn (x_tau', (x_v_list, fv_index')) => ((fn (v', fv_index'') => ((fst x_tau', v')::x_v_list, fv_index'')) (get_fv_arg_of_tau (snd x_tau') fv_index'))) ([],fv_index+1) x_tau'_l
    in
     (mk_e_v $ mk_v_header_list (mk_v_bool $ mk_var (p4_symb_arg_prefix^(Int.toString fv_index), bool)) x_v_l', new_fv_index)
    end
   else raise (ERR "get_fv_arg_of_tau" ("Unsupported struct_ty subtype: "^(term_to_string struct_ty_tm)))
  end
 else raise (ERR "get_fv_arg_of_tau" ("Unsupported tau subtype: "^(term_to_string tau)))
;

fun get_fv_args fv_index ftys =
 let
  val (args, fv_index') = (fn (a, b) => (mk_list(a,e_ty),b)) (foldl (fn (argty, (args, fv_index')) => ((fn (arg', fv_index'') => (arg'::args, fv_index'')) (get_fv_arg_of_tau argty fv_index'))) ([],fv_index) ftys)
 in
  (args, fv_index')
 end
;

(* TODO: Move *)
val (alookup_tm,  mk_alookup, dest_alookup, is_alookup) =
  syntax_fns2 "alist" "ALOOKUP";

fun get_freevars_call (fty_map,b_fty_map) funn block_name fv_index =
 let
  val b_fty_map_lookup_opt = rhs $ concl $ EVAL $ mk_alookup (b_fty_map, block_name)
  (* TODO: b_fty_map_lookup *)
 in
  if is_some b_fty_map_lookup_opt
  then
   let
    val local_fty_map = dest_some b_fty_map_lookup_opt
    val local_fty_map_lookup_opt = rhs $ concl $ EVAL $ mk_alookup (local_fty_map, funn)
   in
    if is_some local_fty_map_lookup_opt
    then
     let
      val ftys = fst $ dest_list $ fst $ dest_pair $ dest_some local_fty_map_lookup_opt
     in
      get_fv_args fv_index ftys
     end
    else
     let
      val fty_map_lookup_opt = rhs $ concl $ EVAL $ mk_alookup (fty_map, funn)
     in
      if is_some fty_map_lookup_opt
      then
       let
	val ftys = fst $ dest_list $ fst $ dest_pair $ dest_some fty_map_lookup_opt
       in
	get_fv_args fv_index ftys
       end
      else raise (ERR "get_freevars_call" ("Function not found in any function map: "^(term_to_string funn)))
     end
   end
  else raise (ERR "get_freevars_call" ("Block not found in blftymap: "^(term_to_string block_name)))
 end
;

(* Function that decides whether to branch or not: returns NONE if no branch should
 * be performed, otherwise SOME of a list of cases and a theorem stating the disjunction
 * between them *)
(* TODO: (fty_map, b_fty_map) and const_actions_tables only needed for apply statement *)
fun p4_should_branch (fty_map, b_fty_map, pblock_action_names_map) const_actions_tables (debug_flag, ctx_def) (fv_index, step_thm) =
 let
  (* DEBUG *)
  val time_start = Time.now();

  (* DEBUG *)
  val _ = dbg_print debug_flag (String.concat ["\nComputing whether symbolic branch should take place...\n"])

  val (path_tm, astate) = the_final_state_hyp_imp step_thm

  val res =
   (case astate_get_branch_data astate of
    (* Branch point: conditional statement *)
    conditional branch_cond =>
   if is_e_v branch_cond andalso not $ null $ free_vars branch_cond
   then
    let
     val branch_cond' = dest_v_bool $ dest_e_v branch_cond
    in
     SOME (SPEC branch_cond' disj_list_EXCLUDED_MIDDLE, [fv_index, fv_index])
    end
   else NONE
    (* Branch point: select expression (in transition statement) *)
    (* TODO: For value sets, this needs to be generalised slightly, similar to the apply case *)
  | select (e, keys, def) =>
    if is_e_v e andalso not $ null $ free_vars e
    then
     if is_v_struct $ dest_e_v e
     then
      let
       val struct_list = dest_v_struct_fields $ dest_e_v e
       (* TODO: Use syntax function for match_all *)
       val key_branch_conds = map (fn key => key_conv (mk_match_all (mk_zip (mk_list(struct_list, v_ty), mk_fst key)))) keys
       val key_branch_conds_neg = map mk_neg $ rev key_branch_conds

       val key_branch_conds' = snd $ foldl (fn (a,(b,c)) => (if null b then b else tl b , (if length b = 1 then a else mk_conj ((list_mk_conj (tl b)), a))::c) ) (key_branch_conds_neg, []) (rev key_branch_conds)

       (* 4. Construct default branch case: i.e., neither of the above hold *)
       val def_branch_cond = list_mk_conj key_branch_conds_neg
       (* Check is default case is even possible to reach *)
       val def_branch_cond_thm = SIMP_CONV bool_ss [match_all_def, match_def, p4Theory.s_case_def, pairTheory.CLOSED_PAIR_EQ, p4Theory.v_11, listTheory.CONS_11, satTheory.AND_INV] def_branch_cond

       (* 5. Construct disjunction theorem, which now is not a strict disjunction *)
       (* TODO: OPTIMIZE: Prove this nchotomy theorem using a template theorem and simple
	* specialisation or rewrites, and not in-place with tactics *)
       val (disj_thm, fv_indices) =
        if Feq $ snd $ dest_eq $ concl def_branch_cond_thm
        then
         (prove(mk_disj_list (key_branch_conds'), REWRITE_TAC [disj_list_def] >> metis_tac[def_branch_cond_thm]),
          List.tabulate (length key_branch_conds', fn n => fv_index))
        else
         (prove(mk_disj_list (key_branch_conds'@[def_branch_cond]), REWRITE_TAC [disj_list_def] >> metis_tac[]),
          List.tabulate ((length key_branch_conds') + 1, fn n => fv_index))
       in
        SOME (disj_thm, fv_indices)
       end
(* OLD
      else if is_v_bit sel_val
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
*)
     else raise (ERR "p4_should_branch" ("Unsupported select value type: "^(term_to_string e)))
    else NONE
    (* Branch point: table application *)
  | apply (tbl_name, e) =>
(*
val apply (tbl_name, e) = apply (“"t2"”, “[e_v (v_bit ([e1; e2; e3; e4; e5; e6; e7; T],8))]”);
*)
    if (hurdUtils.forall is_e_v) (fst $ dest_list e) andalso not $ null $ free_vars e
    then
     let
      (* 1. Extract ctrl from ascope *)
      val ctrl = #4 $ dest_ascope $ #4 $ dest_aenv $ #1 $ dest_astate astate
      (* 2. Extract key sets from ascope using tbl_name *)
      val tbl_opt = rhs $ concl $ EVAL $ mk_alookup (ctrl, tbl_name)
     in
      if is_some tbl_opt
      then
       if exists (fn el => term_eq el tbl_name) const_actions_tables
       then
       (* Old version is really only sound for tables with const entries. *)
	let
	 val tbl = dest_some tbl_opt
	 (* 3. Construct different branch cases for all the key sets
	  *    N.B.: Can now be logically overlapping! *)
	 (* The branch cases for equality with the different table entry keys *)
	 (* TODO: Ensure this obtains the entries in correct order - here be dragons in case of
	  * funny priorities in the table *)

         val keys = fst $ dest_list $ rhs $ concl $ EVAL “MAP FST $ MAP FST ^tbl”
(* TODO: For some reason, changing the line above to the one below causes infinite looping...
	 val keys = fst $ dest_list $ rhs $ concl $ EVAL “MAP FST $ (^(mk_map (fst_tm, tbl)))”
*)
	 val key_branch_conds = map (fn key => key_conv $ mk_comb (key, e)) keys
	 val key_branch_conds_neg = map mk_neg $ rev key_branch_conds

	 val key_branch_conds' = snd $ foldl (fn (a,(b,c)) => (if null b then b else tl b , (if length b = 1 then a else mk_conj ((list_mk_conj (tl b)), a))::c) ) (key_branch_conds_neg, []) (rev key_branch_conds)


	 (* 4. Construct default branch case: i.e., neither of the above hold *)
	 val def_branch_cond = list_mk_conj key_branch_conds_neg
	 (* 5. Construct disjunction theorem, which now is not a strict disjunction *)
	  (* TODO: OPTIMIZE: Prove this nchotomy theorem using a template theorem and simple
	   * specialisation or rewrites, and not in-place with tactics *)
	 val disj_thm = prove(mk_disj_list (key_branch_conds'@[def_branch_cond]), REWRITE_TAC [disj_list_def] >> metis_tac[])
         val fv_indices = List.tabulate ((length key_branch_conds') + 1, fn n => fv_index)

	in
	 SOME (disj_thm, fv_indices)
	end
      else
       (* Table with unknown entries *)
       let
	val tbl = dest_some tbl_opt

        val i = #1 $ dest_aenv $ #1 $ dest_astate astate
        (* TODO: Unify with the syntactic function obtaining the state above? *)
        val (ab_list, pblock_map, _, _, _, _, _, _, _, _) = dest_actx $ rhs $ concl ctx_def
        val (curr_block, _) = dest_arch_block_pbl $ rhs $ concl $ EVAL $ mk_el (i, ab_list)

        (* TODO: All of the information extracted from the ctx below could be
         * pre-computed *)

        (* TODO: handle Exceptions if result is not SOME *)
        val tbl_map = #6 $ dest_pblock $ dest_some $ rhs $ concl $ EVAL $ mk_alookup (pblock_map, curr_block)
        val action_names_map = dest_some $ rhs $ concl $ EVAL $ mk_alookup (pblock_action_names_map, curr_block)
        val action_names = dest_some $ rhs $ concl $ EVAL $ mk_alookup (action_names_map, tbl_name)
        val default_action = snd $ dest_pair $ dest_some $ rhs $ concl $ EVAL $ mk_alookup (tbl_map, tbl_name)
        val (default_action_name, default_action_args) = dest_pair default_action
        (* NOTE: We shouldn't filter out the default action name here - it will have
         * different "hit" dummy arg if it resulted from a hit or a default case. *)

        (* TODO: Depending on control plane API, this should use FOLDL_MATCH_alt instead
         * depending on the match kinds involved *)
	val case_lhs = “FST $ FOLDL_MATCH_alt ^e (^default_action, NONE) (1:num) ^tbl”

        (* TODO: This map should be a foldl, so that the same free variables don't appear in
         * different disjuncts *)
(*
        val (disj_tms, fv_indices) = unzip $ map (fn action_name =>
         let
	  val (action_args, fv_index') = get_freevars_call (fty_map,b_fty_map) “funn_name ^action_name” curr_block fv_index
	  val action_args' = rhs $ concl $ EVAL (mk_append (“[e_v (v_bool T); e_v (v_bool T)]”, (action_args)))
	  val action = mk_pair (action_name, action_args')
	  val res_case = list_mk_exists (rev $ free_vars action_args, mk_eq (case_lhs, action))
         in
          (res_case, fv_index')
         end) (fst $ dest_list action_names)
*)
        val (fv_index''', disj_tms) = foldl (fn (action_name, (fv_index', res_list)) =>
         let
	  val (action_args, fv_index'') = get_freevars_call (fty_map,b_fty_map) “funn_name ^action_name” curr_block fv_index'
	  val action_args' = rhs $ concl $ EVAL (mk_append (“[e_v (v_bool T); e_v (v_bool T)]”, action_args))
	  val action = mk_pair (action_name, action_args')
	  val res_case = list_mk_exists (free_vars_lr action_args, mk_eq (case_lhs, action))
         in
          (fv_index'', (res_case::res_list))
         end) (fv_index, []) (fst $ dest_list action_names)
        (* Reverse order of disj_tms to get free variables in order of increasing index *)
        val disj_tms' = rev disj_tms
        val fv_indices = (replicate (fv_index''', length disj_tms'))

        val fv_indices' = fv_indices@[fv_index]
        val disj_tms'' = disj_tms'@[mk_eq (case_lhs, default_action)]

(*
Problem: existential quantifier needs to enclose the entire disjunct in disj_thm...

But observe that f.ex.:

prove(“((?b. (f = SOME b)) ==> ((if IS_SOME f then stmt1 else stmt2) = stmt1)) <=>
       (!b. ((f = SOME b)) ==> ((if IS_SOME f then stmt1 else stmt2) = stmt1))”,
rw[] >>
fs[]
);

*)

(* TODO: How to use ctrl_is_well_formed here:

val (ftymap, blftymap) = preprocess_ftymaps (symb_exec6_ftymap, symb_exec6_blftymap) 

val (_, pblock_map, _, _, _, _, _, apply_table_f, _, _)= dest_actx $ snd $ dest_eq $ concl $ ctx_def;

val pre_ascope =  #1 $ dest_astate init_astate
val ascope =  #4 $ dest_ascope pre_ascope

val wf_assumption = prove(“ctrl_is_well_formed (^ftymap, ^blftymap) (^pblock_map:pblock_map, ^apply_table_f) (^ascope)”, cheat);

prove(“FST
        (FOLDL_MATCH_alt [e_v (v_bit ([e1; e2; e3; e4; e5; e6; e7; T],8))]
           (("NoAction",[e_v (v_bool T); e_v (v_bool F)]),NONE) 1 t2_ctrl) =
      ("NoAction",[e_v (v_bool T); e_v (v_bool T)]) \/
      (?a0 a1 a2 a3 a4 a5 a6 a7.
        FST
          (FOLDL_MATCH_alt [e_v (v_bit ([e1; e2; e3; e4; e5; e6; e7; T],8))]
             (("NoAction",[e_v (v_bool T); e_v (v_bool F)]),NONE) 1 t2_ctrl) =
        ("set_l",
         [e_v (v_bool T); e_v (v_bool T);
          e_v (v_bit ([a0; a1; a2; a3; a4; a5; a6; a7],8))])) \/
      FST
        (FOLDL_MATCH_alt [e_v (v_bit ([e1; e2; e3; e4; e5; e6; e7; T],8))]
           (("NoAction",[e_v (v_bool T); e_v (v_bool F)]),NONE) 1 t2_ctrl) =
      ("NoAction",[e_v (v_bool T); e_v (v_bool F)])”,

ASSUME_TAC wf_assumption >>
fs[ctrl_is_well_formed_def] >>
PAT_X_ASSUM “_” (fn thm => ASSUME_TAC $ SPECL [“"ingress"”] thm) >>
fs[] >>
PAT_X_ASSUM “_” (fn thm => ASSUME_TAC $ SPECL [“"t2"”] thm) >>
fs[] >>
PAT_X_ASSUM “_” (fn thm => ASSUME_TAC $ SPECL [“[e_v (v_bit ([e1; e2; e3; e4; e5; e6; e7; T],8))]”] thm) >>
(* TODO: Need arch for this... *)
fs[p4_v1modelTheory.v1model_apply_table_f_def]
);

(* Sanity check: *)
prove(“F”,

ASSUME_TAC wf_assumption >>
fs[ctrl_is_well_formed_def] >>
PAT_X_ASSUM “_” (fn thm => ASSUME_TAC $ SPECL [“"ingress"”] thm) >>
fs[] >>
PAT_X_ASSUM “_” (fn thm => ASSUME_TAC $ SPECL [“"t2"”] thm) >>
fs[] >>
PAT_X_ASSUM “_” (fn thm => ASSUME_TAC $ SPECL [“[e_v (v_bit ([e1; e2; e3; e4; e5; e6; e7; T],8))]”] thm) >>
fs[p4_v1modelTheory.v1model_apply_table_f_def]
(* Proof should not work *)
);

*)

        (* TODO: Fix cheat... *)
        val disj_thm = prove (mk_disj_list disj_tms'', cheat)

       in
	SOME (disj_thm, fv_indices')
       end
      else raise (ERR "p4_should_branch" ("Table not found in ctrl: "^(term_to_string tbl_name)))
     end
    else NONE
  | no_branch => NONE)

  val _ = dbg_print debug_flag (String.concat ["\nFinished symbolic branch decision computations in ",
				(LargeInt.toString $ Time.toMilliseconds ((Time.now()) - time_start)),
				" ms\n"])
 in
  res
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

fun p4_regular_step_get_err_msg step_thm =
 let
  (* Get number of steps *)
  val (assl, exec_thm) = dest_imp $ concl step_thm
  val (exec_tm, res_opt) = dest_eq exec_thm
  val (_, _, nsteps) = dest_arch_multi_exec exec_tm
(* DEBUG: *)
  val _ = print "\n\nstep_thm prior to failure:\n";
  val _ = print $ term_to_string $ concl step_thm;
  val _ = print "\n\n";
(*
  val next_state_str =
   if is_some res_opt
   then (term_to_string $ dest_some res_opt)
   else "NONE"
*)
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

(* TODO: Fix naming for the three below, remove unnecessary abstraction *)
(* This is just evaluating a term and adding an assumption, without rewriting *)
fun norewr_eval_ctxt_gen stop_consts ctxt tm =
  RESTR_EVAL_CONV stop_consts tm
  |> PROVE_HYP ctxt
  |> DISCH_CONJUNCTS_ALL
;
fun p4_norewr_eval_ctxt_gen (stop_consts, mk_exec) path_cond astate =
 norewr_eval_ctxt_gen stop_consts path_cond (mk_exec astate)
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
fun dbg_print_stmt_red (func_map, b_func_map, ext_fun_map) stmt status =
 if is_stmt_empty stmt
 then
  if is_status_running status
  then print (String.concat ["\nReducing empty statement...\n\n"])
  else if is_status_trans status
  then print (String.concat ["\nReducing parser state transition...\n\n"])
  else raise (ERR "dbg_print_stmt_red" ("Unsupported status for empty statement: "^(term_to_string status)))
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
   dbg_print_stmt_red (func_map, b_func_map, ext_fun_map) stmt' status
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
      true => print (String.concat ["\nReducing apply statement...\n\n"])
    | false => ())
  end
 else if is_stmt_ext stmt
 then print (String.concat ["\nReducing extern statement...\n\n"])
 else raise (ERR "dbg_print_stmt_red" ("Unsupported statement: "^(term_to_string stmt)))
;

fun p4_funn_name_not_in_func_map funn func_map =
 if is_funn_name funn
 then
  let
   val fname = dest_funn_name funn
  in
   (* TODO: Do this on SML level *)
   optionSyntax.is_none $ rhs $ concl $ EVAL $ mk_alookup (func_map, fname)
  end
 else false
;

datatype e_shortcut_data =
   e_shortcut
 (* term is the expression which could not be shortcut *)
 | e_no_shortcut of term
 | e_fully_reduced;

(* TODO: Actually, both this and the bigstep semantics should be able
 * to look inside expressions that are not shortcuttable *)
fun p4_e_is_shortcuttable e =
 (* Shortcuttable expressions *)
 if is_e_var e
 then e_shortcut
 else if is_e_acc e
 then
  (case p4_e_is_shortcuttable $ fst $ dest_e_acc e of
     e_no_shortcut e' => e_no_shortcut e'
   | _ => e_shortcut)
 else if is_e_cast e
 then
  (case p4_e_is_shortcuttable $ snd $ dest_e_cast e of
     e_no_shortcut e' => e_no_shortcut e'
   | _ => e_shortcut)
 else if is_e_unop e
 then
  (case p4_e_is_shortcuttable $ snd $ dest_e_unop e of
     e_no_shortcut e' => e_no_shortcut e'
   | _ => e_shortcut)
 else if is_e_binop e
 then
  (case p4_e_is_shortcuttable $ #2 $ dest_e_binop e of
     e_no_shortcut e' => e_no_shortcut e'
   | e_shortcut => e_shortcut
   | e_fully_reduced =>
    (case p4_e_is_shortcuttable $ #3 $ dest_e_binop e of
       e_no_shortcut e' => e_no_shortcut e'
     | e_shortcut => e_shortcut
     | e_fully_reduced => e_shortcut))
 (* TODO: Fix concat and slicing *)
 else if is_e_concat e
 then p4_e_is_shortcuttable $ fst $ dest_e_concat e
 else if is_e_slice e
 then p4_e_is_shortcuttable $ #1 $ dest_e_slice e
 (* Expressions with shortcuttable subexpressions *)
(* TODO: Requires keeping track of argument direction in big-step semantics
 else if is_e_call e
 then p4_e_l_is_shortcuttable $ fst $ dest_list $ snd $ dest_e_call e
*)
 else if is_e_struct e
 then
  (case p4_e_l_is_shortcuttable $ ((map (snd o dest_pair)) o fst o dest_list) $ dest_e_struct e of
     e_no_shortcut e' => e_no_shortcut e'
   | _ => e_shortcut)
 else if is_e_header e
 then
  (case p4_e_l_is_shortcuttable $ ((map (snd o dest_pair)) o fst o dest_list) $ snd $ dest_e_header e of
     e_no_shortcut e' => e_no_shortcut e'
   | _ => e_shortcut)
 else if is_e_select e
 then p4_e_is_shortcuttable $ #1 $ dest_e_select e
 else if is_e_v e
 then e_fully_reduced
 else (e_no_shortcut e)
and p4_e_l_is_shortcuttable (h::t) =
 if is_e_v h
 then p4_e_l_is_shortcuttable t
 else p4_e_is_shortcuttable h
  | p4_e_l_is_shortcuttable [] = e_fully_reduced
;

datatype stmt_shortcut_data =
   stmt_shortcut
 (* term is the expression which could not be shortcut *)
 | stmt_no_shortcut_e of term
 (* term is the statement which could not be shortcut *)
 | stmt_no_shortcut_stmt of term;

(* Base cases for p4_is_shortcuttable *)
fun p4_is_shortcuttable' stmt =
 if is_stmt_ass stmt
 then
  (case p4_e_is_shortcuttable $ snd $ dest_stmt_ass stmt of
     e_no_shortcut e => stmt_no_shortcut_e e
   | _ => stmt_shortcut)
 else if is_stmt_ret stmt
 then
  (case p4_e_is_shortcuttable $ dest_stmt_ret stmt of
     e_no_shortcut e => stmt_no_shortcut_e e
   | e_fully_reduced => stmt_no_shortcut_stmt stmt
   | _ => stmt_shortcut)
 else if is_stmt_trans stmt
 then
  (case p4_e_is_shortcuttable $ dest_stmt_trans stmt of
     e_no_shortcut e => stmt_no_shortcut_e e
   | e_fully_reduced => stmt_no_shortcut_stmt stmt
   | _ => stmt_shortcut)
 else if is_stmt_app stmt
 then
  (case p4_e_l_is_shortcuttable $ (fst o dest_list) $ snd $ dest_stmt_app stmt of
     e_no_shortcut e => stmt_no_shortcut_e e
   | e_fully_reduced => stmt_no_shortcut_stmt stmt
   | _ => stmt_shortcut)
 else if is_stmt_cond stmt
 then
  (case p4_e_is_shortcuttable $ #1 $ dest_stmt_cond stmt of
     e_no_shortcut e => stmt_no_shortcut_e e
   | e_fully_reduced => stmt_no_shortcut_stmt stmt
   | _ => stmt_shortcut)
 else stmt_no_shortcut_stmt stmt
;

datatype shortcut_result =
   res_shortcut
 | res_f_args_shortcut
 | res_nonlocal
 | res_no_shortcut_arch
 | res_no_shortcut_stmt of term
 | res_no_shortcut_e of term;

fun shortcut_result_eq sh1 sh2 =
 case sh1 of
   res_shortcut =>
  (case sh2 of
     res_shortcut => true
   | _ => false)
 | res_f_args_shortcut =>
  (case sh2 of
     res_f_args_shortcut => true
   | _ => false)
 | res_nonlocal =>
  (case sh2 of
     res_nonlocal => true
   | _ => false)
 | res_no_shortcut_arch =>
  (case sh2 of
     res_no_shortcut_arch => true
   | _ => false)
 | res_no_shortcut_stmt tm =>
  (case sh2 of
     res_no_shortcut_stmt tm' => term_eq tm tm'
   | _ => false)
 | res_no_shortcut_e tm =>
  (case sh2 of
     res_no_shortcut_e tm' => term_eq tm tm'
   | _ => false)
;

fun get_shortcut_result stmt_shortcut_data =
 case stmt_shortcut_data of
   stmt_shortcut => res_shortcut
 | stmt_no_shortcut_e e => res_no_shortcut_e e
 | stmt_no_shortcut_stmt stmt => res_no_shortcut_stmt stmt
;

fun get_next_stmt stmt =
 if is_stmt_seq stmt
 then
  let
   val stmt' = fst $ dest_stmt_seq stmt
  in
   get_next_stmt stmt'
  end
 else stmt
;

(* TODO: This leaves open the possibility of nested stmt_seq, but the import tool should
 * not enable that - throw exception if this is found to be the case? *)
fun p4_is_shortcuttable (funn, stmt) func_map =
 if p4_funn_name_not_in_func_map funn func_map
 then
  if is_stmt_seq stmt
  then
   let
    val stmt' = get_next_stmt stmt
   in
    if is_stmt_empty stmt'
    then res_shortcut
    else get_shortcut_result $ p4_is_shortcuttable' stmt'
   end
(* Do not allow to shortcut just stmt_empty, since this can lead to status changes
*)
  else get_shortcut_result $ p4_is_shortcuttable' stmt
 else res_nonlocal
;

fun contains_e_call e =
 if is_e_var e
 then false
 else if is_e_acc e
 then
  contains_e_call $ fst $ dest_e_acc e
 else if is_e_cast e
 then
  contains_e_call $ snd $ dest_e_cast e
 else if is_e_unop e
 then
  contains_e_call $ snd $ dest_e_unop e
 else if is_e_binop e
 then
  if contains_e_call $ #2 $ dest_e_binop e
  then true
  else contains_e_call $ #3 $ dest_e_binop e
 (* TODO: Fix concat and slicing *)
 else if is_e_concat e
 then contains_e_call $ fst $ dest_e_concat e
 else if is_e_slice e
 then contains_e_call $ #1 $ dest_e_slice e
 else if is_e_call e
 then true
 else if is_e_struct e
 then contains_e_call_list $ ((map (snd o dest_pair)) o fst o dest_list) $ dest_e_struct e
 else if is_e_header e
 then contains_e_call_list $ ((map (snd o dest_pair)) o fst o dest_list) $ snd $ dest_e_header e
 else if is_e_select e
 then contains_e_call $ #1 $ dest_e_select e
 else if is_e_v e
 then false
 else false
and contains_e_call_list (h::t) =
 if contains_e_call h
 then true
 else contains_e_call_list t
  | contains_e_call_list [] = false
;

(* Is function argument reduction shortcuttable? *)
fun p4_is_f_arg_shortcuttable (func_map, b_func_map, ext_fun_map) e =
 (* TODO: Currently, nested calls are not handled by the bigstep semantics and must be ruled out here. *)
 if is_e_call e andalso (not $ contains_e_call_list $ fst $ dest_list $ snd $ dest_e_call e)
 then
  (case get_next_subexp (func_map, b_func_map, ext_fun_map) e of
     SOME e' =>
    (case p4_e_is_shortcuttable e' of
       e_no_shortcut e'' => res_no_shortcut_e e''
     | e_fully_reduced => res_no_shortcut_e e'
     | e_shortcut => res_f_args_shortcut)
   | NONE => res_no_shortcut_e e)
 else res_no_shortcut_e e
;

(* TODO: Move *)
val (bigstep_arch_exec_tm,  mk_bigstep_arch_exec, dest_bigstep_arch_exec, is_bigstep_arch_exec) =
  syntax_fns3 "p4_bigstep" "bigstep_arch_exec";
val bigstep_arch_exec_none = optionSyntax.mk_none “:('a actx # b_func_map)”;
val bigstep_arch_exec_none_v1model = optionSyntax.mk_none “:(v1model_ascope actx # b_func_map)”;

val (bigstep_arch_exec'_tm,  mk_bigstep_arch_exec', dest_bigstep_arch_exec', is_bigstep_arch_exec') =
  syntax_fns3 "p4_bigstep" "bigstep_arch_exec'";

(* TODO: Move *)
val (in_local_fun_tm,  mk_in_local_fun, dest_in_local_fun, is_in_local_fun) =
  syntax_fns3 "p4_bigstep" "in_local_fun";

(* TODO: Move *)
val (in_local_fun'_tm,  mk_in_local_fun', dest_in_local_fun', is_in_local_fun') =
  syntax_fns4 "p4_bigstep" "in_local_fun'";

(* TODO: Move *)
(* TODO: This should simplify the scopes after shortcutting *)
local
fun word_conv word =
 if null $ free_vars word
 then EVAL word
 else raise UNCHANGED
;

val word_convs_unary =
 map
 (fn wordop =>
  {conv = K (K word_conv),
   key= SOME ([], mk_comb (wordop, mk_var ("w", wordsSyntax.mk_word_type Type.alpha))),
   (* TODO: Better names *)
   name = term_to_string wordop,
   trace = 2}) p4_stop_eval_consts_unary
;
val word_convs_binary =
 map
 (fn wordop =>
  {conv = K (K word_conv),
   key= SOME ([], mk_comb (mk_comb (wordop, mk_var ("w", wordsSyntax.mk_word_type Type.alpha)), mk_var ("w'", wordsSyntax.mk_word_type Type.alpha))),
   (* TODO: Better names *)
   name = term_to_string wordop,
   trace = 2}) p4_stop_eval_consts_binary
;

in
val p4_wordops_ss =
  SSFRAG {ac = [],
          congs = [],
          convs = word_convs_unary@word_convs_binary,
          dprocs = [],
          filter = NONE,
          name = SOME "p4_wordops_ss",
          rewrs = []};
end;
(*
val (id, path_cond_thm, step_thm) = el 1 path_cond_step_list
*)

fun p4_regular_step (debug_flag, ctx_def, ctx, norewr_eval_ctxt, eval_ctxt) comp_thm use_eval_in_ctxt step_thm =
 let
  (* DEBUG *)
  val time_start = Time.now();

  val (ante, astate, nsteps) = the_final_state_hyp_imp_n step_thm
  (* DEBUG *)
  val _ = dbg_print debug_flag (String.concat ["\nCommencing regular step from state with path condition: ",
				(term_to_string $ ante),
				"\n"])

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

  val (func_map, b_func_map, ext_fun_map) = get_f_maps (astate, ctx)

  val (aenv, g_scope_list, arch_frame_list, status) = dest_astate astate
  val stmt_funn_opt = arch_frame_list_get_top_funn_stmt arch_frame_list
  val shortcut =
   case stmt_funn_opt of
     SOME (funn, stmt) =>
    (* TODO: Temporary hack to restrict application of big-step semantics
     * to control block + block-local functions *)
    if
     (if is_funn_name funn
      then Teq $ rhs $ concl $ EVAL (mk_is_some $ mk_alookup (b_func_map, dest_funn_name funn))
      else false)
    then
     (case p4_is_shortcuttable (funn, stmt) func_map of
	res_shortcut => res_shortcut
      | res_no_shortcut_e e =>
       p4_is_f_arg_shortcuttable (func_map, b_func_map, ext_fun_map) e
      | other => other)
    else res_no_shortcut_arch
   | NONE => res_no_shortcut_arch
  (* DEBUG *)
  val _ =
   if debug_flag
   then
    case stmt_funn_opt of
       NONE => print (String.concat ["\nReducing architectural step...\n\n"])
     | SOME (funn, stmt) => dbg_print_stmt_red (func_map, b_func_map, ext_fun_map) stmt status
   else ()
 in
  (* TODO: If use_eval_in_ctxt, this should never shortcut apply or select statements, which
   * need to use assumptions in the middle of execution. Fix this when you enable shortcutting
   * these *)
  if ((shortcut_result_eq shortcut res_shortcut) orelse (shortcut_result_eq shortcut res_f_args_shortcut))
  then
   (* Take regular shortcut *)
   let

    val block_index = #1 $ dest_aenv aenv

    val (is_local_thm, bigstep_tm) =
     if shortcut_result_eq shortcut res_shortcut
     (* Non-function argument reduction *)
     then (EVAL_RULE $ REWRITE_CONV ([ctx_def, in_local_fun'_def, alistTheory.ALOOKUP_def]) $ mk_in_local_fun' (lhs $ concl ctx_def, block_index, arch_frame_list, nsteps),
           mk_bigstep_arch_exec (mk_none $ mk_prod (type_of ctx, type_of b_func_map), g_scope_list, arch_frame_list))
     (* Function argument reduction *)
     else (EVAL_RULE $ REWRITE_CONV ([ctx_def, in_local_fun'_def, alistTheory.ALOOKUP_def]) $ mk_in_local_fun' (lhs $ concl ctx_def, block_index, arch_frame_list, nsteps),
           mk_bigstep_arch_exec' (mk_some $ mk_pair (aenv, ctx), g_scope_list, arch_frame_list))
    val bigstep_thm = REWRITE_RULE [GSYM ctx_def] $ RESTR_EVAL_CONV p4_stop_eval_consts bigstep_tm

    (* DEBUG *)
    val _ = dbg_print debug_flag (String.concat ["Shortcutting ",
                                  let
                                   val n_tm = el 3 $ pairSyntax.strip_pair $ dest_some $ rhs $ concl bigstep_thm
                                  in
                                   if int_of_term n_tm = 0
                                   then raise (ERR "p4_regular_step" ("Shortcutting zero steps (looping): "^(term_to_string arch_frame_list)))
                                   else term_to_string n_tm
                                  end,
                                  ": ",
				  (LargeInt.toString $ Time.toMilliseconds ((Time.now()) - time_start)),
				  " ms\n"])

    (* DEBUG *)
    val time_start2 = Time.now();

    (* Simplify the word operations that contain no free variables *)
    val bigstep_thm' = SIMP_RULE (empty_ss++p4_wordops_ss) [] bigstep_thm
(*
    val is_local_thm = EQT_ELIM $ EVAL $ mk_in_local_fun (func_map, arch_frame_list)
*)

    (* DEBUG *)
    val _ = dbg_print debug_flag (String.concat ["Simplifying word ops on constants: ",
				  (LargeInt.toString $ Time.toMilliseconds ((Time.now()) - time_start2)),
				  " ms\n"])

    (* DEBUG *)
    val time_start3 = Time.now();

    (* DEBUG *)
    val _ = dbg_print debug_flag (String.concat ["Proving locality of local fun: ",
				  (LargeInt.toString $ Time.toMilliseconds ((Time.now()) - time_start3)),
				  " ms\n"])

    (* DEBUG *)
    val time_start4 = Time.now();

    val shortcut_comp_thm =
     if shortcut_result_eq shortcut res_shortcut
     then bigstep_arch_exec_comp'_NONE
     else bigstep_arch_exec_comp'_SOME
(*
val shortcut_comp_thm = Q.ISPECL [‘2’, ‘2’, ‘T’, ‘^ctx’] shortcut_comp_thm
val shortcut_comp_thm = PURE_REWRITE_RULE [GSYM ctx_def] shortcut_comp_thm

val test = snd $ dest_imp $ concl step_thm
val test_lhs = fst $ dest_eq $ test
val (testfun, [testctx, teststate, testn]) = strip_comb test_lhs
val testty = mk_itself $ type_of testctx;

val shortcut_comp_thm' = INST_TYPE [Type.alpha |-> arch_ty] shortcut_comp_thm
val test2ty = mk_itself $ type_of test2ctx;


MATCH_MP bigstep_arch_exec_comp'_NONE step_thm


val test2 = snd $ dest_imp $ fst $ dest_imp $ concl $ SPEC_ALL shortcut_comp_thm'
val test2_lhs = fst $ dest_eq $ test2
val (test2fun, [test2ctx, test2state, test2n]) = strip_comb test2_lhs

ALPHA testty test2ty;

ALPHA testfun test2fun;

*)
    val res =
     SIMP_RULE simple_arith_ss []
      (MATCH_MP (MATCH_MP (MATCH_MP shortcut_comp_thm (PURE_REWRITE_RULE [GSYM ctx_def] step_thm)) is_local_thm) bigstep_thm')

    (* DEBUG *)
    val _ = dbg_print debug_flag (String.concat ["step_thm composition: ",
				  (LargeInt.toString $ Time.toMilliseconds ((Time.now()) - time_start4)),
				  " ms\n"])

   in
    res
   end
  else
   (* OLD regular step *)
   let
    val step_thm2 =
     if use_eval_in_ctxt
     then eval_ctxt (ASSUME ante) astate
     else norewr_eval_ctxt (ASSUME ante) astate

    (* DEBUG *)
    val _ = dbg_print debug_flag (String.concat [(if use_eval_in_ctxt then "evaluation-in-context: " else "evaluation: "),
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
       val time_start2 = Time.now();

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
				     (LargeInt.toString $ Time.toMilliseconds ((Time.now()) - time_start2)),
				     " ms\n"])

      in
       res
      end
      handle (HOL_ERR exn) =>
       raise (if (is_none $ rhs $ snd $ dest_imp $ concl step_thm2)
	     then (ERR "p4_regular_step" ("Unexpected reduction to NONE from frame list: "^(term_to_string $ #3 $ dest_astate $ the_final_state_imp step_thm)))
	     else (HOL_ERR exn))
  end
 end
 handle (HOL_ERR exn) => raise (ERR "p4_regular_step" (String.concat ["Exception: ", #message exn, " in function ", #origin_function exn, " from structure ", #origin_structure exn, p4_regular_step_get_err_msg step_thm])) (* (wrap_exn "p4_symb_exec" "p4_regular_step" (HOL_ERR exn)) *)
;

(* Function that decides whether a HOL4P4 program is finished or not:
 * here, when processing of all symbolic input packets are finished.
 * Used as a default when no other function is specified. *)
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

fun preprocess_ftymaps (fty_map, b_fty_map) =
 let
  val fty_map_opt = rhs $ concl $ EVAL “deparameterise_ftymap_entries ^fty_map”
  val b_fty_map_opt = rhs $ concl $ EVAL “deparameterise_b_ftymap_entries ^b_fty_map”
 in
  if is_some fty_map_opt
  then
   if is_some b_fty_map_opt
   then (dest_some fty_map_opt, dest_some b_fty_map_opt)
   else raise (ERR "preprocess_ftymaps" "Could not deparameterise block-local function type map.")
  else raise (ERR "preprocess_ftymaps" "Could not deparameterise function type map.")
 end
;

(* The main symbolic execution.
 * Here, the static ctxt and the dynamic path condition have been merged. *)
fun p4_symb_exec nthreads_max debug_flag arch_ty (ctx_def, ctx) (fty_map, b_fty_map, pblock_action_names_map) const_actions_tables init_astate stop_consts_rewr stop_consts_never path_cond p4_is_finished_alt_opt fuel =
 let
  (* Pre-process ftymap and b_fty_map *)
  val (fty_map', b_fty_map') = preprocess_ftymaps (fty_map, b_fty_map)

  (* Pre-process const_actions_tables *)
  val const_actions_tables' = map stringSyntax.fromMLstring const_actions_tables

  val comp_thm = INST_TYPE [Type.alpha |-> arch_ty] arch_multi_exec_comp_n_tl_assl
  val init_step_thm = eval_ctxt_gen (stop_consts_rewr@stop_consts_never) stop_consts_never path_cond (mk_arch_multi_exec (ctx, init_astate, 0))

  val table_stop_consts = [match_all_tm]
  val eval_ctxt = p4_eval_ctxt_gen ((stop_consts_rewr@stop_consts_never@p4_stop_eval_consts@table_stop_consts), (stop_consts_never@p4_stop_eval_consts), (fn astate => mk_arch_multi_exec (ctx, astate, 1)))
  val norewr_eval_ctxt = p4_norewr_eval_ctxt_gen ((stop_consts_rewr@stop_consts_never@p4_stop_eval_consts), (fn astate => mk_arch_multi_exec (ctx, astate, 1)))
  val regular_step = p4_regular_step (debug_flag, ctx_def, ctx, norewr_eval_ctxt, eval_ctxt) comp_thm
  val is_finished =
   if isSome p4_is_finished_alt_opt
   then valOf p4_is_finished_alt_opt
   else p4_is_finished
 in
(* DEBUG:
val lang_regular_step = p4_regular_step (debug_flag, ctx_def, ctx, norewr_eval_ctxt, eval_ctxt) comp_thm;
val lang_init_step_thm = init_step_thm;
val lang_should_branch = p4_should_branch (fty_map', b_fty_map') const_actions_tables' (debug_flag, ctx_def);
val lang_is_finished = is_finished;

val const_actions_tables = const_actions_tables'
val (fty_map, b_fty_map) = (fty_map', b_fty_map')
*)
  if List.exists (fn b => b = true) $ map (String.isPrefix p4_symb_arg_prefix) $ map (fst o dest_var) $ free_vars $ concl init_step_thm
  then raise (ERR "p4_symb_exec" ("Found free variables with the prefix \""^(p4_symb_arg_prefix^"\" in the initial step theorem: this prefix is reserved for use by the symbolic execution.")))
  else
   if nthreads_max > 1
   then
     symb_exec_conc (debug_flag, regular_step, init_step_thm, p4_should_branch (fty_map', b_fty_map', pblock_action_names_map) const_actions_tables' (debug_flag, ctx_def), is_finished) path_cond fuel nthreads_max
   else symb_exec (debug_flag, regular_step, init_step_thm, p4_should_branch (fty_map', b_fty_map', pblock_action_names_map) const_actions_tables' (debug_flag, ctx_def), is_finished) path_cond fuel
 end
  handle (HOL_ERR exn) => raise (wrap_exn "p4_symb_exec" "p4_symb_exec" (HOL_ERR exn))
;

(* TODO: Move to a new syntax file *)
fun dest_quinop c e tm =
   case with_exn strip_comb tm e of
      (t, [t1, t2, t3, t4, t5]) =>
         if same_const t c then (t1, t2, t3, t4, t5) else raise e
    | _ => raise e;
fun list_of_quintuple (a, b, c, d, e) = [a, b, c, d, e];
fun mk_quinop tm = HolKernel.list_mk_icomb tm o list_of_quintuple;
val syntax_fns5 = HolKernel.syntax_fns {n = 5, dest = dest_quinop, make = mk_quinop};
val (p4_contract_list_tm, mk_p4_contract_list, dest_p4_contract_list, is_p4_contract_list) =
 syntax_fns5 "p4_symb_exec" "p4_contract_list";

val (p4_contract_tm, mk_p4_contract, dest_p4_contract, is_p4_contract) =
 syntax_fns4 "p4_symb_exec" "p4_contract";

(*
val path_cond_case_thm_list = (zip path_cond_rest_tm_list (CONJUNCTS path_tree_list_leafs_thm))

length path_cond_case_thm_list
 val path_cond_case = fst $ el 1 path_cond_case_thm_list
 val thm = snd $ el 1 path_cond_case_thm_list

val path_cond_tm =
   “((T ∧
      match_all
        [(v_bit
            ([eth96; eth97; eth98; eth99; eth100; eth101; eth102; eth103;
              eth104; eth105; eth106; eth107; eth108; eth109; eth110; eth111],
             16),
          s_sing
            (v_bit ([F; F; F; F; T; F; F; F; F; F; F; F; F; F; F; F],16)))]) ∧
     match_all
       [(v_bit ([ip72; ip73; ip74; ip75; ip76; ip77; ip78; ip79],8),
         s_sing (v_bit ([F; F; T; T; F; F; T; F],8)))]) ∧
    ∃a288 a289 a290 a291 a292 a293 a294 a295 a296 a297 a298 a299 a300 a301
        a302 a303 a304 a305 a306 a307 a308 a309 a310 a311 a312 a313 a314 a315
        a316 a317 a318 a319 a160 a161 a162 a163 a164 a165 a166 a167 a168 a169
        a170 a171 a172 a173 a174 a175 a176 a177 a178 a179 a180 a181 a182 a183
        a184 a185 a186 a187 a188 a189 a190 a191 a192 a193 a194 a195 a196 a197
        a198 a199 a200 a201 a202 a203 a204 a205 a206 a207 a208 a209 a210 a211
        a212 a213 a214 a215 a216 a217 a218 a219 a220 a221 a222 a223 a224 a225
        a226 a227 a228 a229 a230 a231 a232 a233 a234 a235 a236 a237 a238 a239
        a240 a241 a242 a243 a244 a245 a246 a247 a248 a249 a250 a251 a252 a253
        a254 a255 a256 a257 a258 a259 a260 a261 a262 a263 a264 a265 a266 a267
        a268 a269 a270 a271 a272 a273 a274 a275 a276 a277 a278 a279 a280 a281
        a282 a283 a284 a285 a286 a287 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
        a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28
        a29 a30 a31 a32 a33 a34 a35 a36 a37 a38 a39 a40 a41 a42 a43 a44 a45
        a46 a47 a48 a49 a50 a51 a52 a53 a54 a55 a56 a57 a58 a59 a60 a61 a62
        a63 a64 a65 a66 a67 a68 a69 a70 a71 a72 a73 a74 a75 a76 a77 a78 a79
        a80 a81 a82 a83 a84 a85 a86 a87 a88 a89 a90 a91 a92 a93 a94 a95 a96
        a97 a98 a99 a100 a101 a102 a103 a104 a105 a106 a107 a108 a109 a110
        a111 a112 a113 a114 a115 a116 a117 a118 a119 a120 a121 a122 a123 a124
        a125 a126 a127 a128 a129 a130 a131 a132 a133 a134 a135 a136 a137 a138
        a139 a140 a141 a142 a143 a144 a145 a146 a147 a148 a149 a150 a151 a152
        a153 a154 a155 a156 a157 a158 a159.
      FST
        (FOLDL_MATCH_alt
           [e_v
              (v_bit
                 ([ip96; ip97; ip98; ip99; ip100; ip101; ip102; ip103; ip104;
                   ip105; ip106; ip107; ip108; ip109; ip110; ip111; ip112;
                   ip113; ip114; ip115; ip116; ip117; ip118; ip119; ip120;
                   ip121; ip122; ip123; ip124; ip125; ip126; ip127],32));
            e_v
              (v_bit
                 ([ip128; ip129; ip130; ip131; ip132; ip133; ip134; ip135;
                   ip136; ip137; ip138; ip139; ip140; ip141; ip142; ip143;
                   ip144; ip145; ip146; ip147; ip148; ip149; ip150; ip151;
                   ip152; ip153; ip154; ip155; ip156; ip157; ip158; ip159],32));
            e_v
              (v_bit
                 ([esp0; esp1; esp2; esp3; esp4; esp5; esp6; esp7; esp8;
                   esp9; esp10; esp11; esp12; esp13; esp14; esp15; esp16;
                   esp17; esp18; esp19; esp20; esp21; esp22; esp23; esp24;
                   esp25; esp26; esp27; esp28; esp29; esp30; esp31],32))]
           (("NoAction",[e_v (v_bool T); e_v (v_bool F)]),NONE) 1 []) =
      ("esp_decrypt_aes_ctr",
       [e_v (v_bool T); e_v (v_bool T);
        e_v
          (v_bit
             ([a288; a289; a290; a291; a292; a293; a294; a295; a296; a297;
               a298; a299; a300; a301; a302; a303; a304; a305; a306; a307;
               a308; a309; a310; a311; a312; a313; a314; a315; a316; a317;
               a318; a319],32));
        e_v
          (v_bit
             ([a160; a161; a162; a163; a164; a165; a166; a167; a168; a169;
               a170; a171; a172; a173; a174; a175; a176; a177; a178; a179;
               a180; a181; a182; a183; a184; a185; a186; a187; a188; a189;
               a190; a191; a192; a193; a194; a195; a196; a197; a198; a199;
               a200; a201; a202; a203; a204; a205; a206; a207; a208; a209;
               a210; a211; a212; a213; a214; a215; a216; a217; a218; a219;
               a220; a221; a222; a223; a224; a225; a226; a227; a228; a229;
               a230; a231; a232; a233; a234; a235; a236; a237; a238; a239;
               a240; a241; a242; a243; a244; a245; a246; a247; a248; a249;
               a250; a251; a252; a253; a254; a255; a256; a257; a258; a259;
               a260; a261; a262; a263; a264; a265; a266; a267; a268; a269;
               a270; a271; a272; a273; a274; a275; a276; a277; a278; a279;
               a280; a281; a282; a283; a284; a285; a286; a287],128));
        e_v
          (v_bit
             ([a0; a1; a2; a3; a4; a5; a6; a7; a8; a9; a10; a11; a12; a13;
               a14; a15; a16; a17; a18; a19; a20; a21; a22; a23; a24; a25;
               a26; a27; a28; a29; a30; a31; a32; a33; a34; a35; a36; a37;
               a38; a39; a40; a41; a42; a43; a44; a45; a46; a47; a48; a49;
               a50; a51; a52; a53; a54; a55; a56; a57; a58; a59; a60; a61;
               a62; a63; a64; a65; a66; a67; a68; a69; a70; a71; a72; a73;
               a74; a75; a76; a77; a78; a79; a80; a81; a82; a83; a84; a85;
               a86; a87; a88; a89; a90; a91; a92; a93; a94; a95; a96; a97;
               a98; a99; a100; a101; a102; a103; a104; a105; a106; a107;
               a108; a109; a110; a111; a112; a113; a114; a115; a116; a117;
               a118; a119; a120; a121; a122; a123; a124; a125; a126; a127;
               a128; a129; a130; a131; a132; a133; a134; a135; a136; a137;
               a138; a139; a140; a141; a142; a143; a144; a145; a146; a147;
               a148; a149; a150; a151; a152; a153; a154; a155; a156; a157;
               a158; a159],160))])”: term

val path_cond_case =
   “∃a352 a353 a354 a355 a356 a357 a358 a359 a360.
      FST
        (FOLDL_MATCH_alt
           [e_v
              (v_bit
                 ([ip128; ip129; ip130; ip131; ip132; ip133; ip134; ip135;
                   ip136; ip137; ip138; ip139; ip140; ip141; ip142; ip143;
                   ip144; ip145; ip146; ip147; ip148; ip149; ip150; ip151;
                   ip152; ip153; ip154; ip155; ip156; ip157; ip158; ip159],32))]
           (("drop",[e_v (v_bool T); e_v (v_bool F)]),NONE) 1 []) =
      ("l3_forward",
       [e_v (v_bool T); e_v (v_bool T);
        e_v
          (v_bit ([a352; a353; a354; a355; a356; a357; a358; a359; a360],9))])”;

val thm =
 prove(“p4_contract
       ((((T ∧
           match_all
             [(v_bit
                 ([eth96; eth97; eth98; eth99; eth100; eth101; eth102;
                   eth103; eth104; eth105; eth106; eth107; eth108; eth109;
                   eth110; eth111],16),
               s_sing
                 (v_bit ([F; F; F; F; T; F; F; F; F; F; F; F; F; F; F; F],16)))]) ∧
          match_all
            [(v_bit ([ip72; ip73; ip74; ip75; ip76; ip77; ip78; ip79],8),
              s_sing (v_bit ([F; F; T; T; F; F; T; F],8)))]) ∧
         FST
           (FOLDL_MATCH_alt
              [e_v
                 (v_bit
                    ([ip96; ip97; ip98; ip99; ip100; ip101; ip102; ip103;
                      ip104; ip105; ip106; ip107; ip108; ip109; ip110; ip111;
                      ip112; ip113; ip114; ip115; ip116; ip117; ip118; ip119;
                      ip120; ip121; ip122; ip123; ip124; ip125; ip126; ip127],
                     32));
               e_v
                 (v_bit
                    ([ip128; ip129; ip130; ip131; ip132; ip133; ip134; ip135;
                      ip136; ip137; ip138; ip139; ip140; ip141; ip142; ip143;
                      ip144; ip145; ip146; ip147; ip148; ip149; ip150; ip151;
                      ip152; ip153; ip154; ip155; ip156; ip157; ip158; ip159],
                     32));
               e_v
                 (v_bit
                    ([esp0; esp1; esp2; esp3; esp4; esp5; esp6; esp7; esp8;
                      esp9; esp10; esp11; esp12; esp13; esp14; esp15; esp16;
                      esp17; esp18; esp19; esp20; esp21; esp22; esp23; esp24;
                      esp25; esp26; esp27; esp28; esp29; esp30; esp31],32))]
              (("NoAction",[e_v (v_bool T); e_v (v_bool F)]),NONE) 1 []) =
         ("esp_decrypt_aes_ctr",
          [e_v (v_bool T); e_v (v_bool T);
           e_v
             (v_bit
                ([a288; a289; a290; a291; a292; a293; a294; a295; a296; a297;
                  a298; a299; a300; a301; a302; a303; a304; a305; a306; a307;
                  a308; a309; a310; a311; a312; a313; a314; a315; a316; a317;
                  a318; a319],32));
           e_v
             (v_bit
                ([a160; a161; a162; a163; a164; a165; a166; a167; a168; a169;
                  a170; a171; a172; a173; a174; a175; a176; a177; a178; a179;
                  a180; a181; a182; a183; a184; a185; a186; a187; a188; a189;
                  a190; a191; a192; a193; a194; a195; a196; a197; a198; a199;
                  a200; a201; a202; a203; a204; a205; a206; a207; a208; a209;
                  a210; a211; a212; a213; a214; a215; a216; a217; a218; a219;
                  a220; a221; a222; a223; a224; a225; a226; a227; a228; a229;
                  a230; a231; a232; a233; a234; a235; a236; a237; a238; a239;
                  a240; a241; a242; a243; a244; a245; a246; a247; a248; a249;
                  a250; a251; a252; a253; a254; a255; a256; a257; a258; a259;
                  a260; a261; a262; a263; a264; a265; a266; a267; a268; a269;
                  a270; a271; a272; a273; a274; a275; a276; a277; a278; a279;
                  a280; a281; a282; a283; a284; a285; a286; a287],128));
           e_v
             (v_bit
                ([a0; a1; a2; a3; a4; a5; a6; a7; a8; a9; a10; a11; a12; a13;
                  a14; a15; a16; a17; a18; a19; a20; a21; a22; a23; a24; a25;
                  a26; a27; a28; a29; a30; a31; a32; a33; a34; a35; a36; a37;
                  a38; a39; a40; a41; a42; a43; a44; a45; a46; a47; a48; a49;
                  a50; a51; a52; a53; a54; a55; a56; a57; a58; a59; a60; a61;
                  a62; a63; a64; a65; a66; a67; a68; a69; a70; a71; a72; a73;
                  a74; a75; a76; a77; a78; a79; a80; a81; a82; a83; a84; a85;
                  a86; a87; a88; a89; a90; a91; a92; a93; a94; a95; a96; a97;
                  a98; a99; a100; a101; a102; a103; a104; a105; a106; a107;
                  a108; a109; a110; a111; a112; a113; a114; a115; a116; a117;
                  a118; a119; a120; a121; a122; a123; a124; a125; a126; a127;
                  a128; a129; a130; a131; a132; a133; a134; a135; a136; a137;
                  a138; a139; a140; a141; a142; a143; a144; a145; a146; a147;
                  a148; a149; a150; a151; a152; a153; a154; a155; a156; a157;
                  a158; a159],160))])) ∧
        FST
          (FOLDL_MATCH_alt
             [e_v
                (v_bit
                   ([ip128; ip129; ip130; ip131; ip132; ip133; ip134; ip135;
                     ip136; ip137; ip138; ip139; ip140; ip141; ip142; ip143;
                     ip144; ip145; ip146; ip147; ip148; ip149; ip150; ip151;
                     ip152; ip153; ip154; ip155; ip156; ip157; ip158; ip159],
                    32))] (("drop",[e_v (v_bool T); e_v (v_bool F)]),NONE) 1
             []) =
        ("l3_forward",
         [e_v (v_bool T); e_v (v_bool T);
          e_v
            (v_bit ([a352; a353; a354; a355; a356; a357; a358; a359; a360],9))]))
       ctx
       ((0,
         [([eth0; eth1; eth2; eth3; eth4; eth5; eth6; eth7; eth8; eth9;
            eth10; eth11; eth12; eth13; eth14; eth15; eth16; eth17; eth18;
            eth19; eth20; eth21; eth22; eth23; eth24; eth25; eth26; eth27;
            eth28; eth29; eth30; eth31; eth32; eth33; eth34; eth35; eth36;
            eth37; eth38; eth39; eth40; eth41; eth42; eth43; eth44; eth45;
            eth46; eth47; eth48; eth49; eth50; eth51; eth52; eth53; eth54;
            eth55; eth56; eth57; eth58; eth59; eth60; eth61; eth62; eth63;
            eth64; eth65; eth66; eth67; eth68; eth69; eth70; eth71; eth72;
            eth73; eth74; eth75; eth76; eth77; eth78; eth79; eth80; eth81;
            eth82; eth83; eth84; eth85; eth86; eth87; eth88; eth89; eth90;
            eth91; eth92; eth93; eth94; eth95; eth96; eth97; eth98; eth99;
            eth100; eth101; eth102; eth103; eth104; eth105; eth106; eth107;
            eth108; eth109; eth110; eth111; ip0; ip1; ip2; ip3; ip4; ip5;
            ip6; ip7; ip8; ip9; ip10; ip11; ip12; ip13; ip14; ip15; ip16;
            ip17; ip18; ip19; ip20; ip21; ip22; ip23; ip24; ip25; ip26; ip27;
            ip28; ip29; ip30; ip31; ip32; ip33; ip34; ip35; ip36; ip37; ip38;
            ip39; ip40; ip41; ip42; ip43; ip44; ip45; ip46; ip47; ip48; ip49;
            ip50; ip51; ip52; ip53; ip54; ip55; ip56; ip57; ip58; ip59; ip60;
            ip61; ip62; ip63; ip64; ip65; ip66; ip67; ip68; ip69; ip70; ip71;
            ip72; ip73; ip74; ip75; ip76; ip77; ip78; ip79; ip80; ip81; ip82;
            ip83; ip84; ip85; ip86; ip87; ip88; ip89; ip90; ip91; ip92; ip93;
            ip94; ip95; ip96; ip97; ip98; ip99; ip100; ip101; ip102; ip103;
            ip104; ip105; ip106; ip107; ip108; ip109; ip110; ip111; ip112;
            ip113; ip114; ip115; ip116; ip117; ip118; ip119; ip120; ip121;
            ip122; ip123; ip124; ip125; ip126; ip127; ip128; ip129; ip130;
            ip131; ip132; ip133; ip134; ip135; ip136; ip137; ip138; ip139;
            ip140; ip141; ip142; ip143; ip144; ip145; ip146; ip147; ip148;
            ip149; ip150; ip151; ip152; ip153; ip154; ip155; ip156; ip157;
            ip158; ip159; esp0; esp1; esp2; esp3; esp4; esp5; esp6; esp7;
            esp8; esp9; esp10; esp11; esp12; esp13; esp14; esp15; esp16;
            esp17; esp18; esp19; esp20; esp21; esp22; esp23; esp24; esp25;
            esp26; esp27; esp28; esp29; esp30; esp31; esp32; esp33; esp34;
            esp35; esp36; esp37; esp38; esp39; esp40; esp41; esp42; esp43;
            esp44; esp45; esp46; esp47; esp48; esp49; esp50; esp51; esp52;
            esp53; esp54; esp55; esp56; esp57; esp58; esp59; esp60; esp61;
            esp62; esp63],0)],[],0,[],
         [("parseError",
           v_bit
             ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
               F; F; F; F; F; F; F; F; F; F; F],32))],
         [("spd",[]); ("forward",[]); ("sad_decrypt",[]); ("sad_encrypt",[])]),
        [[(varn_name "gen_apply_result",
           v_struct
             [("hit",v_bool ARB); ("miss",v_bool ARB);
              ("action_run",
               v_bit
                 ([ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
                   ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
                   ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB],32))],
           NONE)]],arch_frame_list_empty,status_running) (λs. T)”, cheat);


*)

fun insert_existentials path_cond_tm (path_cond_case, thm) =
 let
  val (precond, ctx, init_state, postcond) = dest_p4_contract $ concl thm
  val (conjs, conj_last) = dest_conj precond
  val vars = (((filter (fn el => String.isPrefix p4_symb_arg_prefix $ fst $ dest_var el)) o free_vars_lr)) precond
  val precond' = mk_conj (path_cond_tm, path_cond_case)
  val goal_contract = mk_p4_contract (precond', ctx, init_state, postcond)
(*
  val time_start = Time.now();
 *)
(* OLD
  val res =
   prove(“^goal_contract”,
         assume_tac (REWRITE_RULE [p4_contract_def] (GENL vars thm)) >>
	 rewrite_tac [p4_contract_def] >>
         ASM_SIMP_TAC bool_ss [] >>
	 METIS_TAC []);
*)
(* This seems to work, but looks hacky... *)

  val res =
   prove(goal_contract,
         assume_tac (REWRITE_RULE [p4_contract_def] (GENL vars thm)) >>
	 rewrite_tac [p4_contract_def] >>
         TRY (
          rpt disch_tac >>
	  rpt (PAT_X_ASSUM “A /\ B” (fn thm => (STRIP_THM_THEN (fn thm' => ASSUME_TAC thm') thm))) >>
	  rpt (PAT_X_ASSUM “?a. _” (fn thm => (STRIP_THM_THEN (fn thm' => ASSUME_TAC thm') thm))) >>
	  res_tac >>
	  qexists_tac ‘n'’ >-
	  ASM_REWRITE_TAC[]
         ) >>
         ASM_SIMP_TAC bool_ss [] >>
         metis_tac[]);

(*
  (* DEBUG *)
  val _ = print (String.concat ["\nInserted existentials in ", (LargeInt.toString $ Time.toSeconds ((Time.now()) - time_start)), "s\n\n"]);
 *)
 in
  res
 end
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
    val (path_cond_tm, path_cond_rest_tm) = dest_symb_branch_cases $ concl path_disj_thm

    val path_cond_rest_tm_list = fst $ dest_list path_cond_rest_tm
(* DEBUG
    val time_start = Time.now();
    val _ = print ("Unifying contracts of path ID "^((Int.toString id)^".\n"))
*)
    val new_p4_contracts = (LIST_CONJ (map (insert_existentials path_cond_tm) (zip path_cond_rest_tm_list (CONJUNCTS path_tree_list_leafs_thm))))
    val p4_contract_list_thm =
     PURE_REWRITE_RULE [SPEC path_cond_tm p4_contract_list_REWR2,
                        SPEC path_cond_tm p4_contract_list_GSYM_REWR,
			SPEC path_cond_tm p4_contract_list_REWR,
			listTheory.APPEND] new_p4_contracts
(* DEBUG
    val _ = print (String.concat ["\nDone in ", (LargeInt.toString $ Time.toSeconds ((Time.now()) - time_start)), "s\n\n"]);
*)

   in
     MATCH_MP (MATCH_MP p4_symb_exec_unify_n_gen path_disj_thm) p4_contract_list_thm
   end
  | p4_unify_path_tree' id_ctthm_list (node (id, path_disj_thm, (h::t))) path_tree_list_leafs =
(* DEBUG: Two iterations, for debugging a simple branch:
(*
val (h::t) = t
*)
val (node (id, path_disj_thm, (h::t))) = path_tree; (* h *)
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
  val postcond_thm = EQT_ELIM $ SIMP_CONV ((srw_ss())++bitstringLib.BITSTRING_GROUND_ss++boolSimps.LET_ss) rewr_thms $ mk_imp (hypo, mk_comb (postcond, res_state_tm))
 in
  MATCH_MP prel_res_thm postcond_thm
 end
;

(* TODO: make better solution for this *)
val prove_postcond_rewr_thms = [packet_has_port_def, get_packet_def, packet_dropped_def];

(* DEBUG
val step_thms = map #3 path_cond_step_list;

val h = el 2 step_thms
val step_thm = h
val rewr_thms = prove_postcond_rewr_thms
*)
fun p4_prove_postconds_debug' postcond []     _ = []
  | p4_prove_postconds_debug' postcond (h::t) n =
 let
  val res = p4_prove_postcond prove_postcond_rewr_thms postcond h
   handle exc => (print (("Error when proving postcondition for step theorem at index "^(Int.toString n))^"\n"); raise exc)
 in
  (res::(p4_prove_postconds_debug' postcond t (n + 1)))
 end
;
fun p4_prove_postconds_debug postcond step_thms =
 p4_prove_postconds_debug' postcond step_thms 0
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
fun p4_symb_exec_prove_contract_gen p4_symb_exec_fun debug_flag arch_ty ctx (fty_map, b_fty_map, pblock_action_names_map) const_actions_tables init_astate stop_consts_rewr stop_consts_never path_cond p4_is_finished_alt_opt n_max postcond =
 let

  (* DEBUG *)
  val time_start = Time.now();

  val ctx_name = "ctx"
  val ctx_def = hd $ Defn.eqns_of $ Defn.mk_defn ctx_name (mk_eq(mk_var(ctx_name, type_of ctx), ctx))

  (* Perform symbolic execution until all branches are finished *)
  val (path_tree, path_cond_step_list) =
   p4_symb_exec_fun debug_flag arch_ty (ctx_def, ctx) (fty_map, b_fty_map, pblock_action_names_map) const_actions_tables init_astate stop_consts_rewr stop_consts_never path_cond p4_is_finished_alt_opt n_max;

  (* DEBUG *)
  val _ = dbg_print debug_flag (String.concat ["\nFinished entire symbolic execution stage in ", (LargeInt.toString $ Time.toSeconds ((Time.now()) - time_start)), "s, trying to prove postcondition...\n\n"]);
  val time_start = Time.now();

  (* Prove postcondition holds for all resulting states in n-step theorems *)
  (* TODO: Should definitions below be arguments? *)
  val id_step_post_thm_list =
   if debug_flag
   then
    let
     val (l', l'') = unzip $ map (fn (a,b,c) => (a, c)) path_cond_step_list
    in
     zip l' (p4_prove_postconds_debug postcond l'')
    end
   else map (fn (a,b,c) => (a, p4_prove_postcond prove_postcond_rewr_thms postcond c)) path_cond_step_list

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

val p4_symb_exec_prove_contract =
 p4_symb_exec_prove_contract_gen (p4_symb_exec 1)
;

val nproc = Thread.numProcessors();
val p4_symb_exec_prove_contract_conc =
 let
  val nthreads_max = if nproc > 3 then (nproc-2) else 1
 in
  p4_symb_exec_prove_contract_gen (p4_symb_exec nthreads_max)
 end
;

fun dest_step_thm step_thm =
 dest_astate $ dest_some $ snd $ dest_eq $ snd $ dest_imp $ concl step_thm
;

fun p4_debug_symb_exec arch_ty ctx (fty_map, b_fty_map, pblock_action_names_map) const_actions_tables init_astate stop_consts_rewr stop_consts_never path_cond fuel =
 let
  val ctx_name = "ctx"
  val ctx_def = hd $ Defn.eqns_of $ Defn.mk_defn ctx_name (mk_eq(mk_var(ctx_name, type_of ctx), ctx))

  val (path_tree, state_list) = p4_symb_exec 1 true arch_ty (ctx_def, ctx) (fty_map, b_fty_map, pblock_action_names_map) const_actions_tables init_astate stop_consts_rewr stop_consts_never path_cond NONE fuel
  val state_list_tms = map (fn (path_id, path_cond, step_thm) => (path_id, path_cond, dest_step_thm step_thm)) state_list
 in
  (path_tree, state_list_tms)
 end
;

fun p4_debug_symb_exec_frame_lists arch_ty ctx (fty_map, b_fty_map, pblock_action_names_map) const_actions_tables init_astate stop_consts_rewr stop_consts_never path_cond fuel =
 let
  val (path_tree, state_list_tms) = p4_debug_symb_exec arch_ty ctx (fty_map, b_fty_map, pblock_action_names_map) const_actions_tables init_astate stop_consts_rewr stop_consts_never path_cond fuel
  val arch_frame_list_tms = map (fn (path_id, path_cond, (tm1, tm2, tm3, tm4)) => tm3) state_list_tms
 in
  (path_tree, arch_frame_list_tms)
 end
;

end
