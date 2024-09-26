structure p4_symb_execLib :> p4_symb_execLib = struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

open pairSyntax listSyntax numSyntax optionSyntax stringSyntax computeLib markerLib;

open listTheory p4_auxTheory optionTheory pairTheory;

open p4Theory p4_exec_semTheory;
open symb_execTheory p4_symb_execTheory p4_bigstepTheory;

open p4Syntax p4_exec_semSyntax evalwrapLib p4_testLib symb_execSyntax;
open auxLib symb_execLib p4_bigstepSyntax;

open p4_convLib p4_symb_exec_v1modelLib;

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

(********************)
(* p4_should_branch *)

fun p4_should_branch_get_err_msg step_thm =
 let
  (* Get number of steps *)
  val (assl, exec_thm) = dest_imp $ concl step_thm
  val (exec_tm, res_opt) = dest_eq exec_thm
  val (_, _, nsteps) = dest_arch_multi_exec exec_tm

  val _ = print "\n\nstep_thm prior to failure:\n";
  val _ = print $ term_to_string $ concl step_thm;
  val _ = print "\n\n";

 in
  (("error encountered during branch decision or disjunction theorem proof, after (regular) step "^(term_to_string nsteps))^".")
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
 | extern
 | conditional of term
 | select of term * (term list) * term
 | apply of term * term
 | output of term;

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
   else if is_stmt_ext stmt'
   then extern
   else no_branch
  end
 | NONE =>
  (* TODO: Generalise this, or at least extend it to other architectures *)
  (* TODO: Fix this hack: this indirectly uses the fact that last block has index 8 in
   * V1Model in HOL4P4 *)
 let
  val ascope = #1 $ dest_astate astate
  val (i, _, _, ascope) = dest_ascope ascope
 in
  if (int_of_term $ i) = 8 andalso
     (type_of ascope = p4_v1modelLib.v1model_arch_ty)
  then
   let
    val (_, _, v_map, _) = p4_v1modelLib.dest_v1model_ascope ascope
    (* TODO: Hack, do in SML *)
    val port_v_bit =
     dest_some $ rhs $ concl $ EVAL “(case ALOOKUP ^v_map "standard_metadata" of
				      | SOME (v_struct struct) =>
				       ALOOKUP struct "egress_spec"
				      | _ => NONE)”
    val port_bl = fst $ dest_pair $ dest_v_bit port_v_bit
   in
    output port_bl
   end
  else no_branch
 end
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

fun get_funn_dirs funn (func_map, b_func_map, ext_fun_map) =
 let
  val funn_sig_opt = rhs $ concl $ HOL4P4_CONV $ mk_lookup_funn_sig (funn, func_map, b_func_map, ext_fun_map)
 in
  if is_some funn_sig_opt
  then
   (map (snd o dest_pair)) $ fst $ dest_list $ dest_some funn_sig_opt
  else raise (ERR "get_funn_dirs" ("Signature of funn not found in function maps: "^(term_to_string funn)))
 end
;

fun is_arg_red (arg, dir) =
 if (is_d_out dir orelse is_d_inout dir)
 then term_eq T (rhs $ concl $ HOL4P4_CONV $ mk_is_e_lval arg) (* Must be lval *)
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
(* This returns the next expression to be reduced - note that this here means
 * the whole expression, not the exact minimal subexpression that is next to be reduced. *)
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

(* This simplifies a key until only the match_all application can be reduced next *)
val key_conv = rhs o concl o (SIMP_CONV std_ss [MAP, THE_DEF, BETA_THM, ZIP, v_of_e_def]);


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
  val (args, fv_index') = (fn (a, b) => (listSyntax.mk_list(a,e_ty),b)) (foldl (fn (argty, (args, fv_index')) => ((fn (arg', fv_index'') => (args@[arg'], fv_index'')) (get_fv_arg_of_tau argty fv_index'))) ([],fv_index) ftys)
 in
  (args, fv_index')
 end
;

fun get_freevars_call (fty_map,b_fty_map) funn block_name fv_index =
 let
  val b_fty_map_lookup_opt = rhs $ concl $ HOL4P4_CONV $ mk_alookup (b_fty_map, block_name)
  (* TODO: b_fty_map_lookup *)
 in
  if is_some b_fty_map_lookup_opt
  then
   let
    val local_fty_map = dest_some b_fty_map_lookup_opt
    val local_fty_map_lookup_opt = rhs $ concl $ HOL4P4_CONV $ mk_alookup (local_fty_map, funn)
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
      val fty_map_lookup_opt = rhs $ concl $ HOL4P4_CONV $ mk_alookup (fty_map, funn)
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

(* TODO: Move *)
val (v_to_tau_tm,  mk_v_to_tau, dest_v_to_tau, is_v_to_tau) =
  syntax_fns1 "p4_aux" "v_to_tau";

val get_bitv_bits_tac =
 qpat_x_assum ‘v_to_tau _ = SOME (tau_bit _)’
  (fn v_to_tau_thm => 
   let
    val tm = concl v_to_tau_thm
    val v_tm = dest_v_to_tau $ lhs tm
    val n_bits = dest_tau_bit $ dest_some $ rhs tm
    val bit_list = fixedwidth_freevars ("b", n_bits)
   in
    qpat_assum ‘^v_tm = v_bit (_, ^(term_of_int n_bits))’
     (fn v_bit_thm => 
      let
       val v_bit_tm = concl v_bit_thm
       val bitvector_tm = fst $ dest_pair $ dest_v_bit $ rhs v_bit_tm
      in
       assume_tac
	(prove(boolSyntax.list_mk_exists ((fst $ dest_list bit_list), (mk_eq (bitvector_tm, bit_list))),
	  assume_tac v_to_tau_thm >>
	  assume_tac v_bit_thm >>
          subgoal ‘LENGTH ^bitvector_tm = ^(term_of_int n_bits)’ >- (
           imp_res_tac v_to_tau_bit >>
           gs[]
          ) >>
	  (* TODO: This below is still a bit inefficient... *)
	  rpt $ goal_term (fn tm => tmCases_on (lhs $ snd $ strip_exists tm) []
	  (* Need to have LENGTH and rewrite that can resolve e.g. SUC (SUC 0) = 160. *)
				    >- (
				     FULL_SIMP_TAC pure_ss [LENGTH] >>
				     qpat_x_assum ‘n = n'’ (fn thm => assume_tac (SIMP_RULE std_ss [] thm)) >>
				     FULL_SIMP_TAC pure_ss [])
				    >> goal_term (fn tm => exists_tac (fst $ dest_cons $ lhs $ snd $ strip_exists tm) >> SIMP_TAC pure_ss [Once CONS_11, Once REFL_CLAUSE, Once AND_CLAUSES])) >>

	  goal_term (fn tm => tmCases_on (lhs tm) [] >> gs[])
	))
      end
     )
   end)
;

fun get_freevars_list (prefix, n) =
 List.tabulate (n, (fn n' => mk_var (prefix^(Int.toString (n')), bool)))
;

fun mk_n_disj n =
 list_mk_disj $ get_freevars_list ("d", n)
;

fun mk_n_filter_disj bool_list =
 list_mk_disj $ map fst $ filter (fn (a,b) => b) $ zip (get_freevars_list ("d", length bool_list)) bool_list
;
(* TODO: Upstream tactic that selects disjuncts based on patterns? *)
fun get_disj_thm bool_list = 
 prove(mk_imp(mk_n_filter_disj bool_list, mk_n_disj (length bool_list)), metis_tac[])
;

(* Function that decides whether to branch or not: returns NONE if no branch should
 * be performed, otherwise SOME of a list of cases and a theorem stating the disjunction
 * between them *)
fun p4_should_branch (fty_map, b_fty_map, pblock_action_names_map) const_actions_tables path_cond_defs (debug_flag, ctx_def) (fv_index, step_thm) =
 let
  (* DEBUG *)
  val time_start = Time.now();
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
       val def_branch_cond_thm = SIMP_CONV bool_ss [match_all_def, match_def, s_case_def, CLOSED_PAIR_EQ, v_11, CONS_11, satTheory.AND_INV] def_branch_cond

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
     else raise (ERR "p4_should_branch" ("Unsupported select value type: "^(term_to_string e)))
    else NONE
    (* Branch point: table application *)
  | apply (tbl_name, e) =>
(*
val apply (tbl_name, e) = apply (“"t2"”, “[e_v (v_bit ([e1; e2; e3; e4; e5; e6; e7; T],8))]”);

basic:
val apply (tbl_name, e) = apply
    (“"spd"”,
     “[e_v
         (v_bit
            ([ip128; ip129; ip130; ip131; ip132; ip133; ip134; ip135; ip136;
              ip137; ip138; ip139; ip140; ip141; ip142; ip143; ip144; ip145;
              ip146; ip147; ip148; ip149; ip150; ip151; ip152; ip153; ip154;
              ip155; ip156; ip157; ip158; ip159],32));
       e_v (v_bit ([ip72; ip73; ip74; ip75; ip76; ip77; ip78; ip79],8))]”);

ARBs:
val apply (tbl_name, e) = apply
    (“"forward"”,
     “[e_v
       (v_bit
	  ([ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
	    ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
	    ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB],32))]”);

*)
    if (hurdUtils.forall is_e_v) (fst $ dest_list e) andalso
       (* Perform a symbolic branch if the apply expression (list) contains
        * free variables or ARBs (hack) *)
       (not $ null $ free_vars e orelse HOLset.member (all_atoms e, “ARB:bool”))
    then
     let
      (* 1. Extract ctrl from ascope *)
      val ctrl = #4 $ dest_ascope $ #4 $ dest_aenv $ #1 $ dest_astate astate
      (* 2. Extract key sets from ascope using tbl_name *)
      val tbl_opt = rhs $ concl $ HOL4P4_CONV $ mk_alookup (ctrl, tbl_name)
     in
      if is_some tbl_opt
      then
       if exists (fn el => term_eq el tbl_name) const_actions_tables
       then
	let
	 val tbl = dest_some tbl_opt
	 (* 3. Construct different branch cases for all the key sets
	  *    N.B.: Can now be logically overlapping! *)
	 (* The branch cases for equality with the different table entry keys *)
	 (* TODO: Ensure this obtains the entries in correct order - here be dragons in case of
	  * funny priorities in the table *)
         val keys = fst $ dest_list $ rhs $ concl $ HOL4P4_CONV “MAP FST $ MAP FST ^tbl”
(* TODO: For some reason, changing the line above to the one below causes infinite looping...
	 val keys = fst $ dest_list $ rhs $ concl $ HOL4P4_CONV “MAP FST $ (^(mk_map (fst_tm, tbl)))”
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

(* For debugging symb_exec6:
 val i = “4:num”;

basic:
 val i = “4:num”;
*)
        val i = #1 $ dest_aenv $ #1 $ dest_astate astate
        (* TODO: Unify with the syntactic function obtaining the state above? *)
        val (ab_list, pblock_map, _, _, _, _, _, _, _, _) = dest_actx $ rhs $ concl ctx_def
        val (curr_block, _) = dest_arch_block_pbl $ rhs $ concl $ HOL4P4_CONV $ mk_el (i, ab_list)

        (* TODO: All of the information extracted from the ctx below could be
         * pre-computed *)

        (* TODO: handle Exceptions if result is not SOME *)
        val (pbl_type, params, b_func_map, decl_list, pars_map, tbl_map) = dest_pblock $ dest_some $ rhs $ concl $ HOL4P4_CONV $ mk_alookup (pblock_map, curr_block)
        val action_names_map = dest_some $ rhs $ concl $ HOL4P4_CONV $ mk_alookup (pblock_action_names_map, curr_block)
        val action_names = dest_some $ rhs $ concl $ HOL4P4_CONV $ mk_alookup (action_names_map, tbl_name)
        val (mk_l, default_action) = dest_pair $ dest_some $ rhs $ concl $ HOL4P4_CONV $ mk_alookup (tbl_map, tbl_name)
        val (default_action_name, default_action_args) = dest_pair default_action
        (* NOTE: We shouldn't filter out the default action name here - it will have
         * different "hit" dummy arg if it resulted from a hit or a default case. *)

        (* TODO: Depending on control plane API, this should use FOLDL_MATCH_alt instead
         * depending on the match kinds involved *)
        (* TODO: CURRENTLY ONLY WORKS FOR V1MODEL, FIX! *)
        val mk_list = fst $ dest_pair $ dest_some $ rhs $ concl $ HOL4P4_CONV $ mk_alookup (tbl_map, tbl_name)
        (* TODO: The below doesn't work with HOL4P4_CONV *)
        val mem_lpm = Teq $ rhs $ concl $ REWRITE_CONV [MEM] (mk_mem (“mk_lpm”, mk_list))
	val case_lhs =
         if mem_lpm
         then “FST $ FOLDL_MATCH ^e (^default_action, NONE) ^tbl”
         else “FST $ FOLDL_MATCH_alt ^e (^default_action, NONE) (1:num) ^tbl”

        (* TODO: This map should be a foldl, so that the same free variables don't appear in
         * different disjuncts *)
(*
        val (disj_tms, fv_indices) = unzip $ map (fn action_name =>
         let
	  val (action_args, fv_index') = get_freevars_call (fty_map,b_fty_map) “funn_name ^action_name” curr_block fv_index
	  val action_args' = rhs $ concl $ HOL4P4_CONV (mk_append (“[e_v (v_bool T); e_v (v_bool T)]”, (action_args)))
	  val action = mk_pair (action_name, action_args')
	  val res_case = list_mk_exists (rev $ free_vars action_args, mk_eq (case_lhs, action))
         in
          (res_case, fv_index')
         end) (fst $ dest_list action_names)
*)
        val (fv_index''', disj_tms) = foldl (fn (action_name, (fv_index', res_list)) =>
         let
	  val (action_args, fv_index'') = get_freevars_call (fty_map,b_fty_map) “funn_name ^action_name” curr_block fv_index'
	  val action_args' = rhs $ concl $ HOL4P4_CONV (mk_append (“[e_v (v_bool T); e_v (v_bool T)]”, action_args))
	  val action = mk_pair (action_name, action_args')
	  val res_case = boolSyntax.list_mk_exists (free_vars_lr action_args, mk_eq (case_lhs, action))
         in
          (fv_index'', (res_case::res_list))
         end) (fv_index, []) (fst $ dest_list action_names)
        (* Reverse order of disj_tms to get free variables in order of increasing index *)
        val disj_tms' = rev disj_tms
        val fv_indices = (replicate (fv_index''', length disj_tms'))

        val fv_indices' = fv_indices@[fv_index]
        val disj_tms'' = disj_tms'@[mk_eq (case_lhs, default_action)]

(* TODO: How to use ctrl_is_well_formed here:

val e = “[e_v (v_bit ([e1; e2; e3; e4; e5; e6; e7; T],8))]”;
val (fty_map, b_fty_map) = preprocess_ftymaps (symb_exec6_ftymap, symb_exec6_blftymap)

(* For basic.p4:

val (fty_map, b_fty_map) = preprocess_ftymaps (basic_ftymap, basic_blftymap)
val pblock_action_names_map = basic_pblock_action_names_map

*)

val (_, pblock_map, _, _, _, _, _, _, _, _)= dest_actx $ snd $ dest_eq $ concl $ ctx_def;

val ascope =  #1 $ dest_astate init_astate
val ctrl =  #4 $ dest_v1model_ascope $ #4 $ dest_ascope pre_ascope

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

        fun v_list_case_tac thm =
	 let
	  val list = snd $ dest_comb $ lhs $ concl thm
	 in
	  if is_nil list
	  then (* FULL_SIMP_TAC bool_ss [p4_auxTheory.v_to_tau_list_empty] *) ALL_TAC
	  else tmCases_on list [] >> ( gs[v_to_tau_list_def, AllCaseEqs()] )
	 end

(* DEBUG:
	val _ = dbg_print debug_flag (String.concat ["\nWell-formedness assumption is:\n\n",
				      term_to_string $ concl wf_assumption,
				      "\n\n",
				      "table is: ", term_to_string tbl_name, "\n\n",
				      "proof goal is:\n\n",
				      term_to_string (mk_disj_list disj_tms''),
				      "\n\n"])

*)
(*
val (fty_map, b_fty_map) = preprocess_ftymaps (basic_ftymap, basic_blftymap)
*)

        val disj_thm = prove (mk_imp (path_tm, mk_disj_list disj_tms''),
	 strip_tac >>
(* Remove all well-formedness assumptions on irrelevant tables. *)
         try $ (qpat_x_assum ‘v1model_tbl_is_well_formed _ _ (^tbl_name,^tbl)’ (fn thm =>
                              (rpt $ qpat_x_assum ‘_’ (fn thm' => ALL_TAC)) >> assume_tac thm)) >>
         REWRITE_TAC [disj_list_def] >>
	 FULL_SIMP_TAC pure_ss (path_cond_defs@[Once v1model_tbl_is_well_formed_def, Once p4_v1modelTheory.v1model_apply_table_f_def]) >>

         (* Specialise the well-formedness assumption and simplify it in isolation *)
	 qpat_x_assum ‘_’ (fn thm => assume_tac $ SPECL [curr_block, pbl_type, params, b_func_map, decl_list, pars_map, tbl_map] thm) >>
	 qpat_x_assum ‘_’ (fn thm => assume_tac $ HOL4P4_RULE thm) >>
	 qpat_x_assum ‘_’ (fn thm => assume_tac $ SPECL [action_names_map] thm) >>
	 qpat_x_assum ‘_’ (fn thm => assume_tac $ HOL4P4_RULE thm) >>
	 qpat_x_assum ‘_’ (fn thm => assume_tac $ SPECL [mk_l, action_names, default_action_name, default_action_args] thm) >>
	 qpat_x_assum ‘_’ (fn thm => assume_tac $ HOL4P4_RULE thm) >>
	 qpat_x_assum ‘_’ (fn thm => assume_tac $ SPEC e thm) >>
	 qpat_x_assum ‘_’ (fn thm => assume_tac $ HOL4P4_RULE thm) >>
	 qpat_x_assum ‘_’ (fn thm => assume_tac $ SPEC ctrl thm) >>
	 qpat_x_assum ‘_’ (fn thm => assume_tac $ HOL4P4_RULE thm) >>
         (* TODO: Avoid srw_ss() if possible... *)
	 qpat_x_assum ‘_’ (fn thm => assume_tac $ SIMP_RULE (srw_ss()) [] thm) >>

	 (goal_term (fn tm => ABBREV_TAC “goal:bool = ^tm”) >>
	  qpat_x_assum ‘Abbrev (goal <=> _)’ (fn thm => hide_tac "goal" thm) >>

	  gs[] >>

	  unhide_tac "goal" >>
	  UNABBREV_TAC "goal") >> (
           qpat_assum ‘f = _’ (fn thm => let val fname = rhs $ concl thm in
	   goal_term (fn tm =>
	    let
	     val disj_bool_list = (map (fn tm' => if term_eq (fst $ dest_pair $ rhs $ snd $ boolSyntax.strip_exists tm') fname then true else false)) $ boolSyntax.strip_disj tm
	    in
	     irule (get_disj_thm disj_bool_list)
	    end) end)
          ) >>
          (* Below this point, each resulting action is a separate subgoal. *)
          (
           (* TODO: Doesn't seem like it's worth it to use markerLib to hide and abbreviate the goal
            * anywhere in this step. *)
	   (* 1. Hard-coded additional arguments (with Booleans stating result from table match,
	    * default match) treated first *)
	   subgoal ‘?f_args' b. f_args = [e_v (v_bool T); e_v (v_bool b)]++f_args'’ >- (
	    Cases_on ‘f_args’ >> (
	     fs [oEL_def]
	    ) >>
	    Cases_on ‘t’ >> (
	     fs [oEL_def, v_to_tau_list_empty]
	    ) >>
	    fs[]
	   ) >>
           (* Needs to use goal, since this might finish the proof in the case of
            * function with no real args - should you check goal? *)
	   gs[oEL_def, v_to_tau_list_empty] >>

	   (* 2. Break apart the v_to_tau_list into separate v_to_tau premises *)
           (* TODO: This is the greatest bottleneck... *)
	   goal_term (fn tm => ABBREV_TAC “f_args_temp:e list = f_args'”) >>
	   goal_term (fn tm => ABBREV_TAC “goal:bool = ^tm”) >>
	   qpat_x_assum ‘Abbrev (goal <=> _)’ (fn thm => hide_tac "goal" thm) >>
	   goal_term (fn tm => ABBREV_TAC “f_args_temp':e list = f_args_temp”) >>
	   rpt (
	    qpat_assum ‘v_to_tau_list l = SOME taus’ (fn thm => v_list_case_tac thm)
	   ) >>
	   unhide_tac "goal" >>
	   UNABBREV_TAC "goal" >>
	   FULL_SIMP_TAC list_ss [v_to_tau_def, AllCaseEqs(), e_11] >>

	   (* TODO: Make this work for Booleans in arguments too *)
	   (* 3. Obtain the bits in the bitstrings of the individual v_to_tau premises *)
	   imp_res_tac v_to_tau_bit >>
	   rpt get_bitv_bits_tac >>
           FULL_SIMP_TAC pure_ss [] >>
	   goal_term (fn tm =>
	    let
	     val vars = flatten $ map (free_vars_lr o lhs) $ boolSyntax.strip_conj $ snd $ boolSyntax.strip_exists tm
	    in
	     (map_every $ exists_tac) vars
	    end) >>
           SIMP_TAC bool_ss []
        )
        )
       in
	SOME (disj_thm, fv_indices')
       end
      else raise (ERR "p4_should_branch" ("Table not found in ctrl: "^(term_to_string tbl_name)))
     end
    else NONE
  (* Branch point: extern *)
  | extern =>
   let
    (* TODO: Fix the hard-coded: let user supply list of externs *)
    (* We can evade some checks since we know we're executing an extern *)
    val (aenv, _, arch_frame_list, _) = dest_astate astate
    val top_frame = hd $ fst $ dest_list $ dest_arch_frame_list_regular $ arch_frame_list
    val (funn, stmt_stack, scope_list) = dest_frame top_frame
   in
    if is_funn_inst funn
    then
     let
      val ext_obj_tm = dest_funn_inst funn
      val ext_obj = stringSyntax.fromHOLstring ext_obj_tm
     in
      if (ext_obj = "register")
      then approx_v1model_register_construct p4_symb_arg_prefix fv_index scope_list
(*
       let
	(* Array size *)
	val array_size = fst $ dest_pair $ dest_v_bit $ dest_some $ rhs $ concl $ HOL4P4_CONV “lookup_lval ^scope_list (lval_varname (varn_name "size"))”
	val targ1_width = snd $ dest_pair $ dest_v_bit $ dest_some $ rhs $ concl $ HOL4P4_CONV “lookup_lval ^scope_list (lval_varname (varn_name "targ1"))”

	(* TODO: V1Model *)
	val tm1 = “v1model_register_construct_inner ^array_size ^targ1_width”

        val array_size_num = rhs $ concl $ EVAL “v2n ^array_size”
(*
	val approx_list_vars = fst $ dest_list $ fixedwidth_freevars_fromindex_ty (p4_symb_arg_prefix, fv_index, int_of_term array_size_num, mk_list_type bool)
	val rhs_tm = mk_list (map (fn var => mk_pair (var, targ1_width)) approx_list_vars, mk_prod (mk_list_type bool, num))
*)
        (* TODO: Hacky... *)
        val rhs_tm = hd $ fst $ dest_list $ fixedwidth_freevars_fromindex_ty (p4_symb_arg_prefix, fv_index, 1, mk_list_type $ mk_prod (mk_list_type bool, num))
	val goal_tm = mk_disj_list [boolSyntax.mk_exists (rhs_tm, mk_conj (mk_eq (tm1, rhs_tm), “wellformed_register_array ^targ1_width ^rhs_tm”))]
(*
(* Unless you cache, these have to be proved every single time *)
val list_var = mk_var("list", “:bool list”)
val list_hyp = mk_eq(mk_length list_var, entry_width)
val list_exists_thm = prove(mk_forall (list_var, mk_imp (list_hyp, list_mk_exists(fst $ dest_list approx_vars, mk_eq (list_var, approx_vars)))), 
rpt strip_tac >>
rpt (goal_term (fn tm => tmCases_on (fst $ dest_eq $ snd $ strip_exists tm) []) >> FULL_SIMP_TAC list_ss [])
);
*)

(*
val array_size = rhs $ concl $ EVAL “fixwidth 32 $ n2v 1024”

val targ1_width = “32”

val fv_index = 0

val array = “[([ARB:bool; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
             ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
             ARB; ARB; ARB; ARB; ARB; ARB],32);
           ([ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
             ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
             ARB; ARB; ARB; ARB; ARB; ARB],32);
           ([ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
             ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
             ARB; ARB; ARB; ARB; ARB; ARB],32)]”
*)

	val approx_thm =
         (* “^goal_tm” *)
	 prove(goal_tm,
          SIMP_TAC std_ss [disj_list_def, p4_v1modelTheory.v1model_register_construct_inner_def, wellformed_register_array_replicate_arb]
	 );
       in
	SOME (approx_thm, [fv_index+1])
       end
*)
      else NONE
     end
    else if is_funn_ext funn
    then
     (* TODO: What is going on here? Print debug output... *)
     let
      val (ext_obj_tm, ext_method_tm) = dest_funn_ext funn
      val ext_obj = stringSyntax.fromHOLstring ext_obj_tm
      val ext_method = stringSyntax.fromHOLstring ext_method_tm
      val ascope = #4 $ dest_aenv aenv
     in
      if (ext_obj = "register") andalso (ext_method = "read")
      then approx_v1model_register_read p4_symb_arg_prefix fv_index scope_list ascope
(*
       let
	(* 1. Get first entry of register array (for entry width) *)
	val array_index = fst $ dest_pair $ dest_v_bit $ dest_some $ rhs $ concl $ HOL4P4_CONV “lookup_lval ^scope_list (lval_varname (varn_name "index"))”
	val ext_ref = dest_v_ext_ref $ dest_some $ rhs $ concl $ HOL4P4_CONV “lookup_lval ^scope_list (lval_varname (varn_name "this"))”

	val ascope = #4 $ dest_aenv aenv
	(* TODO: V1Model *)
	val ext_obj_map = #2 $ p4_v1modelLib.dest_v1model_ascope ascope
	val array = snd $ dest_comb $ fst $ sumSyntax.dest_inr $ dest_some $ rhs $ concl $ HOL4P4_CONV “ALOOKUP ^ext_obj_map ^ext_ref”
        (* TODO: Double-check this works *)
	val entry_width = snd $ dest_pair $ dest_v_bit $ dest_some $ rhs $ concl $ HOL4P4_CONV “lookup_lval ^scope_list (lval_varname (varn_name "result"))”
(*
	val entry_width = snd $ dest_pair $ rhs $ concl $ HOL4P4_CONV “EL 0 ^array”
*)

	(* 2. Prove approximation theorem *)
	val tm1 = “v1model_register_read_inner ^entry_width ^array_index ^array”
	(* TODO: Hack, make function that returns list *)
	val approx_vars = fixedwidth_freevars_fromindex (p4_symb_arg_prefix, fv_index, int_of_term entry_width)
	val rhs_tm = mk_pair (approx_vars, entry_width)
	val goal_tm = mk_disj_list [list_mk_exists (fst $ dest_list approx_vars, mk_eq (tm1, rhs_tm))]

(* Unless you cache, these have to be proved every single time *)
val list_var = mk_var("list", “:bool list”)
val list_hyp = mk_eq(mk_length list_var, entry_width)
val list_exists_thm = prove(mk_forall (list_var, mk_imp (list_hyp, list_mk_exists(fst $ dest_list approx_vars, mk_eq (list_var, approx_vars)))), 
rpt strip_tac >>
rpt (goal_term (fn tm => tmCases_on (fst $ dest_eq $ snd $ strip_exists tm) []) >> FULL_SIMP_TAC list_ss [])
);

(*
val old_array = array

val array = “[([ARB:bool; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
             ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
             ARB; ARB; ARB; ARB; ARB; ARB],32);
           ([ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
             ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
             ARB; ARB; ARB; ARB; ARB; ARB],32);
           ([ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
             ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
             ARB; ARB; ARB; ARB; ARB; ARB],32)]”

val array2 = “[([ARB:bool; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
             ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
             ARB; ARB; ARB; ARB; ARB; ARB],32);
           ([ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
             ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
             ARB; ARB; ARB; ARB; ARB; ARB],32);
           ([ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
             ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
             ARB; ARB; ARB; ARB; ARB; ARB],32)]”
*)

	val approx_thm =
         (* “^goal_tm” *)
	 prove(mk_imp (“wellformed_register_array ^entry_width ^array”, goal_tm),
          (* As soon as possible, hide the array, which may be big *)
          markerLib.ABBREV_TAC “(array:(bool list # num) list) = ^array” >>
          qpat_x_assum ‘Abbrev (array = _)’ (fn thm => markerLib.hide_tac "big_array" thm) >>
          (* TODO: V1Model hack *)
          SIMP_TAC std_ss [disj_list_def, p4_v1modelTheory.v1model_register_read_inner_def] >>
(*
          subgoal ‘wellformed_register_array ^entry_width array’ >- (
           markerLib.unhide_tac "big_array" >>
           markerLib.UNABBREV_TAC "array" >>
           (* TODO: May want to use path cond here if you abbreviate array using assumptions *)
           EVAL_TAC
          ) >>
*)
          disch_tac >>
          CASE_TAC >- (
           EVAL_TAC >>
           ntac (int_of_term entry_width) (exists_tac (mk_arb bool)) >>
           REWRITE_TAC []
          ) >>
          Cases_on ‘x’ >>
	  imp_res_tac p4_symb_execTheory.wellformed_register_array_oEL >>
          imp_res_tac list_exists_thm >>
          RW_TAC std_ss []
	 );
        (* TODO: The antecedent may be computable. Either check this before or compute it here *)
        val wf_ante_eval = EVAL “wellformed_register_array ^entry_width ^array”

        val approx_thm' =
         if Teq $ snd $ dest_eq $ concl wf_ante_eval
         then MATCH_MP approx_thm (EQT_ELIM wf_ante_eval)
         else approx_thm
       in
	SOME (approx_thm', [fv_index+(int_of_term entry_width)])
       end
*)
      else NONE
     end
    else NONE
   end
  (* Branch point: emission of packet in final block *)
  | output port_bl =>
   if (not $ null $ free_vars port_bl orelse HOLset.member (all_atoms port_bl, “ARB:bool”))
   then
    (* TODO: Fix hack... *)
    SOME (SPEC “v1model_is_drop_port ^port_bl” disj_list_EXCLUDED_MIDDLE, [fv_index, fv_index])
   else NONE
  | no_branch => NONE)

  val _ = dbg_print debug_flag (String.concat ["\nFinished symbolic branch decision computations in ",
				(LargeInt.toString $ Time.toMilliseconds ((Time.now()) - time_start)),
				" ms\n"])
 in
  res
 end
 handle (HOL_ERR exn) => raise (ERR "p4_should_branch" (String.concat ["Exception: ", #message exn, " in function ", #origin_function exn, " from structure ", #origin_structure exn, p4_should_branch_get_err_msg step_thm])) (* (wrap_exn "p4_symb_exec" "p4_should_branch" (HOL_ERR exn)) *)
;


(*******************)
(* p4_regular_step *)

fun p4_regular_step_get_err_msg step_thm =
 let
  (* Get number of steps *)
  val (assl, exec_thm) = dest_imp $ concl step_thm
  val (exec_tm, res_opt) = dest_eq exec_thm
  val (_, _, nsteps) = dest_arch_multi_exec exec_tm

  val _ = print "\n\nstep_thm prior to failure:\n";
  val _ = print $ term_to_string $ concl step_thm;
  val _ = print "\n\n";
(* DEBUG:
  val next_state_str =
   if is_some res_opt
   then (term_to_string $ dest_some res_opt)
   else "NONE"
*)
 in
  (("error encountered at (regular) step "^(term_to_string nsteps))^".")
(* DEBUG:
  (("error encountered at step "^(term_to_string nsteps))^(". State prior to failure is: ")^((next_state_str)^(" \n\n and path condition is: "^(term_to_debug_string $ concl path_cond))))
*)
 end
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
  else if is_status_returnv status
  then print (String.concat ["\nReducing programmable block exit...\n\n"])
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
   optionSyntax.is_none $ rhs $ concl $ HOL4P4_CONV $ mk_alookup (func_map, fname)
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

val (symb_exec_abbrevs_tm,  mk_symb_exec_abbrevs, dest_symb_exec_abbrevs, is_symb_exec_abbrevs) =
  syntax_fns1 "p4_symb_exec" "symb_exec_abbrevs";

val (stmt_stack_abbrev_tm,  mk_stmt_stack_abbrev, dest_stmt_stack_abbrev, is_stmt_stack_abbrev) =
  syntax_fns1 "p4_symb_exec" "stmt_stack_abbrev";

val (frame_stack_abbrev_tm,  mk_frame_stack_abbrev, dest_frame_stack_abbrev, is_frame_stack_abbrev) =
  syntax_fns1 "p4_symb_exec" "frame_stack_abbrev";

val (ascope_abbrev_tm,  mk_ascope_abbrev, dest_ascope_abbrev, is_ascope_abbrev) =
  syntax_fns1 "p4_symb_exec" "ascope_abbrev";

(* This function replaces the tail of the frame stack with a
 * free variable, and adds the equality between these to the
 * hypotheses of the theorem. *)
fun abbreviate_frame_stack step_thm =
 let
  val (ante, concl_step) = dest_imp $ concl step_thm
  val (prestate, poststate_opt) = dest_eq concl_step
  val poststate = dest_some poststate_opt
  val (aenv, g_scope_list, arch_frame_list, status) = dest_astate poststate
  val arch_frame_list' = dest_arch_frame_list_regular arch_frame_list
 in
  let
   val (arch_frame_list'', list_ty) = dest_list arch_frame_list'
  in
   if length arch_frame_list'' = 1
   then step_thm
   else
    let
     (* 2. Take the sub-term to abbreviate and pick something to abbreviate it to *)
     val arch_frame_list_tl = mk_list (tl arch_frame_list'', list_ty)
     val abbrev_var = mk_var("frame_stack_tl", mk_list_type frame_ty)
     val abbrev_tm = mk_eq (abbrev_var, arch_frame_list_tl)

     (* 3. Construct a pattern to mark the sub-term to abbreviate in the conclusion of step_thm *)
     val pat_tm = mk_imp (ante, mk_eq (prestate, mk_some $ mk_astate(aenv, g_scope_list, mk_arch_frame_list_regular $ mk_cons (hd arch_frame_list'', abbrev_var), status)))

    in
     (* 4. Perform the actual abbreviation *)
     (* TODO: Use symb_exec_abbrevs *)
     SUBST [abbrev_var |-> GSYM (ASSUME abbrev_tm)] pat_tm step_thm
    end
  end
 end
;

(* This function replaces the tail of the stmt stack with a
 * free variable, and adds the equality between these to the
 * hypotheses of the theorem. *)
fun abbreviate_stmt_stack step_thm =
 let
  val (ante, concl_step) = dest_imp $ concl step_thm
  val (prestate, poststate_opt) = dest_eq concl_step
  val poststate = dest_some poststate_opt
  val (aenv, g_scope_list, arch_frame_list, status) = dest_astate poststate
  val arch_frame_list' = dest_arch_frame_list_regular arch_frame_list
 in
  let
   val (arch_frame_list'', list_ty) = dest_list arch_frame_list'
   val (funn, stmt_stack, scope_stack) = dest_frame $ hd arch_frame_list''
   val (stmt_stack', stmt_ty) = dest_list stmt_stack
  in
   if length stmt_stack' = 1
   then step_thm
   else
    let

     val stmt_stack_tl = mk_list (tl stmt_stack', stmt_ty)
     val abbrev_var = mk_var("stmt_stack_tl", mk_list_type stmt_ty)
     val abbrev_tm = mk_eq (abbrev_var, stmt_stack_tl)

     (* 3. Construct a pattern to mark the sub-term to abbreviate in the conclusion of step_thm *)
     val pat_tm = mk_imp (ante, mk_eq (prestate, mk_some $ mk_astate(aenv, g_scope_list, mk_arch_frame_list_regular (mk_cons (mk_frame (funn, mk_cons (hd stmt_stack', abbrev_var), scope_stack) , mk_list (tl arch_frame_list'', list_ty))), status)))

    in
     (* 4. Perform the actual abbreviation *)
     (* TODO: Use symb_exec_abbrevs *)
     SUBST [abbrev_var |-> GSYM (ASSUME abbrev_tm)] pat_tm step_thm
    end
  end
 end
;

(* This function replaces the arch scope with a
 * free variable, and adds the equality between these to the
 * hypotheses of the theorem. *)
fun abbreviate_ascope step_thm =
 let
  val (ante, concl_step) = dest_imp $ concl step_thm
  val (prestate, poststate_opt) = dest_eq concl_step
  val poststate = dest_some poststate_opt
  val (aenv, g_scope_list, arch_frame_list, status) = dest_astate poststate
  val (block_index, io_list, io_list', ascope) = dest_aenv aenv
 in
  let
   (* 2. Take the sub-term to abbreviate and pick something to abbreviate it to *)
   val abbrev_var = mk_var("ascope", type_of ascope)
   val abbrev_tm = mk_eq (abbrev_var, ascope)

   (* 3. Construct a pattern to mark the sub-term to abbreviate in the conclusion of step_thm *)
   val pat_tm = mk_imp (ante, mk_eq (prestate, mk_some $ mk_astate(mk_aenv (block_index, io_list, io_list', abbrev_var), g_scope_list, arch_frame_list, status)))

  in
   (* 4. Perform the actual abbreviation *)
   (* TODO: Use symb_exec_abbrevs *)
   SUBST [abbrev_var |-> GSYM (ASSUME abbrev_tm)] pat_tm step_thm
  end
 end
;

(* Returns a tuple of three Boolean flags signifying which of the
 * abbreviations in symb_exec_abbrevs that are inactive *)
(* TODO: You could also keep track of this purely in SML, 
 * if the abbreviation function returns which abbreviations were
 * made *)
fun check_abbreviations ante =
 if is_conj ante
 then
  let
   val (first_conj, conj_tl) = dest_conj ante
  in
   if is_symb_exec_abbrevs first_conj
   then
    let
     val abbrevs = strip_conj $ dest_symb_exec_abbrevs first_conj
    in
     (List.exists is_stmt_stack_abbrev abbrevs,
      List.exists is_frame_stack_abbrev abbrevs,
      List.exists is_ascope_abbrev abbrevs)
    end
   (* No symb_exec_abbrevs: no active abbreviations *)
   else (true, true, true)
(*
   if is_symb_exec_abbrevs first_conj
   then
    let
     val (stmt_stack_tl_abbrev_opt, frame_stack_tl_abbrev_opt, ascope_abbrev_opt) = dest_symb_exec_abbrevs first_conj
    in
     (is_none stmt_stack_tl_abbrev_opt, is_none frame_stack_tl_abbrev_opt, is_none ascope_abbrev_opt)
    end
   (* No symb_exec_abbrevs: no active abbreviations *)
   else (true, true, true)
*)
  end
 (* Unmodified path condition: No active abbreviations *)
 else (true, true, true)
;

(* Abbreviates everything that is not currently abbreviated: use
 * this after evaluating steps *)
fun abbreviate step_thm =
 let
  val (ante, concl_step) = dest_imp $ concl step_thm
  val (abbreviate_stmt_stack, abbreviate_frame_list, abbreviate_ascope) = check_abbreviations ante

  (* 1. Disassemble the step_thm to prepare for making any abbreviation *)
  val (prestate, poststate_opt) = dest_eq concl_step
  val poststate = dest_some poststate_opt
  val (aenv, g_scope_list, arch_frame_list, status) = dest_astate poststate
  val arch_frame_list' = dest_arch_frame_list_regular arch_frame_list
  val (block_index, io_list, io_list', ascope) = dest_aenv aenv

  (* Cancel frame stack abbreviation if frame stack is too small *)
  val (arch_frame_list'', list_ty) = dest_list arch_frame_list'
  val abbreviate_frame_list =
   if abbreviate_frame_list
   then not (length arch_frame_list'' = 1)
   else false

  (* Cancel stmt stack abbreviation if stmt stack is too small *)
  val (funn, stmt_stack, scope_stack) = dest_frame $ hd arch_frame_list''
  val (stmt_stack', stmt_ty) = dest_list stmt_stack
  val abbreviate_stmt_stack =
   if abbreviate_stmt_stack
   then not (length stmt_stack' = 1)
   else false
(*
  val (abbreviate_stmt_stack, abbreviate_frame_list, abbreviate_ascope) = (true, true, true)
*)

  val substs = []
  val subst_rewrs = []

  (* Statement stack tail *)
  val stmt_stack_tl = mk_list (tl stmt_stack', stmt_ty)
  val (stmt_stack_abbrev_var, substs', subst_rewrs') =
   if abbreviate_stmt_stack
   then
    let
     val stmt_stack_abbrev_var = mk_var("stmt_stack_tl", mk_list_type stmt_ty)
     val stmt_stack_abbrev_tm = mk_eq (stmt_stack_abbrev_var, stmt_stack_tl)
    in
     (stmt_stack_abbrev_var,
      [stmt_stack_abbrev_var |-> GSYM (ASSUME stmt_stack_abbrev_tm)]@substs,
      [GSYM $ SPEC (stmt_stack_abbrev_tm) stmt_stack_abbrev_def]@subst_rewrs)
    end
   else (stmt_stack_tl, substs, subst_rewrs)

  (* Frame stack tail *)
  val arch_frame_list_tl = mk_list (tl arch_frame_list'', list_ty)
  val (frame_list_abbrev_var, substs'', subst_rewrs'') =
   if abbreviate_frame_list
   then
    let
     val frame_list_abbrev_var = mk_var("frame_stack_tl", mk_list_type frame_ty)
     val frame_list_abbrev_tm = mk_eq (frame_list_abbrev_var, arch_frame_list_tl)
    in
     (frame_list_abbrev_var,
      [frame_list_abbrev_var |-> GSYM (ASSUME frame_list_abbrev_tm)]@substs',
      [GSYM $ SPEC (frame_list_abbrev_tm) frame_stack_abbrev_def]@subst_rewrs')
    end
   else (arch_frame_list_tl, substs', subst_rewrs')

  (* ascope *)
  val (ascope_abbrev_var, substs''', subst_rewrs''') =
   if abbreviate_ascope
   then
    let
     val ascope_abbrev_var = mk_var("ascope", type_of ascope)
     val ascope_abbrev_tm = mk_eq (ascope_abbrev_var, ascope)
    in
     (ascope_abbrev_var,
      [ascope_abbrev_var |-> GSYM (ASSUME ascope_abbrev_tm)]@substs'',
      [GSYM $ SPEC (ascope_abbrev_tm) ascope_abbrev_def]@subst_rewrs'')
    end
   else (ascope, substs'', subst_rewrs'')


  val pat_tm = mk_imp (ante, mk_eq (prestate, mk_some $ mk_astate(mk_aenv (block_index, io_list, io_list', ascope_abbrev_var), g_scope_list, mk_arch_frame_list_regular (mk_cons (mk_frame (funn, mk_cons (hd stmt_stack', stmt_stack_abbrev_var), scope_stack) , frame_list_abbrev_var)), status)))

  val step_thm' = PURE_ONCE_REWRITE_RULE subst_rewrs''' $ hurdUtils.DISCH_CONJUNCTS_ALL $ SUBST substs''' pat_tm step_thm

 in
  (* 4. Perform the actual abbreviation *)
  (* TODO: Convert imp to conj in path cond *)
  PURE_ONCE_REWRITE_RULE [GSYM $ SPEC (fst $ dest_imp $ concl step_thm') symb_exec_abbrevs_def] step_thm'
 end
;

(* TODO: Upstream? *)
local
fun subst_of_list' [] acc = (rev acc):('a, 'b) subst
  | subst_of_list' ((a,b)::t) acc =
 subst_of_list' t (({redex=a, residue=b})::acc)
in
fun subst_of_list list = subst_of_list' list []
end
;

(* TODO: Do this for multiple abbreviations in one go. *)
fun deabbreviate (deabbrev_stmt_stack, deabbrev_frame_stack, deabbrev_ascope) step_thm =
 let
  val abbrevs = List.filter (fn el => is_symb_exec_abbrevs el) $ strip_conj $ fst $ dest_imp $ concl step_thm
  (* TODO: Selectively pick out the abbreviations you want to deabbreviate *)
 in
  if length abbrevs = 1
  then
   let
    val rewr_thm = PURE_REWRITE_CONV [symb_exec_abbrevs_def, stmt_stack_abbrev_def, frame_stack_abbrev_def, ascope_abbrev_def] (hd abbrevs)
    val (abbrev_vars, big_tms) = unzip $ map dest_eq $ strip_conj $ snd $ dest_eq $ concl rewr_thm
    val refl_thm =
     if length big_tms = 1
     then (REFL (hd big_tms))
     else
      List.foldl (fn (a,b) => CONJ b (REFL a)) (REFL $ hd big_tms) (tl big_tms)
   in
    MP (INST (subst_of_list (zip abbrev_vars big_tms)) step_thm) refl_thm
   end
  (* Presumably, this means that length abbrevs = 0 *)
  else step_thm
 end
;

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
   eval_ctxt_gen (stop_consts_rewr@stop_consts_never)
                 (stop_consts_never) path_cond
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
      then Teq $ rhs $ concl $ HOL4P4_CONV (mk_is_some $ mk_alookup (b_func_map, dest_funn_name funn))
      else false)
    then
     (case p4_is_shortcuttable (funn, stmt) func_map of
	res_shortcut => res_shortcut
      | res_no_shortcut_e e => res_no_shortcut_e e
(*
       p4_is_f_arg_shortcuttable (func_map, b_func_map, ext_fun_map) e
*)
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
  (* TODO: Perform abbreviation/deabbreviation here? *)
(*
(* 1. Take the step theorem and disassemble it *)
val test_thm = step_thm;

val (ante, concl_step) = dest_imp $ concl step_thm
val (prestate, poststate_opt) = dest_eq concl_step
val poststate = dest_some poststate_opt
val (aenv, g_scope_list, arch_frame_list, status) = dest_astate poststate

(* 2. Take the sub-term to abbreviate and pick something to abbreviate it to *)
val subs_tm = aenv;
val abc_tm = ``(aenv:v1model_ascope aenv)``;
val eq_tm = ``^abc_tm = ^subs_tm``

(* 3. Construct a pattern to mark the sub-term to abbreviate in the conclusion of step_thm *)
val B_tm = ``(B:v1model_ascope aenv)``;
val pat_tm = “^(mk_imp (ante, mk_eq (prestate, mk_some $ mk_astate(B_tm, g_scope_list, arch_frame_list, status))))”

(* 4. Perform the actual abbreviation *)

val changed_thm = SUBST [B_tm |-> GSYM (ASSUME eq_tm)] pat_tm test_thm

val changed_thm = REWRITE_RULE [GSYM (ASSUME eq_tm)] test_thm;

(* 4. Deabbreviate - requires the stuff from step 2 *)

(* Changing back using instantiation + evaluation: *)
val changed_back_thm = BETA_RULE (CONV_RULE (RATOR_CONV EVAL) (INST [abc_tm |-> subs_tm] (DISCH_ALL changed_thm)));

(* Changing back using instantiation + modus ponens: *)
val changed_back_thm = MP (INST [abc_tm |-> subs_tm] (DISCH_ALL changed_thm)) (REFL subs_tm);
(* Alternative variant: *)
val changed_back_thm = MP (DISCH_ALL (INST [abc_tm |-> subs_tm] (changed_thm))) (REFL subs_tm);

val changed_back_thm = REWRITE_RULE [gen_rev_thm] (DISCH_ALL (INST [abc_tm |-> subs_tm] (changed_thm)));

*****************************

(* TODO: Is this faster or slower? *)
SUBST_MATCH (GSYM (ASSUME eq_tm)) test_thm

*)
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
     then (EQT_ELIM $ (REWRITE_CONV ([ctx_def, in_local_fun'_def, alistTheory.ALOOKUP_def]) THENC RESTR_HOL4P4_CONV_stop_consts)$ mk_in_local_fun' (lhs $ concl ctx_def, block_index, arch_frame_list, nsteps),
           mk_bigstep_arch_exec (mk_none $ mk_prod (type_of ctx, type_of b_func_map), g_scope_list, arch_frame_list))
(* OLD
     then (HOL4P4_RULE $ REWRITE_CONV ([ctx_def, in_local_fun'_def, alistTheory.ALOOKUP_def]) $ mk_in_local_fun' (lhs $ concl ctx_def, block_index, arch_frame_list, nsteps),
           mk_bigstep_arch_exec (mk_none $ mk_prod (type_of ctx, type_of b_func_map), g_scope_list, arch_frame_list))
*)
     (* Function argument reduction *)
     else (EQT_ELIM $ (REWRITE_CONV ([ctx_def, in_local_fun'_def, alistTheory.ALOOKUP_def]) THENC RESTR_HOL4P4_CONV_stop_consts)$ mk_in_local_fun' (lhs $ concl ctx_def, block_index, arch_frame_list, nsteps),
           mk_bigstep_arch_exec' (mk_some $ mk_pair (aenv, ctx), g_scope_list, arch_frame_list))
    val bigstep_thm = REWRITE_RULE [GSYM ctx_def] $ RESTR_HOL4P4_CONV_stop_consts bigstep_tm

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

    (* DEBUG *)
    val _ = dbg_print debug_flag (String.concat ["Simplifying word ops on constants: ",
				  (LargeInt.toString $ Time.toMilliseconds ((Time.now()) - time_start2)),
				  " ms\n"])

    (* DEBUG *)
    val time_start3 = Time.now();

    val shortcut_comp_thm =
     if shortcut_result_eq shortcut res_shortcut
     then bigstep_arch_exec_comp'_NONE
     else bigstep_arch_exec_comp'_SOME

    val res =
     SIMP_RULE simple_arith_ss []
      (MATCH_MP (MATCH_MP (MATCH_MP shortcut_comp_thm (PURE_REWRITE_RULE [GSYM ctx_def] step_thm)) is_local_thm) bigstep_thm')

    (* DEBUG *)
    val _ = dbg_print debug_flag (String.concat ["step_thm composition: ",
				  (LargeInt.toString $ Time.toMilliseconds ((Time.now()) - time_start3)),
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
     else norewr_eval_ctxt astate

    (* DEBUG *)
    val _ = dbg_print debug_flag (String.concat [(if use_eval_in_ctxt then "evaluation-in-context: " else "evaluation: "),
				  (LargeInt.toString $ Time.toMilliseconds ((Time.now()) - time_start)),
				  " ms\n"])

    (* DEBUG:
    val stop_consts1 = (stop_consts_rewr@stop_consts_never);
    val stop_consts2 = (stop_consts_never);
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
               if use_eval_in_ctxt
               then
	        next_subexp_syntax_f $ next_e_syntax_f $ the_final_state_imp step_thm2
               else
                next_subexp_syntax_f $ next_e_syntax_f $ (optionSyntax.dest_some $ snd $ dest_eq $ concl step_thm2)
	      (* Evaluate the subexp without restrictions *)
	      val subexp_red_res_EVAL = HOL4P4_CONV subexp_red_res
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
(* Non-conj version:
	 (MATCH_MP (MATCH_MP comp_thm (PURE_REWRITE_RULE [GSYM ctx_def] step_thm)) (PURE_REWRITE_RULE [GSYM ctx_def] step_thm2))
*)
         (if use_eval_in_ctxt
          then
	   (MATCH_MP comp_thm (CONJ (PURE_REWRITE_RULE [GSYM ctx_def] step_thm) (PURE_REWRITE_RULE [GSYM ctx_def] step_thm2)))
          else
          (* TODO: Specialise type of composition theorem before? *)
(* small-big:
	  (MATCH_MP small_big_exec_comp_conj (CONJ (PURE_REWRITE_RULE [GSYM ctx_def] step_thm) (PURE_REWRITE_RULE [GSYM ctx_def] step_thm2))))
*)
	  (MATCH_MP arch_multi_exec_comp_n_tl_assl_conj_nomidassl (CONJ (PURE_REWRITE_RULE [GSYM ctx_def] step_thm) (PURE_REWRITE_RULE [GSYM ctx_def] step_thm2))))

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

(******************)
(* p4_is_finished *)
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


(***********************)
(* Top-level functions *)
(* The below functions use symb_execLib to prove contracts, or to get intermediate symbolic
 * execution results. *)

fun preprocess_ftymaps (fty_map, b_fty_map) =
 let
  val fty_map_opt = rhs $ concl $ HOL4P4_CONV “deparameterise_ftymap_entries ^fty_map”
  val b_fty_map_opt = rhs $ concl $ HOL4P4_CONV “deparameterise_b_ftymap_entries ^b_fty_map”
 in
  if is_some fty_map_opt
  then
   if is_some b_fty_map_opt
   then (dest_some fty_map_opt, dest_some b_fty_map_opt)
   else raise (ERR "preprocess_ftymaps" "Could not deparameterise block-local function type map.")
  else raise (ERR "preprocess_ftymaps" "Could not deparameterise function type map.")
 end
;

val (small_big_exec_tm, mk_small_big_exec, dest_small_big_exec, is_small_big_exec) =
 syntax_fns2 "p4_bigstep" "small_big_exec";

(* The main symbolic execution.
 * Here, the static ctxt and the dynamic path condition have been merged. *)
fun p4_symb_exec nthreads_max debug_flag arch_ty (ctx_def, ctx) (fty_map, b_fty_map, pblock_action_names_map) const_actions_tables path_cond_defs init_astate stop_consts_rewr stop_consts_never thms_to_add path_cond p4_is_finished_alt_opt fuel =
 let
  (* Pre-process ftymap and b_fty_map *)
  val (fty_map', b_fty_map') = preprocess_ftymaps (fty_map, b_fty_map)

  (* Pre-process const_actions_tables *)
  val const_actions_tables' = map stringSyntax.fromMLstring const_actions_tables

  val comp_thm = INST_TYPE [Type.alpha |-> arch_ty] arch_multi_exec_comp_n_tl_assl_conj

  (* TODO: Use eval_ctxt defined below for init_step_thm? *)
  val init_step_thm = eval_ctxt_gen (stop_consts_rewr@stop_consts_never) stop_consts_never path_cond (mk_arch_multi_exec (ctx, init_astate, 0))

  val eval_ctxt = p4_eval_ctxt_gen ((stop_consts_rewr@stop_consts_never), stop_consts_never, (fn astate => mk_arch_multi_exec (ctx, astate, 1)))
(*
  val norewr_eval_ctxt = p4_get_norewr_eval_ctxt_gen ((stop_consts_rewr@stop_consts_never), thms_to_add, (fn astate => mk_small_big_exec (ctx, astate)))
*)
  val norewr_eval_ctxt = p4_get_norewr_eval_ctxt_gen ((stop_consts_rewr@stop_consts_never), thms_to_add, (fn astate => mk_arch_multi_exec (ctx, astate, 1)))
  val regular_step = p4_regular_step (debug_flag, ctx_def, ctx, norewr_eval_ctxt, eval_ctxt) comp_thm
  val is_finished =
   if isSome p4_is_finished_alt_opt
   then valOf p4_is_finished_alt_opt
   else p4_is_finished
 in
(* DEBUG:
val lang_regular_step = p4_regular_step (debug_flag, ctx_def, ctx, norewr_eval_ctxt, eval_ctxt) comp_thm;
val lang_init_step_thm = init_step_thm;
val lang_should_branch = p4_should_branch (fty_map', b_fty_map') const_actions_tables' path_cond_defs (debug_flag, ctx_def);
val lang_is_finished = is_finished;

val const_actions_tables = const_actions_tables'
val (fty_map, b_fty_map) = (fty_map', b_fty_map')
*)
  if List.exists (fn b => b = true) $ map (String.isPrefix p4_symb_arg_prefix) $ map (fst o dest_var) $ free_vars $ concl init_step_thm
  then raise (ERR "p4_symb_exec" ("Found free variables with the prefix \""^(p4_symb_arg_prefix^"\" in the initial step theorem: this prefix is reserved for use by the symbolic execution.")))
  else
   if nthreads_max > 1
   then
     symb_exec_conc (debug_flag, regular_step, init_step_thm, p4_should_branch (fty_map', b_fty_map', pblock_action_names_map) const_actions_tables' path_cond_defs (debug_flag, ctx_def), is_finished) path_cond fuel nthreads_max
   else symb_exec (debug_flag, regular_step, init_step_thm, p4_should_branch (fty_map', b_fty_map', pblock_action_names_map) const_actions_tables' path_cond_defs (debug_flag, ctx_def), is_finished) path_cond fuel
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

val (p4_contract'_tm, mk_p4_contract', dest_p4_contract', is_p4_contract') =
 syntax_fns3 "p4_symb_exec" "p4_contract'";

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

fun p4_int_of_symb_argvar var =
 let
  val varname = fst $ dest_var var
  val i = string_to_int $ unprefix p4_symb_arg_prefix varname
 in
  i
 end
;

fun var_compare var1 var2 =
 (p4_int_of_symb_argvar var1) < (p4_int_of_symb_argvar var2)
;

fun insert_existentials path_cond_tm (path_cond_case, thm) =
 let
  val (precond, contract_ctx, init_state, contract_postcond) = dest_p4_contract $ concl thm
  val vars = (((filter (fn el => String.isPrefix p4_symb_arg_prefix $ fst $ dest_var el)) o free_vars_lr)) precond
  val precond' = mk_conj (path_cond_tm, path_cond_case)
  val goal_contract = mk_p4_contract (precond', contract_ctx, init_state, contract_postcond)

(*
  val time_start = Time.now();
*)

(* “^goal_contract” *)
  val res =
   prove(goal_contract,
         (if boolSyntax.is_exists path_cond_case
          then
           (* This is the demanding case: when there are existential quantifiers involved *)
	   assume_tac (REWRITE_RULE [p4_contract_def] (GENL vars thm)) >>
	   rewrite_tac [p4_contract_def] >>
	   goal_term (fn tm =>
	    let
	     val exec_imp_postcond_tm = snd $ boolSyntax.dest_imp tm
	    in
	     ABBREV_TAC “exec_imp_postcond:bool = ^exec_imp_postcond_tm”
	    end) >>
           qpat_x_assum ‘Abbrev (exec_imp_postcond <=> _)’ (fn thm => hide_tac "exec_imp_postcond" thm) >>
           disch_tac >>
           (* The underscore will try anything, but there's only one assumption that will work,
            * it's a hassle to match only that one though *)
           qpat_x_assum ‘_’ (fn thm => irule thm) >>
	   rpt conj_tac >> (
	    qpat_assum ‘_’ (fn thm' =>
	    let
	     val conjs = boolSyntax.strip_conj $ concl thm'
	     val existvars_freeconjs = map boolSyntax.strip_exists conjs
	    in
	     goal_term (fn tm =>
	      let
	       val (goal_vars, goal_tm) = boolSyntax.strip_exists tm
	      in
               (* If the goal_tm exists among the conjs.. *)
	       if List.exists (fn tm' => term_eq tm tm') conjs
               (* ... then just use asm_rewrite_tac *)
	       then ASM_REWRITE_TAC[]

	       else
                (case List.find (fn (a,b) => term_eq goal_tm b) existvars_freeconjs of
                  SOME (exist_vars, match_conj) =>
                  (if null exist_vars
                   then
                    (* The goal can be directly given witnesses *)
                    (((map_every $ exists_tac) goal_vars) >> ASM_REWRITE_TAC[])
                   else
                    (* There is a matching assumption, but it has existentials in the wrong order. *)
                    let
                     val conj_index = Lib.index (fn (a,b) => term_eq goal_tm b) existvars_freeconjs

                     val matching_conjunct = el (conj_index+1) $ BODY_CONJUNCTS thm'

                     val sort_thm = RESORT_EXISTS_CONV (sort var_compare) tm
                    in
		     (qpat_x_assum ‘_’ (fn thm' => ALL_TAC) >>
		      assume_tac matching_conjunct >>
		      ASM_REWRITE_TAC [sort_thm] >>
		      (* TODO: The below needed? Above tactic should solve... *)
		      FULL_SIMP_TAC std_ss [] >>
		      (((map_every $ exists_tac) goal_vars) >> ASM_REWRITE_TAC[]))
                    end
                  )
                 (* TODO: Weird case: the conjunct has been rearranged somehow *)
                | NONE =>
		 let
		  val sort_thm = RESORT_EXISTS_CONV (sort var_compare) tm

		  val assum_exists_vars = flatten $ map fst existvars_freeconjs

		  val goal_vars' = List.filter (fn a => not $ List.exists (fn a' => term_eq a' a) assum_exists_vars) $ (sort var_compare) goal_vars
		 in
		  (ONCE_REWRITE_TAC [sort_thm] >>
		   ((map_every $ exists_tac) goal_vars') >>
		   ASM_REWRITE_TAC[])
		 end)
(* OLD
                 (((map_every $ exists_tac) goal_vars) >> ASM_REWRITE_TAC[]))
*)
	      end)
	    end)
 (* Should match conj_tac *)
           )
(* OLD
	    qpat_assum ‘_’ (fn thm' =>
	    let
	     val conjs = strip_conj $ concl thm'
	    in
	     goal_term (fn tm =>
	      let
	       val (goal_vars, goal_tm) = boolSyntax.strip_exists tm
	      in
               (* If the goal exists among the conjs.. *)
	       if List.exists (fn tm' => term_eq tm tm') conjs
               (* ... then just use asm_rewrite_tac *)
	       then
                ASM_REWRITE_TAC[]
               (* ... otherwise, provide witnesses in order *)
	       else (((map_every $ exists_tac) goal_vars) >> ASM_REWRITE_TAC[])
	      end)
	    end)
	   )
*)
(* OLDER
	   TRY (
	    rpt disch_tac >>
	    rpt (PAT_X_ASSUM “A /\ B” (fn thm => (STRIP_THM_THEN (fn thm' => ASSUME_TAC thm') thm))) >>
	    rpt (PAT_X_ASSUM “?a. _” (fn thm => (STRIP_THM_THEN (fn thm' => ASSUME_TAC thm') thm))) >>
	    res_tac >>
	    qexists_tac ‘n'’ >-
	    ASM_REWRITE_TAC[]
	   ) >>
	   ASM_SIMP_TAC bool_ss [] >>
	   metis_tac[]
*)
         else
         (* Simple case: no quantifiers. *)
         assume_tac thm >>
	 irule p4_contract_pre_str >>
	 exists_tac precond >>
	 fs[]));

(*
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
*)
    val _ = print ("Unifying contracts of path ID "^((Int.toString id)^".\n"))

(* Single application of insert_existentials:

val test1 = (zip path_cond_rest_tm_list (CONJUNCTS path_tree_list_leafs_thm))

length test1

val (path_cond_case, thm) = (el 1 test1);

(insert_existentials path_cond_tm) (path_cond_case, thm)

*)
    val new_p4_contracts = (LIST_CONJ (map (insert_existentials path_cond_tm) (zip path_cond_rest_tm_list (CONJUNCTS path_tree_list_leafs_thm))))
    val p4_contract_list_thm =
     if length path_tree_list_leafs = 1
     then
      PURE_REWRITE_RULE [SPEC path_cond_tm p4_contract_list_trivial_REWR] new_p4_contracts
     else
      PURE_REWRITE_RULE [SPEC path_cond_tm p4_contract_list_REWR2,
			 SPEC path_cond_tm p4_contract_list_GSYM_REWR,
			 SPEC path_cond_tm p4_contract_list_REWR,
			 APPEND] new_p4_contracts
(* DEBUG
    val _ = print (String.concat ["\nDone in ", (LargeInt.toString $ Time.toSeconds ((Time.now()) - time_start)), "s\n\n"]);
*)

   in
     MATCH_MP (MATCH_MP p4_symb_exec_unify_n_gen path_disj_thm) p4_contract_list_thm
   end
  | p4_unify_path_tree' id_ctthm_list (node (id, path_disj_thm, (h::t))) path_tree_list_leafs =
(* DEBUG:
(*
val orig_path_tree = path_tree;
(* To enter next layer of the tree using one of the next nodes: *)
val path_tree = h
(* Then repeatedly, (choosing the leftmost path): *)
val (node (id, path_disj_thm, (h::t))) = h;

(* get new h
val SOME h = get_node 19 path_tree;
val node_19 = h;
val (node (id, path_disj_thm, (h::t))) = h;

length t
*)

val (node (id, path_disj_thm, (h::t))) = path_tree;
val ctthm' = p4_unify_path_tree' id_ctthm_list h []
val path_tree_list_leafs = ([ctthm'])

val (node (id, path_disj_thm, (h::t))) = (node (id, path_disj_thm, t));
val ctthm' = p4_unify_path_tree' id_ctthm_list h []
val path_tree_list_leafs = (path_tree_list_leafs@[ctthm'])

(* Reset path_tree to go back to starting position: *)
val path_tree = orig_path_tree;
*)
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

(* TODO: Does this exist elsewhere? *)
fun varname_free_in_tm varname tm =
 not $ List.exists (fn varname' => varname' = varname) $ map (fst o dest_var) $ free_vars tm
;

fun make_new_precond path_cond init_astate =
 let
  val state_var = mk_var("s", type_of init_astate)
  val path_cond_tm = concl path_cond
 in
  if (varname_free_in_tm "s" path_cond_tm) andalso (varname_free_in_tm "s" init_astate)
  then mk_abs(state_var, mk_conj (concl path_cond, mk_eq (state_var, init_astate)))
  else raise (ERR "make_new_precond" ("Variable name s occupied in path condition or initial state."))
 end
;

(* TODO: Obtain tuple from contact_thm instead? *)
fun prove_contract' contract_thm (path_cond, init_astate, ctx_lhs, postcond) =
(* “^(mk_p4_contract' (make_new_precond path_cond init_astate, ctx_lhs, postcond))” *)
 prove (mk_p4_contract' (make_new_precond path_cond init_astate, ctx_lhs, postcond),
  assume_tac contract_thm >>
  (* TODO: fs really needed? *)
  fs[p4_contract_def, p4_contract'_def] >>
  (* Most proved at this point already, some need extra guidance *)
  exists_tac (mk_var("n", num)) >>
  ASM_REWRITE_TAC[]
 )
;

(*
(* TODO: Should be possible to add to these? Ugly if it has architecture-dependent stuff... *)
val p4_prove_postcond_rewr_thms = [packet_has_port_def, get_packet_def, packet_dropped_def, p4_v1modelTheory.v1model_is_drop_port_def];
*)


fun get_bits_of_v v =
 if is_v_bit v
 then fst $ dest_list $ fst $ dest_pair $ dest_v_bit v
 else if is_v_bool v
 then [dest_v_bool v]
 else if is_v_ext_ref v
 then []
 else if is_v_str v
 then []
 else if is_v_struct v
 then
  let
   val fields = dest_v_struct v
   val field_vs = map (snd o dest_pair) $ fst $ dest_list fields
   val field_bits = flatten $ map get_bits_of_v field_vs
  in
   field_bits
  end
 else if is_v_header v
 then
  let
   val (validity_bit, fields) = dest_v_header v
   val field_vs = map (snd o dest_pair) $ fst $ dest_list fields
   val field_bits = flatten $ map get_bits_of_v field_vs
  in
   (validity_bit::field_bits)
  end
 else if is_v_bot v
 then []
 else raise (ERR "get_bits_of_v" ("Unsupported v: "^(term_to_string v)))
;

fun p4_prove_wellformed_state astate wf_def =
 prove(“^(fst $ dest_comb $ fst $ dest_eq $ snd $ strip_forall $ concl wf_def) ^astate <=> T”,
  REWRITE_TAC [wf_def] >>
  goal_term (fn tm =>
  let
   val (vars, eqn) = strip_exists tm
   val (concrete_state, abstract_state) = dest_eq eqn
   val (aenv, g_scope_list, _, _) = dest_astate concrete_state
   val (block_index, io_list, io_list', ascope) = dest_aenv aenv
   val (ext_obj_index, ext_obj_map, v_map, ctrl) = p4_v1modelLib.dest_v1model_ascope ascope

   (* TODO: Fix this *)
   (* 1. Variables from ext_obj_map
    *    * Remaining input packet *)
(*
   val input_packet_tail_var = snd $ dest_comb $ fst $ sumSyntax.dest_inl $ snd $ dest_pair $ hd $ fst $ dest_list ext_obj_map
*)

   (* 2. Variables from v_map
    *    * Block parameters of V1Model *)
   val v_map_bits = flatten $ map get_bits_of_v $ (map (snd o dest_pair)) $ fst $ dest_list v_map

   (* 3. Variables from g_scope_list
    *    * Desugaring struct for apply results *)
   val g_scope_list_bits = get_bits_of_v $ fst $ dest_pair $ snd $ dest_pair $ hd $ fst $ dest_list $ hd $ fst $ dest_list g_scope_list
  in
(*
   exists_tac input_packet_tail_var >>
*)
   (map_every $ exists_tac) v_map_bits >>
   (map_every $ exists_tac) g_scope_list_bits
  end
  ) >>
  REWRITE_TAC[]
 )
;

(*
val astate = (optionSyntax.dest_some $ rhs $ snd $ dest_imp $ concl step_thm1)
prove(“p4_v1model_parser_wellformed ^astate <=> T”,
SIMP_TAC (bool_ss++(p4_wellformed_ss wf_def)) []
);
*)
local
fun wf_conv wf_def =
 let
  val wf_tm = fst $ dest_comb $ fst $ dest_eq $ snd $ strip_forall $ concl wf_def
 in
  {conv = K (K (fn tm => p4_prove_wellformed_state (snd $ dest_comb tm) wf_def)),
   key= SOME ([], mk_comb (wf_tm, mk_var ("astate", “:v1model_ascope astate”))),
   (* TODO: Better names *)
   name = "Prove wellformedness (v1model)",
   trace = 2}
 end
;

in
fun p4_wellformed_ss wf_def =
  SSFRAG {ac = [],
          congs = [],
          convs = [wf_conv wf_def],
          dprocs = [],
          filter = NONE,
          name = SOME "p4_wellformed_ss",
          rewrs = []};
end;

datatype defn_data =
   def_term of term
 | def_thm of thm;

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
 * postcond: the postcondition, a term which is a predicate on the architectural state
 *
 * postcond_rewr_thms: additional theorems used when proving the postcondition
 * 
 * postcond_simpset: additional simpset used when proving the postcondition *)
(* Note: precondition strengthening is probably not needed, since initial path condition is
 * provided freely *)
fun p4_symb_exec_prove_contract_gen p4_symb_exec_fun debug_flag arch_ty ctx_data (fty_map, b_fty_map, pblock_action_names_map) const_actions_tables path_cond_defs init_astate stop_consts_rewr stop_consts_never thms_to_add path_cond p4_is_finished_alt_opt n_max postcond postcond_rewr_thms postcond_simpset =
 let

  (* DEBUG *)
  val time_start = Time.now();

  val (ctx, ctx_def) =
   case ctx_data of
     def_term ctx_tm =>
    let
     val ctx_name = "ctx"
    in
     (ctx_tm, hd $ Defn.eqns_of $ Defn.mk_defn ctx_name (mk_eq(mk_var(ctx_name, type_of ctx_tm), ctx_tm)))
    end
   | def_thm ctx_def =>
    (rhs $ concl ctx_def, ctx_def)

  (* Perform symbolic execution until all branches are finished *)
  (* DEBUG *)
  (* val p4_symb_exec_fun = (p4_symb_exec 1); *)
  val (path_tree, path_cond_step_list) =
   p4_symb_exec_fun debug_flag arch_ty (ctx_def, ctx) (fty_map, b_fty_map, pblock_action_names_map) const_actions_tables path_cond_defs init_astate stop_consts_rewr stop_consts_never thms_to_add path_cond p4_is_finished_alt_opt n_max;

  (* DEBUG *)
  val time_res = Time.toSeconds ((Time.now()) - time_start)
  val _ = dbg_print debug_flag (String.concat ["\nFinished entire symbolic execution stage in ", (LargeInt.toString time_res), "s, trying to prove postcondition...\n\n"]);
  val time_start = Time.now();

  (* Prove postcondition holds for all resulting states in n-step theorems *)
  val id_step_post_thm_list =
   prove_postconds debug_flag postcond_rewr_thms postcond_simpset postcond path_cond_step_list
(*
   if debug_flag
   then
    let
     val (l', l'') = unzip $ map (fn (a,b,c) => (a, c)) path_cond_step_list
    in
     zip l' (prove_postconds_debug postcond_rewr_thms postcond l'')
    end
   else map (fn (a,b,c) => (a, prove_postcond postcond_rewr_thms postcond c)) path_cond_step_list
*)

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
  (* Fix contract format *)
  val ctx_lhs = lhs $ concl ctx_def
  val unified_ct_thm' = prove_contract' unified_ct_thm (path_cond, init_astate, ctx_lhs, postcond);

  (* DEBUG *)
  val _ = dbg_print debug_flag (String.concat ["\nFinished unification of all contracts in ", (LargeInt.toString $ Time.toSeconds ((Time.now()) - time_start)), "s.\n\n"]);

 in
  unified_ct_thm'
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

fun p4_debug_symb_exec arch_ty ctx_data (fty_map, b_fty_map, pblock_action_names_map) const_actions_tables path_cond_defs init_astate stop_consts_rewr stop_consts_never thms_to_add path_cond fuel =
 let
  val (ctx, ctx_def) =
   case ctx_data of
     def_term ctx_tm =>
    let
     val ctx_name = "ctx"
    in
     (ctx_tm, hd $ Defn.eqns_of $ Defn.mk_defn ctx_name (mk_eq(mk_var(ctx_name, type_of ctx_tm), ctx_tm)))
    end
   | def_thm ctx_def =>
    (rhs $ concl ctx_def, ctx_def)

  val (path_tree, state_list) = p4_symb_exec 1 true arch_ty (ctx_def, ctx) (fty_map, b_fty_map, pblock_action_names_map) const_actions_tables path_cond_defs init_astate stop_consts_rewr stop_consts_never thms_to_add path_cond NONE fuel
  val state_list_tms = map (fn (path_id, path_cond, step_thm) => (path_id, path_cond, dest_step_thm step_thm)) state_list
 in
  (path_tree, state_list_tms)
 end
;

fun p4_debug_symb_exec_frame_lists arch_ty ctx_data (fty_map, b_fty_map, pblock_action_names_map) const_actions_tables path_cond_defs init_astate stop_consts_rewr stop_consts_never thms_to_add path_cond fuel =
 let
  val (path_tree, state_list_tms) = p4_debug_symb_exec arch_ty ctx_data (fty_map, b_fty_map, pblock_action_names_map) const_actions_tables path_cond_defs init_astate stop_consts_rewr stop_consts_never thms_to_add path_cond fuel
  val arch_frame_list_tms = map (fn (path_id, path_cond, (tm1, tm2, tm3, tm4)) => tm3) state_list_tms
 in
  (path_tree, arch_frame_list_tms)
 end
;


(* From petr4_to_hol4p4.sml:
          val ab_list' = [``arch_block_inp``,
                  (el 1 ab_list), (* Parser *)
                  ``arch_block_ffbl "postparser"``,
                  (el 2 ab_list), (* VerifyChecksum *)
                  (el 3 ab_list), (* Ingress *)
                  (el 4 ab_list), (* Egress *)
                  (el 5 ab_list), (* ComputeChecksum *)
                  (el 6 ab_list), (* Deparser *)
                  ``arch_block_out``]
*)

(* "well-formedness" here means that the content of all the parts of the astate are in agreement
 * with those of a valid execution of a V1Model program, with the following additional assumptions:

 Both input and output lists are empty;
 No program-specific persistent externs exists.

*)

fun mk_v_bit_freevars (prefix, nbits) =
 let
  val bits = fixedwidth_freevars (prefix, nbits);
 in
   (fst $ dest_list bits, mk_v_bit $ mk_pair (bits, term_of_int nbits))
 end
;

fun mk_v_bit_freevars_fromindex (prefix, index, nbits) =
 let
  val bits = fixedwidth_freevars_fromindex (prefix, index, nbits);
 in
   (fst $ dest_list bits, mk_v_bit $ mk_pair (bits, term_of_int nbits))
 end
;

(*
(* The block name *)
val bname = “"p"”

val ab_list = “[arch_block_inp;
  arch_block_pbl "p"
    [e_var (varn_name "b"); e_var (varn_name "parsedHdr");
     e_var (varn_name "meta"); e_var (varn_name "standard_metadata")];
  arch_block_ffbl "postparser";
  arch_block_pbl "vrfy" [e_var (varn_name "hdr"); e_var (varn_name "meta")];
  arch_block_pbl "ingress"
    [e_var (varn_name "hdr"); e_var (varn_name "meta");
     e_var (varn_name "standard_metadata")];
  arch_block_pbl "egress"
    [e_var (varn_name "hdr"); e_var (varn_name "meta");
     e_var (varn_name "standard_metadata")];
  arch_block_pbl "update" [e_var (varn_name "hdr"); e_var (varn_name "meta")];
  arch_block_pbl "deparser" [e_var (varn_name "b"); e_var (varn_name "hdr")];
  arch_block_out]”

val pblock_tymap = symb_exec1_pblock_tymap;
*)

(* TODO: This must ensure no accidental duplicate free variables are formed.
 * Simplest way is to use common prefix + passing current fv index *)
(*
val prefix = "a"
val fv_index = 0
val name_tau = “("row",
		 tau_xtl struct_ty_struct
		   [("e",tau_bit 8); ("t",tau_bit 16); ("l",tau_bit 8);
		    ("r",tau_bit 8); ("v",tau_bit 8)])”
free_vars_v_of_name_tau "a" 0 name_tau
*)

fun free_vars_v_of_name_tau prefix fv_index name_tau =
 let
  val (name, tau) = dest_pair name_tau
 in
  if is_tau_bit tau
  then
   let
    val width = dest_tau_bit tau
   in
    (fv_index+width, mk_pair (name, snd $ mk_v_bit_freevars_fromindex (prefix, fv_index, width)))
   end
  else if is_tau_xtl tau
  then
   let
    val (struct_ty, struct_elems) = dest_tau_xtl tau
   in
     if is_struct_ty_struct struct_ty
     then
      let
       val (fv_index', name_vs) = free_vars_v_of_name_tau_list prefix fv_index (fst $ dest_list struct_elems)
      in
       (fv_index', mk_pair (name, mk_v_struct $ mk_list (name_vs, mk_prod (string_ty, v_ty))))
      end
     else if is_struct_ty_header struct_ty
     then
      let
       val (fv_index', name_vs) = free_vars_v_of_name_tau_list prefix (fv_index+1) (fst $ dest_list struct_elems)
      in
       (fv_index', mk_pair (name, mk_v_header (mk_var (prefix^(Int.toString (fv_index)), bool), mk_list (name_vs, mk_prod (string_ty, v_ty)))))
      end
     else raise (ERR "free_vars_v_of_tau" ("Unsupported struct_ty: "^(term_to_string struct_ty)))
   end
  else raise (ERR "free_vars_v_of_tau" ("Unsupported tau: "^(term_to_string tau)))
 end
and free_vars_v_of_name_tau_list prefix fv_index [] = (fv_index, [])
  | free_vars_v_of_name_tau_list prefix fv_index (h::t) =
 let
  val (fv_index', name_v) = free_vars_v_of_name_tau prefix fv_index h
  val (fv_index'', name_vs) = free_vars_v_of_name_tau_list prefix fv_index' t
 in
  (fv_index'', name_v::name_vs)
 end
;

(* TODO: Feedback for all failure cases *)
fun free_vars_vs_of_bargs bname ab_list pblock_tymap =
 let
  (* Get the arg names from the block name and ab_list *)
  (* TODO: Hack *)
  val bargs_opt = rhs $ concl $ EVAL “case FIND (\ab. case ab of arch_block_pbl bname bargs => if bname = ^bname then T else F | _ => F) ^ab_list of
	| SOME (arch_block_pbl bname bargs) => SOME bargs
	| _ => NONE”
  val bargnames = mk_list (map (dest_varn_name o dest_e_var) $ fst $ dest_list $ dest_some bargs_opt, string_ty)

  val pblock_tys_opt = rhs $ concl $ EVAL “ALOOKUP ^pblock_tymap ^bname”

  val pblock_tys = dest_some pblock_tys_opt

  val bargname_tau_list = rhs $ concl $ EVAL “ZIP (^bargnames, ^pblock_tys)”

  val bargname_tau_list' = List.filter (not o is_tau_ext o snd o dest_pair) $ fst $ dest_list bargname_tau_list
  (* TODO: "a" is a temporary solution: what prefixes to use? Remember this gets existentially
   * quantified later... *)
  val bargname_v_list = mk_list (snd $ free_vars_v_of_name_tau_list "b" 0 bargname_tau_list', mk_prod (string_ty, v_ty))
 in
  bargname_v_list
 end
;

val v1model_standard_metadata_name_ty =
 “("standard_metadata",
   tau_xtl struct_ty_struct
     [("ingress_port",tau_bit 9); ("egress_spec",tau_bit 9);
      ("egress_port",tau_bit 9); ("instance_type",tau_bit 32);
      ("packet_length",tau_bit 32); ("enq_timestamp",tau_bit 32);
      ("enq_qdepth",tau_bit 19); ("deq_timedelta",tau_bit 32);
      ("deq_qdepth",tau_bit 19); ("ingress_global_timestamp",tau_bit 48);
      ("egress_global_timestamp",tau_bit 48); ("mcast_grp",tau_bit 16);
      ("egress_rid",tau_bit 16); ("checksum_error",tau_bit 1);
      ("parser_error",tau_bit 32); ("priority",tau_bit 3)])”
;

(* TODO: Make this work for case of remaining input *)
fun get_v1model_wellformed_defs actx init_astate block_index_stop =
 let
  (* Obtain the function maps for generating star variables *)
  val (_, _, _, input_f, _, _, _, _, ext_fun_map, func_map) = dest_actx actx

  (* Obtain the control plane configuration from the initial state - this is used directly
   * for the intermediate state *)
  val aenv = #1 $ dest_astate init_astate
  val ascope = #4 $ dest_aenv aenv
  val ctrl = #4 $ p4_v1modelLib.dest_v1model_ascope ascope

  (* TODO: V1Model hack *)
  val (tau1_v, tau2_v) = dest_pair $ snd $ dest_comb input_f
  val tau1 = dest_some $ rhs $ concl $ EVAL “v_to_tau ^tau1_v”
  val tau2 = dest_some $ rhs $ concl $ EVAL “v_to_tau ^tau2_v”

  val fv_prefix = "b"

  (* Start filling v_map up with the platform-specific variables *)
  val (pe_free_vars, pe_v) = mk_v_bit_freevars (fv_prefix, 32)
  val (fv_index, sm_name_v) = free_vars_v_of_name_tau fv_prefix 32 v1model_standard_metadata_name_ty
  val (fv_index', ph_name_v) = free_vars_v_of_name_tau fv_prefix fv_index (mk_pair(fromMLstring "parsedHdr" , tau1))
  val (fv_index'', h_name_v) = free_vars_v_of_name_tau fv_prefix fv_index' (mk_pair(fromMLstring "hdr" , tau1))
  val (fv_index''', m_name_v) = free_vars_v_of_name_tau fv_prefix fv_index'' (mk_pair(fromMLstring "meta" , tau2))

  val v_map' = mk_list ([mk_pair (fromMLstring "parseError", pe_v),
                         mk_pair (fromMLstring "b", mk_v_ext_ref $ term_of_int 0),
                         mk_pair (fromMLstring "b_temp", mk_v_ext_ref $ term_of_int 1),
                         sm_name_v, ph_name_v, h_name_v, m_name_v],
                        mk_prod (string_ty, v_ty))

  (* Note: Should agree with updates of initialise_var_stars_def to global scope in exec sem *)
  val var_stars = rhs $ concl $ EVAL “(var_star_updates_of_func_map ^func_map)++(var_star_updates_of_ext_map ^ext_fun_map)”

  (* Note: Apply result desugaring variable is hard-coded into the architecture models *)
  val hit_var = mk_var("hit", bool)
  val miss_var = mk_var("miss", bool)
  val (ar_free_vars, ar_v) = mk_v_bit_freevars ("r", 32)
  val gen_apply_result_var = “(varn_name "gen_apply_result",
             v_struct
               [("hit",v_bool ^hit_var); ("miss",v_bool ^miss_var);
                ("action_run", ^ar_v)],
             NONE:lval option)”

  val g_scope_list' = mk_list ([mk_cons (gen_apply_result_var, var_stars)], scope_ty)

  (* TODO: Make this work for ctrl tables that are not constants *)
(* OLD
  val def_free_vars = [“packet_tail:bool list”]@(fst $ dest_list $ fixedwidth_freevars (fv_prefix, fv_index'''))@[hit_var, miss_var]@ar_free_vars
*)
  val def_free_vars = (fst $ dest_list $ fixedwidth_freevars (fv_prefix, fv_index'''))@[hit_var, miss_var]@ar_free_vars
 in
  (* TODO: Adjust block index for the block in question, adjust extern map? *)
  Defn.mk_defn "p4_v1model_parser_wellformed"
   “p4_v1model_parser_wellformed astate <=>
     ^(list_mk_exists(def_free_vars, 
     “(astate:v1model_ascope astate) =
     ((^block_index_stop, [], [], (2, [(0,INL (core_v_ext_packet [])); (1,INL (core_v_ext_packet []))], ^v_map', ^ctrl)), ^g_scope_list', arch_frame_list_empty, status_running)”))”
 end
;

val (p4_v1model_lookup_avar_validity_tm,  mk_p4_v1model_lookup_avar_validity, dest_p4_v1model_lookup_avar_validity, is_p4_v1model_lookup_avar_validity) =
  syntax_fns2 "p4_symb_exec" "p4_v1model_lookup_avar_validity";

val (p4_v1model_lookup_avar_tm,  mk_p4_v1model_lookup_avar, dest_p4_v1model_lookup_avar, is_p4_v1model_lookup_avar) =
  syntax_fns2 "p4_symb_exec" "p4_v1model_lookup_avar";

(* postcond is the postcondition of the contract preceding the intermediate state *)
fun get_intermediate_state postcond wf_def =
 let
  val (state_var, predicate) = dest_abs postcond
  val conjs = strip_conj predicate
  val usable_conjs = List.filter (fn conj => if is_eq conj then ((fn tm => (is_p4_v1model_lookup_avar tm) orelse (is_p4_v1model_lookup_avar_validity tm)) $ lhs conj) else false) conjs
  val gen_usable_conjs = map (fn conj => mk_abs (state_var, conj)) usable_conjs

  val init_astate = rhs $ snd $ strip_exists $ rhs $ snd $ dest_forall $ concl wf_def

  val comb_usable_conjs = map (fn conj => mk_comb (conj, init_astate)) gen_usable_conjs
  (* TODO: EVAL - use HOL4P4_CONV? *)
  val comb_usable_conjs' = map EVAL comb_usable_conjs
  val comb_usable_conjs'' = map (strip_conj o rhs o concl) comb_usable_conjs'

  val subst_eqs = map (fn eqn => if is_eq eqn
                                 then let val (a,b) = dest_eq eqn in (a |-> b) end
                                 else if is_neg eqn
                                      then ((dest_neg eqn) |-> F)
                                      else (eqn |-> T)) $ flatten comb_usable_conjs''
  val init_astate' = subst subst_eqs init_astate
 in
  init_astate'
 end
;

(* This takes two contracts in p4_contract' formulation, and composes them sequentially.
 * wellformed_def is a definition stating the intermediate state is well-formed *)
(* TODO: This can still be made more efficient *)
fun p4_combine_contracts contract1 contract2 wellformed_def =
 let
  val (pre1, ctx1, post1) = dest_p4_contract' $ concl contract1
  val (pre2, ctx2, post2) = dest_p4_contract' $ concl contract2

  val init_state1 = snd $ dest_eq $ hd $ rev $ strip_conj $ snd $ dest_abs pre1
 in
 (* “^(mk_p4_contract' (pre1, ctx2, post2))” *)
  prove(mk_p4_contract' (pre1, ctx1, post2),
  (let
    val gen_contract2 = (hol88Lib.GEN_ALL contract2)
    val vars = fst $ strip_forall $ concl $ gen_contract2
   in
    assume_tac contract1 >>
(*
    qpat_x_assum ‘!vars. _’ (fn thm => markerLib.ABBREV_TAC “contract2 = ^(concl thm)”) >>
    qpat_x_assum ‘Abbrev (contract2 = _)’ (fn thm => markerLib.hide_tac "hide_contract2" thm) >>

    goal_term (fn tm => markerLib.ABBREV_TAC “goal = ^tm”) >>
    qpat_x_assum ‘Abbrev (goal = _)’ (fn thm => markerLib.hide_tac "goal_hide" thm) >>

    rpt (qpat_x_assum ‘?vars. _’ (fn thm => CHOOSE_TAC thm)) >>
*)
    (* Somehow massively more efficient than REWRITE_TAC... *)
    EVERY_ASSUM (fn thm => PAT_X_ASSUM (concl thm) (fn thm => ASSUME_TAC $ REWRITE_RULE [p4_contract'_alt_shape] thm)) >>
    EVERY_ASSUM (fn thm => PAT_X_ASSUM (concl thm) (fn thm => ASSUME_TAC $ REWRITE_RULE [wellformed_def] thm)) >>
    SIMP_TAC bool_ss [p4_contract'_alt_shape] >>
    (* Simplify the first contract *)
    qpat_x_assum ‘!s. _’ (fn thm => assume_tac (SPEC init_state1 thm)) >>
    qpat_x_assum ‘A ==> B’ (fn thm => assume_tac (REWRITE_RULE [(EVAL_CONV $ fst $ dest_imp $ concl thm)] thm)) >>
    FULL_SIMP_TAC pure_ss [] >>
    qpat_x_assum ‘P s'’ (fn thm => assume_tac (REWRITE_RULE [(EVAL_CONV $ concl thm)] thm)) >>
    (**********************************************)
    (* Construction of the intermediate state s'  *)

    (* Split up conjoined assumptions *)
    rpt (qpat_x_assum ‘A /\ B’ (fn thm => assume_tac (CONJUNCT1 thm) >> assume_tac (CONJUNCT2 thm))) >>
    (* Eliminate existentially quantified variables *)
    rpt (qpat_x_assum ‘?vars. _’ (fn thm => CHOOSE_TAC thm)) >>

    qpat_x_assum ‘s' = _’ (fn thm => FULL_SIMP_TAC bool_ss [thm]) >>
    (* Use all assumptions on looked-up L-values *)
    rpt (qpat_x_assum ‘p4_v1model_lookup_avar _ _ = _’ (fn thm => (FULL_SIMP_TAC bool_ss [EVAL_RULE thm]))) >>
    (* Use all assumptions on validity bits *)
    rpt (qpat_x_assum ‘p4_v1model_lookup_avar_validity _ _ = _’ (fn thm => (FULL_SIMP_TAC bool_ss [EVAL_RULE thm]))) >>
    
    (* Introduce the second contract *)
    qpat_assum ‘arch_multi_exec _ _ _ = _’ (fn thm => assume_tac $ SPECL (free_vars_lr $ rhs $ concl thm) gen_contract2) >>
    FULL_SIMP_TAC std_ss [p4_contract'_alt_shape]
   end) >> (
    (* Combine the two executions *)
    qexistsl_tac [‘n + n'’, ‘s'’] >>
    rfs[] >>
    PairCases_on ‘s'’ >>
    irule arch_multi_exec_comp_n_tl >>
(* OLD
    (* Use constraints on middle state:
     * Currently, this looks for all instances of p4_v1model_lookup_avar, and validity version. *)
    (* TODO: Use HOL4P4_CONV? *)
    rpt (qpat_x_assum ‘p4_v1model_lookup_avar _ _ = _’ (fn thm => ASSUME_TAC $ EVAL_RULE thm)) >>
    rpt (qpat_x_assum ‘p4_v1model_lookup_avar_validity _ _ = _’ (fn thm => ASSUME_TAC $ EVAL_RULE thm)) >>
*)
    FULL_SIMP_TAC std_ss []
   )
  )
      
(* TODO: See if you can use abbreviations anywhere...
   markerLib.ABBREV_TAC “init_state1 = ^init_state1” >>
   qpat_x_assum ‘Abbrev (init_state1 = _)’ (fn thm => markerLib.hide_tac "hide_init_state1" thm) >>

     markerLib.unhide_tac "hide_init_state1" >>
     markerLib.UNABBREV_TAC "init_state1" >>
*)
 end
;

end
