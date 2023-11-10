open HolKernel boolLib liteLib simpLib Parse bossLib;

open pairSyntax listSyntax optionSyntax computeLib hurdUtils;

open p4Theory p4_exec_semTheory p4Syntax p4_exec_semSyntax;

open evalwrapLib p4_testLib;

val _ = new_theory "p4_symb_exec";
(* TODO: Rename "branch condition"? *)

val ERR = mk_HOL_ERR "p4_symb_exec"

(* Checking if a conditional statement is about to be reduced
 * to one of its two statement constituents *)


Definition stmt_get_cond_def:
 stmt_get_cond stmt =
  case stmt of
  | stmt_empty => NONE
  | stmt_ass lval e => NONE
  | stmt_cond e stmt' stmt'' =>
   SOME e
  | stmt_block t_scope stmt' =>
   stmt_get_cond stmt'
  | stmt_ret e => NONE
  | stmt_seq stmt' stmt'' =>
   stmt_get_cond stmt'
  | stmt_trans e => NONE
  | stmt_app x e_l => NONE
  | stmt_ext => NONE
End
(* OLD
Definition e_get_next_subexp_def:
 (e_get_next_subexp e =
   case e of
   | e_v v => NONE
   | e_var varn => SOME (e_var varn)
   | e_list e_l =>
    (case e_l_get_next_subexp e_l of
     | NONE => SOME (e_list e_l)
     | SOME e' => SOME e')
   | e_acc e' x =>
    (case e_get_next_subexp e' of
     | NONE => SOME (e_acc e' x)
     | SOME e'' => SOME e'')
   | e_unop unop e' =>
    (case e_get_next_subexp e' of
     | NONE => SOME (e_unop unop e')
     | SOME e'' => SOME e'')
   | e_cast cast e' =>
    (case e_get_next_subexp e' of
     | NONE => SOME (e_cast cast e')
     | SOME e'' => SOME e'')
   | e_binop e' binop e'' =>
    (case e_get_next_subexp e' of
     | NONE =>
      if is_short_circuitable binop
      then SOME (e_binop e' binop e'')
      else
       (case e_get_next_subexp e'' of
        | NONE =>
         SOME (e_binop e' binop e'')
        | SOME e''' => SOME e''')
     | SOME e''' => SOME e''')
   | e_concat e' e'' =>
    (case e_get_next_subexp e' of
     | NONE =>
      (case e_get_next_subexp e'' of
       | NONE =>
        SOME (e_concat e' e'')
       | SOME e''' => SOME e''')
     | SOME e''' => SOME e''')
   | e_slice e' e'' e''' =>
    (case e_get_next_subexp e' of
     | NONE =>
      (case e_get_next_subexp e'' of
       | NONE =>
        (case e_get_next_subexp e''' of
         | NONE =>
          SOME (e_slice e' e'' e''')
         | SOME e'''' => SOME e'''')
       | SOME e'''' => SOME e'''')
     | SOME e'''' => SOME e'''')
   | e_call funn e_l =>
    (case e_l_get_next_subexp e_l of
     | NONE => SOME (e_call funn e_l)
     | SOME e' => SOME e')
   | e_select e' v_x_l x =>
    (case e_get_next_subexp e' of
     | NONE => SOME (e_select e' v_x_l x)
     | SOME e'' => SOME e'')
   | e_struct x_e_l =>
    (case e_l_get_next_subexp $ (MAP SND) x_e_l of
     | NONE => SOME (e_struct x_e_l)
     | SOME e' => SOME e')
   | e_header boolv x_e_l =>
    (case e_l_get_next_subexp $ (MAP SND) x_e_l of
     | NONE => SOME (e_header boolv x_e_l)
     | SOME e' => SOME e')) /\
 (e_l_get_next_subexp [] = NONE) /\
 (e_l_get_next_subexp (h::t) = 
  (case e_get_next_subexp h of
   | NONE => e_l_get_next_subexp t
   | SOME e' => SOME e'))
Termination
cheat
End

Definition list_get_next_e_def:
 (list_get_next_e [] = NONE) /\
 (list_get_next_e (h::t) = 
  (case h of
   | e_v v => list_get_next_e t
   | e' => SOME e'))
End

Definition stmt_get_next_e_def:
 stmt_get_next_e stmt =
  case stmt of
  | stmt_empty => NONE
  | stmt_ass lval e => SOME e
  | stmt_cond e stmt' stmt'' =>
   SOME e
  | stmt_block t_scope stmt' =>
   stmt_get_next_e stmt'
  | stmt_ret e => SOME e
  | stmt_seq stmt' stmt'' =>
   stmt_get_next_e stmt'
  | stmt_trans e => SOME e
  | stmt_app x e_l =>
   list_get_next_e e_l
  | stmt_ext => NONE
End

Definition stmt_get_next_e_subexp_def:
 stmt_get_next_e_subexp stmt =
  case stmt_get_next_e stmt of
  | SOME e => e_get_next_subexp e
  | NONE => NONE
End

(*
val branch_cond_opt = rhs $ concl $ EVAL “stmt_get_cond (stmt_cond
               (e_binop (e_v (v_bit ([e1; e2; e3; e4; e5; e6; e7; e8],8)))
                  binop_lt (e_v (v_bit ([T; F; F; F; F; F; F; F],8))))
               (stmt_ass
                  (lval_field (lval_varname (varn_name "standard_meta"))
                     "egress_spec")
                  (e_v (v_bit ([F; F; F; F; F; F; F; F; T],9))))
               (stmt_ass
                  (lval_field (lval_varname (varn_name "standard_meta"))
                     "egress_spec")
                  (e_v (v_bit ([F; F; F; F; F; F; F; T; F],9)))))”;

next_e_has_free_vars “(e_binop
                    (e_acc
                       (e_v
                          (v_struct
                             [("e",v_bit ([e1; e2; e3; e4; e5; e6; e7; e8],8));
                              ("t",
                               v_bit
                                 ([F; F; F; T; F; F; F; T; F; F; F; T; F; F;
                                   F; T],16));
                              ("l",v_bit ([F; F; F; F; F; F; F; F],8));
                              ("r",v_bit ([F; F; F; F; F; F; F; F],8));
                              ("v",v_bit ([T; F; T; T; F; F; F; F],8))])) "e")
                    binop_lt (e_v (v_bit ([T; F; F; F; F; F; F; F],8))))”

*)
*)
Definition astate_get_top_stmt_def:
 astate_get_top_stmt ((aenv, g_scope_list, arch_frame_list, status):'a astate) =
  case arch_frame_list of
  | arch_frame_list_empty => NONE
  | arch_frame_list_regular frame_list =>
   (case frame_list of
    | [] => NONE
    | ((funn, stmt_stack, scope_list)::t) =>
     (case stmt_stack of
      | [] => NONE
      | (h'::t') => SOME h'
     )
   )
End

Definition astate_get_cond_def:
 astate_get_cond astate =
  case astate_get_top_stmt astate of
  | SOME stmt => stmt_get_cond stmt
  | NONE => NONE
End

(*
Definition astate_get_next_e_subexp_def:
 astate_get_next_e_subexp astate =
  case astate_get_top_stmt astate of
  | SOME stmt => stmt_get_next_e_subexp stmt
  | NONE => NONE
End

Definition astate_get_next_e_def:
 astate_get_next_e astate =
  case astate_get_top_stmt astate of
  | SOME stmt => stmt_get_next_e stmt
  | NONE => NONE
End

Definition is_cond_red_next_def:
 is_cond_red_next stmt =
  case stmt_get_cond stmt of
  | SOME cond => T
  | NONE => F
End
*)

(* TODO: The below two are also found in p4_testLib.sml - put elsewhere? *)
(* TODO: For some reason, step_thm sometimes has an antecedent, sometimes not. Find out
 * what's going on and unify the form. *)
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
fun dest_actx actx =
 case spine_pair actx of
    [ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_fun_map, func_map] => (ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_fun_map, func_map)
  | _ => raise (ERR "dest_actx" ("Invalid actx shape: "^(term_to_string actx)))
;
fun dest_astate astate =
 case spine_pair astate of
    [aenv, g_scope_list, arch_frame_list, status] => (aenv, g_scope_list, arch_frame_list, status)
  | _ => raise (ERR "dest_astate" ("Invalid astate shape: "^(term_to_string astate)))
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

(* TODO: Definition a HOL4 function for this for now, would be a pain in the ass otherwise *)
Definition get_b_func_map_def:
 get_b_func_map i ab_list pblock_map =
  case EL i ab_list of
  | (arch_block_pbl f e_l) =>
   (case ALOOKUP pblock_map f of
    | SOME (pblock_regular pbl_type b_func_map t_scope pars_map tbl_map) =>
     SOME b_func_map
    | NONE => NONE)
  | _ => NONE
End

fun get_b_func_map i ab_list pblock_map =
 rhs $ concl $ EVAL “get_b_func_map ^i ^ab_list ^pblock_map”
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
  if is_some b_func_map_opt
  then (func_map, dest_some b_func_map_opt, ext_fun_map)
  else (func_map, “[]:b_func_map”, ext_fun_map)
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

(* TODO: This needs a map between function names and the directions of their parameters *)
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

(*
fun next_e_has_free_vars e =
 if is_e_v e
 then not $ null $ free_vars e
 else if is_e_var e
 then false
 else if is_e_list e
 then
  let
   val e_list = dest_e_list e
  in
   next_e_has_free_vars_list (dest_list e_list)
  end
 else if is_e_acc e
 then
  let
   val (e', x) = dest_e_acc e
  in
   (* We can always allow field access to proceed *)
   if is_e_v e'
   then false
   else next_e_has_free_vars e'
  end
 else if is_e_unop e
 then
  let
   val (unop, e') = dest_e_unop e
  in
   next_e_has_free_vars e'
  end
 else if is_e_cast e
 then
  let
   val (cast, e') = dest_e_cast e
  in
   (* We can always allow cast to proceed *)
   if is_e_v e'
   then false
   else next_e_has_free_vars e'
  end
 else if is_e_binop e
 then
  let
   val (e', binop, e'') = dest_e_binop e
  in
   if is_e_v e'
   then next_e_has_free_vars e'
   else next_e_has_free_vars e''
  end
 else if is_e_concat e
 then
  let
   val (e', e'') = dest_e_concat e
  in
   (* We can always allow concat to proceed *)
   if is_e_v e'
   then
    if is_e_v e''
    then false
    else next_e_has_free_vars e''
   else next_e_has_free_vars e'
  end
 else if is_e_slice e
 then
  let
   val (e', e'', e''') = dest_e_slice e
  in
   (* We can allow slice to proceed if indices have no free variables *)
   if is_e_v e'
   then
    if is_e_v e''
    then
     if is_e_v e'''
     then next_e_has_free_vars e'' orelse next_e_has_free_vars e'''
     else next_e_has_free_vars e'''
    else next_e_has_free_vars e''
   else next_e_has_free_vars e'
  end
 else if is_e_call e
 then
  let
   val (funn, e_list) = dest_e_call e
  in
   next_e_has_free_vars_list (fst $ dest_list e_list)
  end
 else if is_e_select e
 then
  let
   val (e', v_x_list, x) = dest_e_select e
  in
   next_e_has_free_vars e'
  end
 else if is_e_struct e
 then
  let
   val x_e_list = dest_e_struct e
  in
   next_e_has_free_vars_list ((map (snd o dest_pair)) $ fst $ dest_list x_e_list)
  end
 else if is_e_header e
 then
  let
   val (boolv, x_e_list) = dest_e_header e
  in
   next_e_has_free_vars_list ((map (snd o dest_pair)) $ fst $ dest_list x_e_list)
  end
 else raise (ERR "next_e_has_free_vars" ("Unsupported expression: "^(term_to_string e)))
and next_e_has_free_vars_list []     = false
  | next_e_has_free_vars_list (h::t) =
   if next_e_has_free_vars h
   then true
   else next_e_has_free_vars_list t
;
*)

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

(* TEST *)
val branch_cond = “(e_binop (e_v (v_bit ([e1; e2; e3; e4; e5; e6; e7; e8],8)))
                    binop_lt (e_v (v_bit ([T; F; F; F; F; F; F; F],8))))”;

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
(* TODO: Add more constants to RESTR_EVAL_CONV? *)
fun p4_should_branch step_thm =
 let
  val astate = the_final_state_imp step_thm
  val branch_cond_opt = rhs $ concl $ RESTR_EVAL_CONV p4_stop_eval_consts “astate_get_cond ^astate”
 in
  if is_some branch_cond_opt
  then
   let
    val branch_cond = dest_some branch_cond_opt
   in
    if is_e_v branch_cond andalso not $ null $ free_vars branch_cond
    then SOME (dest_v_bool $ dest_e_v branch_cond)
    else NONE
   end
  else NONE
 end
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
      val path_cond_pos = CONJ path_cond (ASSUME (mk_eq (branch_cond, T)))
      val path_cond_neg = CONJ path_cond (ASSUME (mk_eq (branch_cond, F)))
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

(* Test area *)

val symb_exec1_actx = ``([arch_block_inp;
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
  arch_block_out],
 [("p",
   pblock_regular pbl_type_parser
     [("p",stmt_seq stmt_empty (stmt_trans (e_v (v_str "start"))),
       [("b",d_none); ("h",d_out); ("m",d_inout); ("sm",d_inout)])] []
     [("start",
       stmt_seq
         (stmt_ass lval_null
            (e_call (funn_ext "packet_in" "extract")
               [e_var (varn_name "b"); e_acc (e_var (varn_name "h")) "h"]))
         (stmt_trans (e_v (v_str "accept"))))] []);
  ("vrfy",
   pblock_regular pbl_type_control
     [("vrfy",stmt_seq stmt_empty stmt_empty,[("h",d_inout); ("m",d_inout)])]
     [] [] []);
  ("update",
   pblock_regular pbl_type_control
     [("update",stmt_seq stmt_empty stmt_empty,[("h",d_inout); ("m",d_inout)])]
     [] [] []);
  ("egress",
   pblock_regular pbl_type_control
     [("egress",stmt_seq stmt_empty stmt_empty,
       [("h",d_inout); ("m",d_inout); ("sm",d_inout)])] [] [] []);
  ("deparser",
   pblock_regular pbl_type_control
     [("deparser",
       stmt_seq stmt_empty
         (stmt_ass lval_null
            (e_call (funn_ext "packet_out" "emit")
               [e_var (varn_name "b"); e_acc (e_var (varn_name "h")) "h"])),
       [("b",d_none); ("h",d_in)])] [] [] []);
  ("ingress",
   pblock_regular pbl_type_control
     [("ingress",
       stmt_seq stmt_empty
         (stmt_cond
            (e_binop
               (e_acc (e_acc (e_acc (e_var (varn_name "h")) "h") "row") "e")
               binop_lt (e_v (v_bit ([T; F; F; F; F; F; F; F],8))))
            (stmt_ass
               (lval_field (lval_varname (varn_name "standard_meta"))
                  "egress_spec")
               (e_v (v_bit ([F; F; F; F; F; F; F; F; T],9))))
            (stmt_ass
               (lval_field (lval_varname (varn_name "standard_meta"))
                  "egress_spec")
               (e_v (v_bit ([F; F; F; F; F; F; F; T; F],9))))),
       [("h",d_inout); ("m",d_inout); ("standard_meta",d_inout)])] [] [] [])],
 [("postparser",ffblock_ff v1model_postparser)],
 v1model_input_f
   (v_struct
      [("h",
        v_header ARB
          [("row",
            v_struct
              [("e",v_bit ([ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB],8));
               ("t",
                v_bit
                  ([ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB;
                    ARB; ARB; ARB; ARB; ARB],16));
               ("l",v_bit ([ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB],8));
               ("r",v_bit ([ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB],8));
               ("v",v_bit ([ARB; ARB; ARB; ARB; ARB; ARB; ARB; ARB],8))])])],
    v_struct []),v1model_output_f,v1model_copyin_pbl,v1model_copyout_pbl,
 v1model_apply_table_f,
 [("header",NONE,
   [("isValid",[("this",d_in)],header_is_valid);
    ("setValid",[("this",d_inout)],header_set_valid);
    ("setInvalid",[("this",d_inout)],header_set_invalid)]);
  ("",NONE,
   [("mark_to_drop",[("standard_metadata",d_inout)],v1model_mark_to_drop);
    ("verify",[("condition",d_in); ("err",d_in)],v1model_verify)]);
  ("packet_in",NONE,
   [("extract",[("this",d_in); ("headerLvalue",d_out)],
     v1model_packet_in_extract);
    ("lookahead",[("this",d_in); ("targ1",d_in)],v1model_packet_in_lookahead);
    ("advance",[("this",d_in); ("bits",d_in)],v1model_packet_in_advance)]);
  ("packet_out",NONE,
   [("emit",[("this",d_in); ("data",d_in)],v1model_packet_out_emit)]);
  ("register",
   SOME
     ([("this",d_out); ("size",d_none); ("targ1",d_in)],register_construct),
   [("read",[("this",d_in); ("result",d_out); ("index",d_in)],register_read);
    ("write",[("this",d_in); ("index",d_in); ("value",d_in)],register_write)])],
 [("NoAction",stmt_seq stmt_empty (stmt_ret (e_v v_bot)),[])]):v1model_ascope actx``;

val symb_exec1_astate = rhs $ concl $ EVAL “(p4_append_input_list [([F; F; F; F; F; F; F; T; F; F; F; T; F; F; F; T; F; F; F; T; F; F; F; T; F;
   F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; T; F; T; T; F; F; F; F],0);
 ([F; F; F; F; F; F; T; F; F; F; F; T; F; F; F; T; T; F; F; F; F; F; F; T; F;
   F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; T; F; T; T; F; F; F; F],0);
 ([T; T; T; T; F; F; T; T; F; F; F; T; F; F; F; F; F; F; F; F; F; F; F; F; F;
   F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; T; F; T; T; F; F; F; F],0);
 ([T; T; T; T; F; T; F; F; F; F; F; T; F; F; F; T; F; F; F; T; F; F; F; T; F;
   F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; T; F; T; T; F; F; F; F],0)] (((0,[],[],ARB,ARB,ARB,[]),[[]],arch_frame_list_empty,status_running):v1model_ascope astate))”;

(* eval_under_assum: *)
GEN_ALL $ eval_under_assum p4_v1modelLib.v1model_arch_ty symb_exec1_actx symb_exec1_astate [] [] (ASSUME T) 10;

val symb_exec1_astate_symb = rhs $ concl $ EVAL “(p4_append_input_list [([e1; e2; e3; e4; e5; e6; e7; e8; F; F; F; T; F; F; F; T; F; F; F; T; F; F; F; T; F;
   F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; T; F; T; T; F; F; F; F],0)] (((0,[],[],ARB,ARB,ARB,[]),[[]],arch_frame_list_empty,status_running):v1model_ascope astate))”;

(* symb_exec: *)
(* Parameter assignment for debugging: *)
val arch_ty = p4_v1modelLib.v1model_arch_ty
val ctx = symb_exec1_actx
val init_astate = symb_exec1_astate_symb
val stop_consts_rewr = []
val stop_consts_never = []
val path_cond = (ASSUME T)
val fuel = 2

val comp_thm = INST_TYPE [Type.alpha |-> arch_ty] arch_multi_exec_comp_n_tl_assl

val [(path_cond, step_thm)] =
 symb_exec arch_ty ctx init_astate stop_consts_rewr stop_consts_never path_cond 24

(* Something goes wrong here *)
val [(path_cond, step_thm), (path_cond2, step_thm2)] =
 symb_exec arch_ty ctx init_astate stop_consts_rewr stop_consts_never path_cond 25

val [(path_cond, step_thm), (path_cond2, step_thm2)] =
 symb_exec arch_ty ctx init_astate stop_consts_rewr stop_consts_never path_cond 26




symb_exec arch_ty ctx init_astate stop_consts_rewr stop_consts_never path_cond 13









val _ = export_theory ();
