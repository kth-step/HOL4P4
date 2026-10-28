structure p4_symb_exec_v1modelLib :> p4_symb_exec_v1modelLib = struct

open HolKernel boolLib liteLib simpLib bossLib;

open bitstringSyntax listSyntax numSyntax optionSyntax pairSyntax;

open symb_execTheory p4_symb_execTheory p4_v1modelTheory;

open p4_v1modelLib p4Syntax p4_testLib;

open auxLib symb_execSyntax p4_symb_execSyntax p4_convLib;

(***********************************************)
(* Approximation functions for v1model externs *)

val ERR = mk_HOL_ERR "p4_symb_exec_v1model"

fun lookup_var varname scope_list =
 let
  val lookup_res = rhs $ concl $ HOL4P4_CONV (mk_lookup_lval (scope_list, (mk_lval_varname varname)))
 in
  if is_some lookup_res
  then dest_some lookup_res
  else raise (ERR "lookup_var" ("Could not find variable in local scope: "^varname))
 end
;

(* |- !list. LENGTH list = width ==> ?bits. list = bits, for the fresh variables bits *)
fun bits_exists_thm approx_vars width =
 let
  val list_var = mk_var("list", mk_list_type bool)
 in
  prove(mk_forall (list_var, mk_imp (mk_eq (mk_length list_var, width), list_mk_exists (fst $ dest_list approx_vars, mk_eq (list_var, approx_vars)))),
   rpt strip_tac >>
   rpt (goal_term (fn tm => tmCases_on (fst $ dest_eq $ snd $ strip_exists tm) []) >> FULL_SIMP_TAC list_ss [])
  )
 end
;

fun approx_v1model_register_construct p4_symb_arg_prefix fv_index scope_list ascope =
 let
  (* Array size *)
  val array_size = fst $ dest_pair $ dest_v_bit $ lookup_var "size" scope_list
  val targ1_width = snd $ dest_pair $ dest_v_bit $ lookup_var "targ1" scope_list
  val oracle_index = #5 $ dest_v1model_ascope ascope

  (* TODO: HOL4P4_CONV? *)
  val array_size_num = rhs $ concl $ EVAL (mk_v2n array_size)

  val tm1 = mk_v1model_register_construct_inner (array_size_num, targ1_width, oracle_index, random_oracle_tm)

  (* TODO: Hacky... *)
  val rhs_tm = hd $ fst $ dest_list $ fixedwidth_freevars_fromindex_ty (p4_symb_arg_prefix, fv_index, 1, mk_list_type $ mk_prod (mk_list_type bool, num))
  val goal_tm = mk_disj_list [boolSyntax.mk_exists (rhs_tm, mk_conj (mk_eq (tm1, rhs_tm), (mk_wellformed_register_array (targ1_width, rhs_tm))))]

  val approx_thm =
   (* “^goal_tm” *)
   prove(goal_tm,
(*
    SIMP_TAC std_ss [disj_list_def, v1model_register_construct_inner_def, get_oracle_calls_array_def] >>
*)
   (* TODO: Why doesn't just the above work? Make more efficient solution... *)
    SIMP_TAC bool_ss [disj_list_def] >>
    EVAL_TAC
   );
 in
  SOME (approx_thm, [fv_index+1])
 end
;

(* Proves wellformed_register_array w arr, with thms for array variables *)
fun prove_wellformed_register_array thms tm =
 let
  val thm = QCONV (SIMP_CONV (srw_ss()) ([wellformed_register_array_construct_inner, wellformed_register_array_write_inner, wellformed_register_array_LUPDATE, bitstringTheory.length_fixwidth]@thms)) tm
  val thm' = if Teq $ rhs $ concl thm then thm else QCONV (computeLib.RESTR_EVAL_CONV [v1model_register_construct_inner_tm]) tm
 in
  if Teq $ rhs $ concl thm' then SOME (EQT_ELIM thm') else NONE
 end
;

fun approx_v1model_register_read p4_symb_arg_prefix fv_index scope_list ascope = 
 let
  (* 1. Get first entry of register array (for entry width) *)
  val array_index = fst $ dest_pair $ dest_v_bit $ lookup_var "index" scope_list
  val ext_ref = dest_v_ext_ref $ lookup_var "this" scope_list
  val entry_width = snd $ dest_pair $ dest_v_bit $ lookup_var "result" scope_list

  val (_, ext_obj_map, _, _, oracle_index) = dest_v1model_ascope ascope
  (* Looked up structurally: evaluation would unfold the register contents *)
  val array =
   case List.find (fn kv => term_eq (fst $ dest_pair kv) ext_ref) (fst $ dest_list ext_obj_map) of
     SOME kv => snd $ dest_comb $ fst $ sumSyntax.dest_inr $ snd $ dest_pair kv
   | NONE => raise (ERR "approx_v1model_register_read" ("no extern object at index "^(term_to_string ext_ref)))

  (* 2. Prove approximation theorem *)
  val tm1 = mk_v1model_register_read_inner (entry_width, array_index, array, oracle_index, random_oracle_tm)
  (* TODO: Hack, make function that returns list *)
  val approx_vars = fixedwidth_freevars_fromindex (p4_symb_arg_prefix, fv_index, int_of_term entry_width)
  val rhs_tm = mk_pair (approx_vars, entry_width)
  val goal_tm = mk_disj_list [list_mk_exists (fst $ dest_list approx_vars, mk_eq (tm1, rhs_tm))]

  (* Unless you cache, these have to be proved every single time *)
  val list_exists_thm = bits_exists_thm approx_vars entry_width

  val approx_thm =
   (* “^(mk_imp (mk_wellformed_register_array (entry_width, array), goal_tm))” *)
   prove(mk_imp (mk_wellformed_register_array (entry_width, array), goal_tm),
    (* As soon as possible, hide the array, which may be big *)
    markerLib.ABBREV_TAC (mk_eq (mk_var("array", mk_list_type (mk_prod (mk_list_type bool, num))) ,array)) >>
    qpat_x_assum ‘Abbrev (array = _)’ (fn thm => markerLib.hide_tac "big_array" thm) >>
    SIMP_TAC std_ss [disj_list_def, v1model_register_read_inner_def] >>
    disch_tac >>
    CASE_TAC >- (
     (* The oracle index is taken from the goal, where it may have been simplified *)
     goal_term (fn tm =>
      case strip_comb $ lhs $ snd $ strip_exists tm of
        (_, [n, i, f]) => ACCEPT_TAC (MATCH_MP list_exists_thm (ISPECL [n, i, f] LENGTH_get_oracle_calls))
      | _ => raise (ERR "approx_v1model_register_read" "unexpected goal for an index out of bounds"))
    ) >>
    Cases_on ‘x’ >>
    imp_res_tac p4_symb_execTheory.wellformed_register_array_oEL >>
    imp_res_tac list_exists_thm >>
    RW_TAC std_ss []
   );
  val approx_thm' =
   case prove_wellformed_register_array [] (mk_wellformed_register_array (entry_width, array)) of
     SOME wf_thm => MATCH_MP approx_thm wf_thm
   | NONE => approx_thm
 in
  SOME (approx_thm', [fv_index+(int_of_term entry_width)])
 end
;

(* Fresh variables in [lo, hi] when the draw is not resolved by the bounds alone *)
fun approx_v1model_random p4_symb_arg_prefix fv_index scope_list ascope =
 let
  val lo = fst $ dest_pair $ dest_v_bit $ lookup_var "lo" scope_list
  val hi = fst $ dest_pair $ dest_v_bit $ lookup_var "hi" scope_list
  val width = snd $ dest_pair $ dest_v_bit $ lookup_var "result" scope_list
  val oracle_index = #5 $ dest_v1model_ascope ascope
  val tm1 = mk_v1model_random_inner (lo, hi, width, oracle_index, random_oracle_tm)
  val tm1_val = rhs $ concl $ EVAL tm1
 in
  if is_list tm1_val andalso not (can (find_term is_cond) tm1_val)
  then NONE
  else
   let
    val approx_vars = fixedwidth_freevars_fromindex (p4_symb_arg_prefix, fv_index, int_of_term width)
    val range_tm = mk_imp (mk_leq (mk_v2n lo, mk_v2n hi), mk_conj (mk_leq (mk_v2n lo, mk_v2n approx_vars), mk_leq (mk_v2n approx_vars, mk_v2n hi)))
    val goal_tm = mk_disj_list [list_mk_exists (fst $ dest_list approx_vars, mk_conj (mk_eq (tm1, approx_vars), range_tm))]
    val len_thm = MP (SPECL [lo, hi, width, oracle_index, random_oracle_tm] v1model_random_inner_LENGTH) (EQT_ELIM $ EVAL (mk_eq (mk_length lo, width)))
    val range_thm = SPECL [lo, hi, width, oracle_index, random_oracle_tm] v1model_random_inner_range
    val exists_thm = MP (SPEC tm1 (bits_exists_thm approx_vars width)) len_thm
    val approx_thm =
     prove(goal_tm,
      SIMP_TAC std_ss [disj_list_def] >>
      STRIP_ASSUME_TAC exists_thm >>
      MAP_EVERY EXISTS_TAC (fst $ dest_list approx_vars) >>
      POP_ASSUM (fn thm => REWRITE_TAC [GSYM thm, range_thm])
     )
   in
    SOME (approx_thm, [fv_index + (int_of_term width)])
   end
 end
;

(* TODO: Fix this. Similar to register construction *)
fun approx_v1model_update_checksum p4_symb_arg_prefix fv_index scope_list =
 let
  (* Must be evaluated like the regular steps (not with EVAL), so that the equation added to the path condition matches the term in the state *)
  val data_bitlist = dest_some $ rhs $ concl $ RESTR_HOL4P4_CONV_stop_consts “case lookup_lval ^scope_list (lval_varname (varn_name "data")) of SOME v => OPTION_MAP (pad_bits 16) (data_bits v) | NONE => NONE”

  val tm1 = mk_v1model_update_checksum_inner data_bitlist

  val approx_vars = fixedwidth_freevars_fromindex (p4_symb_arg_prefix, fv_index, 16)

  val rhs_tm = mk_v_bit $ mk_pair (approx_vars, term_of_int 16)
  val goal_tm = mk_disj_list [boolSyntax.list_mk_exists (fst $ dest_list approx_vars, mk_eq (tm1, rhs_tm))]

  val approx_thm =
   (* “^goal_tm” *)
   prove(goal_tm,
    SIMP_TAC std_ss [disj_list_def, v1model_update_checksum_inner_def, p4Theory.v_11, p4Theory.w16_def, w2v_exists]
   );
 in
  SOME (approx_thm, [fv_index+16])
 end
;

end
