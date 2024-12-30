structure p4_symb_exec_v1modelLib :> p4_symb_exec_v1modelLib = struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

open bitstringSyntax listSyntax numSyntax optionSyntax pairSyntax;

open symb_execTheory p4_symb_execTheory p4_v1modelTheory;

open p4_v1modelLib p4Syntax p4_testLib;

open auxLib symb_execSyntax p4_convLib;

(* TODO: Move? *)
val (wellformed_register_array_tm, mk_wellformed_register_array, dest_wellformed_register_array, is_wellformed_register_array) =
  syntax_fns2 "p4_symb_exec" "wellformed_register_array";

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

fun approx_v1model_register_construct p4_symb_arg_prefix fv_index scope_list =
 let
  (* Array size *)
  val array_size = fst $ dest_pair $ dest_v_bit $ lookup_var "size" scope_list
  val targ1_width = snd $ dest_pair $ dest_v_bit $ lookup_var "targ1" scope_list

  val tm1 = mk_v1model_register_construct_inner (array_size, targ1_width)

  (* TODO: HOL4P4_CONV? *)
  val array_size_num = rhs $ concl $ EVAL (mk_v2n array_size)

  (* TODO: Hacky... *)
  val rhs_tm = hd $ fst $ dest_list $ fixedwidth_freevars_fromindex_ty (p4_symb_arg_prefix, fv_index, 1, mk_list_type $ mk_prod (mk_list_type bool, num))
  val goal_tm = mk_disj_list [boolSyntax.mk_exists (rhs_tm, mk_conj (mk_eq (tm1, rhs_tm), (mk_wellformed_register_array (targ1_width, rhs_tm))))]

  val approx_thm =
   (* “^goal_tm” *)
   prove(goal_tm,
    SIMP_TAC std_ss [disj_list_def, v1model_register_construct_inner_def, wellformed_register_array_replicate_arb]
   );
 in
  SOME (approx_thm, [fv_index+1])
 end
;

fun approx_v1model_register_read p4_symb_arg_prefix fv_index scope_list ascope = 
 let
  (* 1. Get first entry of register array (for entry width) *)
  val array_index = fst $ dest_pair $ dest_v_bit $ lookup_var "index" scope_list
  val ext_ref = dest_v_ext_ref $ lookup_var "this" scope_list
  val entry_width = snd $ dest_pair $ dest_v_bit $ lookup_var "result" scope_list

  val ext_obj_map = #2 $ p4_v1modelLib.dest_v1model_ascope ascope
  val array = snd $ dest_comb $ fst $ sumSyntax.dest_inr $ dest_some $ rhs $ concl $ HOL4P4_CONV (mk_alookup (ext_obj_map, ext_ref))

  (* 2. Prove approximation theorem *)
  val tm1 = mk_v1model_register_read_inner (entry_width, array_index, array)
  (* TODO: Hack, make function that returns list *)
  val approx_vars = fixedwidth_freevars_fromindex (p4_symb_arg_prefix, fv_index, int_of_term entry_width)
  val rhs_tm = mk_pair (approx_vars, entry_width)
  val goal_tm = mk_disj_list [list_mk_exists (fst $ dest_list approx_vars, mk_eq (tm1, rhs_tm))]

  (* Unless you cache, these have to be proved every single time *)
  val list_var = mk_var("list", mk_list_type bool)
  val list_hyp = mk_eq(mk_length list_var, entry_width)
  val list_exists_thm = prove(mk_forall (list_var, mk_imp (list_hyp, list_mk_exists(fst $ dest_list approx_vars, mk_eq (list_var, approx_vars)))), 
   rpt strip_tac >>
   rpt (goal_term (fn tm => tmCases_on (fst $ dest_eq $ snd $ strip_exists tm) []) >> FULL_SIMP_TAC list_ss [])
  );

  val approx_thm =
   (* “^goal_tm” *)
   prove(mk_imp (mk_wellformed_register_array (entry_width, array), goal_tm),
    (* As soon as possible, hide the array, which may be big *)
    markerLib.ABBREV_TAC (mk_eq (mk_var("array", mk_list_type (mk_prod (mk_list_type bool, num))) ,array)) >>
    qpat_x_assum ‘Abbrev (array = _)’ (fn thm => markerLib.hide_tac "big_array" thm) >>
    SIMP_TAC std_ss [disj_list_def, v1model_register_read_inner_def] >>
    disch_tac >>
    CASE_TAC >- (
     (* TODO: HOL4P4_TAC or other solution? *)
     EVAL_TAC >>
     ntac (int_of_term entry_width) (exists_tac (mk_arb bool)) >>
     REWRITE_TAC []
    ) >>
    Cases_on ‘x’ >>
    imp_res_tac p4_symb_execTheory.wellformed_register_array_oEL >>
    imp_res_tac list_exists_thm >>
    RW_TAC std_ss []
   );
  (* The antecedent may be computable. Either check this before or compute it here *)
  val wf_ante_eval = EVAL $ mk_wellformed_register_array (entry_width, array)

  val approx_thm' =
   if Teq $ snd $ dest_eq $ concl wf_ante_eval
   then MATCH_MP approx_thm (EQT_ELIM wf_ante_eval)
   else approx_thm
 in
  SOME (approx_thm', [fv_index+(int_of_term entry_width)])
 end
;

(* TODO: Fix this. Similar to register construction *)
fun approx_v1model_update_checksum p4_symb_arg_prefix fv_index scope_list =
 let
  (* TODO: HOL4P4_CONV? *)
  val data_bitlist = dest_some $ rhs $ concl $ EVAL “get_checksum_incr'' ^scope_list (lval_varname (varn_name "data"))”

  val tm1 = mk_compute_checksum16_inner data_bitlist

  val approx_vars = fixedwidth_freevars_fromindex (p4_symb_arg_prefix, fv_index, 16)

  val rhs_tm = mk_some approx_vars
  val goal_tm = mk_disj_list [boolSyntax.list_mk_exists (fst $ dest_list approx_vars, mk_eq (tm1, rhs_tm))]

  val approx_thm =
   (* “^goal_tm” *)
   prove(goal_tm,
    SIMP_TAC std_ss [disj_list_def, compute_checksum16_inner_def, p4Theory.v_11, p4Theory.w16_def, w2v_exists]
   );
 in
  SOME (approx_thm, [fv_index+16])
 end
;

end
