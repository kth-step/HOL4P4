open HolKernel boolLib Parse bossLib;

val _ = new_theory "p4_cake_exec_semProg";

open p4Theory p4_exec_semTheory p4_auxTheory p4_coreTheory p4_v1modelTheory;
open p4_cake_auxTheory p4_cake_exec_semTheory p4_cake_archTheory;
open p4_cake_auxLib;

(* CakeML: *)
open preamble ml_translatorLib ml_progLib basisProgTheory;

intLib.deprecate_int();
val _ = (max_print_depth := 100);

val _ = translation_extends "basisProg";

val _ = ml_prog_update (open_module "p4_exec_sem_cakeProg");

(** Expression semantics **)

val _ = translate numposrepTheory.l2n_def;
val _ = translate bitstringTheory.bitify_def;
val _ = translate bitstringTheory.v2n_def;
Theorem l2n_side_thm:
!n l. l2n_side n l <=> (l <> [] ==> n <> 0)
Proof
strip_tac \\
Induct \\ (
 rpt strip_tac \\
 ONCE_REWRITE_TAC[theorem "l2n_side_def"] \\
 gs[]
) \\
Cases_on ‘l’ \\ (
 gs[]
)
QED
val _ = update_precondition l2n_side_thm;
Theorem v2n_side:
!v1. v2n_side v1
Proof
gs[definition "v2n_side_def", l2n_side_thm, bitstringTheory.bitify_def]
QED
val _ = update_precondition v2n_side;

val _ = translate numposrepTheory.n2l_def;
val _ = translate bitstringTheory.boolify_def;
val _ = translate bitstringTheory.n2v_def;
Theorem n2l_side_thm:
!n m. n2l_side n m <=> n <> 0
Proof
strip_tac \\
completeInduct_on ‘m’ \\
rpt strip_tac \\
ONCE_REWRITE_TAC[theorem "n2l_side_def"] \\
gs[]
QED
val _ = update_precondition n2l_side_thm;
Theorem n2v_side:
!v. n2v_side v
Proof
gs[definition "n2v_side_def", n2l_side_thm]
QED
val _ = update_precondition n2v_side;

val _ = translate find_topmost_map'_def;
val _ = translate lookup_map'_def;
val _ = translate lookup_vexp2'_def;
val _ = translate is_v'_def;
val _ = translate e_exec_acc'_def;
val _ = translate INDEX_FIND_def;
val _ = translate is_const'_def;
val _ = translate unred_mem'_def;
val _ = translate unred_mem_index'_def;
val _ = translate MAP_SND_def;
val _ = translate v_of_e'_def;
val _ = translate vl_of_el'_def;
val _ = translate MAP_FST_def;
val _ = translate oEL_def;
val _ = translate listTheory.LUPDATE_DEF;

(* Function call *)
val _ = translate lookup_funn_sig_body'_def;
val _ = translate is_d_out_def;
val _ = translate get_lval_of_e'_def;
val _ = translate is_e_lval'_def;
val _ = translate is_arg_red'_def;
val _ = translate find_unred_arg'_def;
val _ = translate unred_arg_index'_def;
val _ = translate listTheory.FOLDL;
val _ = translate find_topmost_map'_def;
val _ = translate lookup_map'_def;
val _ = translate lookup_v'_def;
val _ = translate acc_f'_def;

val _ = translate rich_listTheory.SEG;
Theorem seg_side_thm:
!len start l. seg_side len start l <=> (len <> 0 ==> (start + len <= LENGTH l))
Proof
strip_tac \\
completeInduct_on ‘len’ \\
completeInduct_on ‘start’ \\
rpt strip_tac \\
ONCE_REWRITE_TAC[theorem "seg_side_def"] \\
gs[] \\
eq_tac >- (
 rpt strip_tac >- (
  res_tac \\
  gs[]
 ) \\
 gs[] \\
 qpat_x_assum ‘!m. m < SUC x4 ==>
               !l'. seg_side (SUC x3) m l' <=> m + SUC x3 <= LENGTH l'’
              (fn thm => ASSUME_TAC $ Q.SPEC ‘x4’ thm) \\
 gs[arithmeticTheory.SUC_ONE_ADD]
) \\
rpt strip_tac \\ (
 gs[]
) >- (
 Cases_on ‘len’ \\ Cases_on ‘start’ \\ (
  gs[]
 ) >- (
  Cases_on ‘l’ \\ (
   gs[]
  )
 ) \\
 Cases_on ‘l’ \\ (
  gs[]
 )
) \\
qpat_x_assum ‘!m. m < SUC x10 ==>
              !l'. seg_side (SUC x13) m l' <=> m + SUC x13 <= LENGTH l'’
             (fn thm => ASSUME_TAC $ Q.SPEC ‘x10’ thm) \\
gvs[] \\
gs[arithmeticTheory.SUC_ONE_ADD]
QED
val _ = update_precondition seg_side_thm;
val _ = translate bitv_bitslice_def;
val _ = translate slice'_def;
Theorem slice'_side:
!v1 v2 v3. slice'_side v1 v2 v3
Proof
simp[Once $ definition "slice'_side_def"] \\
simp[Once $ definition "bitv_bitslice_side_def"]
QED
val _ = update_precondition slice'_side;
val _ = translate slice_lval'_def;
val _ = translate lookup_lval''_def;

val _ = translate is_d_in_def;
val _ = translate bitstringTheory.extend_def;
val _ = translate init_out_v_cake_def;
val _ = translate one_arg_val_for_newscope'_def;
val _ = translate AFUPDKEY_def;
val _ = translate AUPDATE_def;
val _ = translate update_arg_for_newscope'_def;
val _ = translate all_arg_update_for_newscope'_def;
val _ = translate copyin'_def;

(* Cast *)
val _ = translate bitstringTheory.zero_extend_def;
val _ = translate listTheory.DROP_def;
val _ = translate bitstringTheory.fixwidth_def;
val _ = translate bool_cast_def;
val _ = translate bitv_cast_def;
val _ = translate oHD_def;
val _ = translate to_bool_cast_exec_def;
val _ = translate cast_exec_def;
val _ = translate e_exec_cast'_def;

(* Unops *)
val _ = translate bitv_1comp_def;
val _ = translate bitv_2comp_def;
Theorem bitv_2comp_side:
!v. bitv_2comp_side v
Proof
gs[definition "bitv_2comp_side_def", arithmeticTheory.LT_IMP_LE, bitstringTheory.v2n_lt]
QED
val _ = update_precondition bitv_2comp_side;
val _ = translate unop_exec'_def;
val _ = translate e_exec_unop'_def;

(* Binops *)

val _ = translate bitv_ls_def;
val _ = translate bitv_hs_def;
val _ = translate bitv_lo_def;
val _ = translate bitv_hi_def;
val _ = translate rich_listTheory.AND_EL_DEF;
val _ = translate bit_eq_def;
val _ = translate bitv_eq_def;
val _ = translate bitv_neq_def;
val _ = translate get_bitv_binpred'_def;
val _ = translate bitv_binpred'_def;

val _ = translate is_short_circuitable_def;
val _ = translate e_exec_short_circuit'_def;
val _ = translate bitv_bl_binop_def;
val _ = translate bitstringTheory.shiftl_def;

val _ = translate bitv_mul_def;
val _ = translate bitv_div_def;
val _ = translate bitv_mod_def;
val _ = translate bitv_add_def;
val _ = translate bitv_sub_def;
val _ = translate band'_def;
val _ = translate bitv_and_def;
val _ = translate bor'_def;
val _ = translate bitv_or_def;
val _ = translate bitstringTheory.bitwise_def;
val _ = translate bitstringTheory.bxor_def;
val _ = translate bitv_xor_def;

val _ = translate rich_listTheory.REPLICATE;
val _ = translate bitv_saturate_add_def;
val _ = translate bitv_saturate_sub_def;
val _ = translate TAKE_def;
val _ = translate bitv_lsl_bv_def;
val _ = translate bitv_lsr_bv_def;

val _ = translate p4Theory.binop2num_thm;
val _ = translate p4Theory.binop_CASE;
val _ = translate get_bitv_binop'_def;
val _ = translate bitv_binop'_def;

(* TODO: Not needed? At least not for binops?
val _ = translate (EVAL “w2v (w:word64)” |> SIMP_RULE (srw_ss()) [word_bit_test,word_bit_def,word_bit]);
val _ = translate (word_eq_def |> INST_TYPE [alpha|->match_width] |> INST_TYPE [beta|->match_width]);
*)

val _ = translate binop_exec'_def;
val _ = translate e_exec_binop'_def;

(* Select *)
val _ =
 if matching_optimization
 then
  let
   val match_width = “:64”;

   val word_msb_thm = Q.prove(
    ‘!w. word_msb (w:'a word) = BIT (dimindex (:'a) - 1) (w2n w)’,
    Cases \\ FULL_SIMP_TAC std_ss [word_msb_n2w,w2n_n2w])

   val _ = translate bitTheory.MOD_2EXP_def;
   val _ = translate bitTheory.DIV_2EXP_def;
   val _ = translate bitTheory.BITS_def;
   val _ = translate bitTheory.BIT_def;
   val _ = translate (word_msb_thm |> INST_TYPE [alpha|->match_width] |> SIMP_RULE (srw_ss()) []);
   val word_msb_side = Q.prove(
    ‘!w. word_msb_side w’,
    simp[Once $ definition "word_msb_side_def", definition "bit_side_def", definition "bits_side_def"])
   val _ = update_precondition word_msb_side;

   val _ = translate (word_mul_def |> INST_TYPE [alpha|->match_width] |> SIMP_RULE (srw_ss()) []);

   val _ = translate (word_2comp_def |> INST_TYPE [alpha|->match_width] |> SIMP_RULE (srw_ss()) [] |> SIMP_RULE std_ss [GSYM wordsTheory.WORD_NEG_MUL]);
   val word_2comp_side = Q.prove(
    ‘!w. word_2comp_side w’,
    simp[Once $ definition "word_2comp_side_def"] \\
    wordsLib.Induct_word \\ (
     gs[]
    ))
   val _ = update_precondition word_2comp_side;

   val _ = translate (nzcv_def |> INST_TYPE [alpha|->match_width] |> SIMP_RULE (srw_ss()) []);
   val nzcv_side = Q.prove(
    ‘!w w'. nzcv_side w w'’,
    simp[definition "nzcv_side_def", definition "bit_side_def", definition "bits_side_def"])
   val _ = update_precondition nzcv_side;
   val _ = translate (word_ls_def |> INST_TYPE [alpha|->match_width]);
   val _ = translate (word_lo_def |> INST_TYPE [alpha|->match_width]);
   val _ = translate p4_match_range''_def;
   val _ = translate p4_match_mask''_def;
   val _ = translate match''_def;
   val _ = translate match_all''_def;
   val _ = translate match_all_first''_def;

   val v2w_64_thm = Q.prove(
    ‘!v. v2w v = (n2w (v2n v)):word64’,
    FULL_SIMP_TAC std_ss [bitstringTheory.n2w_v2n])

   val _ = translate v2w_64_thm;
   val _ = translate v_list_to_word64s_list_def;
   val _ = translate match_all_first_def;
  in
   ()
  end
 else
  let
   val _ = translate p4_match_mask'_def;
   val _ = translate p4_match_range'_def;
   val _ = translate match'_def;
   val _ = translate match_all'_def;

   val _ = translate pre_match_check'_def;
  in
   ()
  end
;

val _ = translate e_exec_select'_def;

(* Concatenation *)
val _ = translate bitv_concat_def;
val _ = translate e_exec_concat'_def;
val _ = translate is_v_bit'_def;

(* Slicing *)
val _ = translate e_exec_slice'_def;

(* The whole expression-level semantics: *)
val _ = translate e_exec'_def;


(** Statement semantics **)

(* Assignment *)
val _ = translate lookup_out'_def;
val _ = translate listTheory.INDEX_OF_def;
val _ = translate replace_bits_def;
val _ = translate assign_to_slice'_def;
val _ = translate assign'_def;
val _ = translate stmt_exec_ass'_def;
val _ = translate oDROP_def;
val _ = translate oTAKE_def;
val _ = translate get_e_ctx_def;

(* Conditional *)
val _ = translate is_v_bool'_def;
val _ = translate stmt_exec_cond'_def;

(* Block *)
val _ = translate init_v_from_tau_cake_def;
val _ = translate declare_list_in_fresh_scope'_def;

(* Return *)
val _ = translate get_v'_def;

(* Sequence *)
val _ = translate is_empty'_def;

(* Transition *)
val _ = translate is_v_str'_def;
val _ = translate stmt_exec_trans'_def;

(* Apply *)
val _ = translate index_not_const'_def;
val _ = translate is_consts_exec'_def;

(* Extern *)
val _ = translate lookup_ext_fun'_def;
val _ = translate separate'_def;
val _ = translate stmt_exec'_def;


(** Frame semantics **)

val _ = translate scopes_to_pass'_def;
val _ = translate map_to_pass'_def;
val _ = translate tbl_to_pass'_def;
val _ = translate scopes_to_retrieve'_def;

val _ = translate is_d_none_in_def;
val _ = translate update_return_frame'_def;
val _ = translate copyout'_def;
val _ = translate frames_exec'_def;


(** Arch semantics **)

val _ = translate lookup_block_body_def;
val _ = translate oLASTN_def;
val _ = translate declare_list_in_scope'_def;
val _ = translate AUPDATE_LIST_def;
val _ = translate var_star_updates_of_func_map'_def;
val _ = translate var_star_updates_of_ext_map'_def;
val _ = translate initialise_var_stars'_def;
val _ = translate state_fin_exec_def;
val _ = translate set_fin_status'_def;

val _ = translate arch_exec'_def;

val _ = translate arch_multi_exec'_def;

(** Core arch implementation **)

val _ = translate header_is_valid'_def;

val _ = translate header_set_valid'_def;

val _ = translate header_set_invalid'_def;

(* Common extern functions: *)

val _ = translate oTAKE_DROP_def;
val _ = translate v2w16s'''_def;
val _ = translate header_entries2v'_def;
val _ = translate v2w16s''_def;
val _ = translate p4_cake_archTheory.get_checksum_incr''_def;

val _ = translate add_with_carry'_def;
val _ = translate add_ones_complement'_def;
val _ = translate compute_checksum16_inner_def;
val _ = translate all_lists_length_16_def;
val _ = translate compute_checksum16_def;
Theorem compute_checksum16_side:
!v1. compute_checksum16_side v1
Proof
simp[Once $ definition "compute_checksum16_side_def"] \\
Induct >- (
 simp[Once $ theorem "compute_checksum16_inner_side_def", all_lists_length_16_def]
) \\
rpt strip_tac \\
gs[all_lists_length_16_def, Once $ theorem "compute_checksum16_inner_side_def"] \\
Cases_on ‘v1’ >- (
 gs[theorem "compute_checksum16_inner_side_def",
    compute_checksum16_inner_def, Once $ definition "add_ones_complement'_side_def",
    Once $ definition "add_with_carry'_side_def"] \\
 rpt strip_tac \\ (
  gs[bitstringTheory.fixwidth_def, AllCaseEqs(), bitstringTheory.zero_extend_def,
     listTheory.PAD_LEFT]
 ) 
) \\
qpat_x_assum ‘!x2 x1. _’ (fn thm => ASSUME_TAC $ Q.SPECL [‘h'’, ‘t’] thm) \\
simp[Once $ theorem "compute_checksum16_inner_side_def",
     Once $ definition "add_ones_complement'_side_def",
     Once $ definition "add_with_carry'_side_def"] \\
rpt strip_tac >- (
 gs[]
) >- (
 gs[compute_checksum16_inner_def, add_ones_complement'_def, add_with_carry'_def,
    AllCaseEqs(), bitstringTheory.fixwidth_def, AllCaseEqs(),
    bitstringTheory.zero_extend_def, listTheory.PAD_LEFT]
) >- (
 gs[]
) >- (
 gs[bitstringTheory.fixwidth_def, AllCaseEqs(), bitstringTheory.zero_extend_def,
    listTheory.PAD_LEFT]
) \\
simp[Once $ theorem "compute_checksum16_inner_side_def"]
QED
val _ = update_precondition compute_checksum16_side;

(** For wrapper, rewrites, et.c. **)

val _ = translate p4_append_input_list'_def;
val _ = translate p4_get_output_list'_def;

val _ = translate word_def;

val _ = ml_prog_update (close_module NONE);

val _ = export_theory ();
