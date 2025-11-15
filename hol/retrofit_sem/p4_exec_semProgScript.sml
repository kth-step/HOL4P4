open HolKernel boolLib Parse bossLib;

val _ = new_theory "p4_exec_semProg";

open p4Theory p4_auxTheory p4_coreTheory p4_v1modelTheory
     p4_exec_semTheory;
open p4_exec_archTheory;

(* CakeML: *)
open preamble ml_translatorLib ml_progLib basisProgTheory;

intLib.deprecate_int();
val _ = (max_print_depth := 100);

val _ = translation_extends "basisProg";

val _ = ml_prog_update (open_module "p4_exec_semProg");

(************************)
(* Expression semantics *)

(* Variable look-up *)
val _ = translate INDEX_FIND_def;
val _ = translate find_topmost_map_def;
val _ = translate topmost_map_def;
val _ = translate lookup_map_def;
val _ = translate lookup_vexp2_def;

(* Struct/header field access *)
val _ = translate is_v_def;
val _ = translate e_exec_acc_def;

(* Unary arithmetic *)
val _ = translate bitv_1comp_def;
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
val _ = translate bitstringTheory.zero_extend_def;
val _ = translate listTheory.DROP_def;
val _ = translate bitstringTheory.boolify_def;
val _ = translate numposrepTheory.n2l_def;
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
val _ = translate bitstringTheory.fixwidth_def;
val _ = translate bitv_2comp_def;
Theorem bitv_2comp_side:
!v. bitv_2comp_side v
Proof
gs[definition "bitv_2comp_side_def", arithmeticTheory.LT_IMP_LE, bitstringTheory.v2n_lt]
QED
val _ = update_precondition bitv_2comp_side;
val _ = translate bitv_unop_def;
val _ = translate unop_exec_def;
Theorem unop_exec_side:
!unop v. unop_exec_side unop v
Proof
gs[definition "unop_exec_side_def"] >>
rpt strip_tac >>
gs[definition "bitv_unop_side_def"]
QED
val _ = update_precondition unop_exec_side;
val _ = translate e_exec_unop_def;

(* Cast *)
val _ = translate bool_cast_def;
val _ = translate bitv_cast_def;
val _ = translate oHD_def;
val _ = translate to_bool_cast_exec_def;
val _ = translate cast_exec_def;
val _ = translate e_exec_cast_def;

(* Binary arithmetic *)
val _ = translate is_short_circuitable_def;
val _ = translate e_exec_short_circuit_def;

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
val _ = translate bitv_lsl_bv_def;
val _ = translate TAKE_def;
val _ = translate bitv_lsr_bv_def;
val _ = translate get_bitv_binop_def;
val _ = translate bitv_binop_def;

val _ = translate bitv_bl_binop_def;
val _ = translate bitstringTheory.shiftl_def;

val _ = translate bitv_ls_def;
val _ = translate bitv_hs_def;
val _ = translate bitv_lo_def;
val _ = translate bitv_hi_def;
val _ = translate rich_listTheory.AND_EL_DEF;
val _ = translate bit_eq_def;
val _ = translate bitv_eq_def;
val _ = translate bitv_neq_def;
val _ = translate get_bitv_binpred_def;
val _ = translate bitv_binpred_def;

val _ = translate binop_exec_def;
val _ = translate e_exec_binop_def;

(* Concatenation *)
val _ = translate bitv_concat_def;
val _ = translate e_exec_concat_def;
val _ = translate is_v_bit_def;

(* Slicing *)
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
val _ = translate e_exec_slice_def;

(* Function call *)
val _ = translate lookup_funn_sig_body_def;

val _ = translate is_d_out_def;

val _ = translate get_lval_of_e_def;

val _ = translate is_e_lval_def;
val _ = translate is_const_def;
val _ = translate is_arg_red_def;
val _ = translate find_unred_arg_def;
val _ = translate unred_arg_index_def;

val _ = translate is_d_in_def;
val _ = translate bitstringTheory.extend_def;

val _ = translate slice_lval'_def;
val _ = translate acc_f_def;
val _ = translate lookup_v_def;
val _ = translate lookup_lval'_def;

val _ = translate v_of_e_def;
val _ = translate uninit_bit_def;
val _ = translate uninit_string_def;
val _ = translate init_out_v_gen_def;

Theorem FOLDL_and_elem_F:
!l f.
~FOLDL (λa b. f b ∧ a) F l
Proof
Induct >>
gs[]
QED

Theorem FOLDL_and_elem_nonempty:
!f b e h t.
FOLDL (λa b. f b ∧ a) e (h::t) ==> e
Proof
Induct_on ‘t’ >> (
 gs[]
) >>
rpt strip_tac >>
qpat_x_assum ‘!f e h. _’ irule >>
Cases_on ‘f h’ >> gs[] >- (
 metis_tac[]
) >>
gs[FOLDL_and_elem_F]
QED

Theorem FOLDL_and_member:
!f b e m l.
FOLDL (λa b. f b ∧ a) e l ==>
MEM m l ==>
f m
Proof
Induct_on ‘l’ >> (
 gs[]
) >>
rpt strip_tac >>
gvs[] >- (
 Cases_on ‘f h’ >> gs[FOLDL_and_elem_F]
) >>
metis_tac[]
QED

Theorem init_out_v_gen_side_thm:
!uninit.
uninit <> uninit_arb ==>
!v.
init_out_v_gen_side uninit v
Proof
strip_tac >>
strip_tac >>
Cases_on ‘uninit’ >> (gs[]) >>
‘(!v. (\v. init_out_v_gen_side uninit_zero v) v) /\
 (!l. (\l:((string # p4$v) list). FOLDL (\b v. init_out_v_gen_side uninit_zero (SND v) /\ b) T l) l) /\
 (!(p:(string # p4$v)). (\v. init_out_v_gen_side uninit_zero (SND v)) p)’ suffices_by (
 gs[]
) >>
irule v_induction >>
rpt strip_tac >- (
 simp[Once $ theorem "init_out_v_gen_side_def"]
) >- (
 simp[Once $ theorem "init_out_v_gen_side_def"]
) >- (
 simp[Once $ theorem "init_out_v_gen_side_def", Once $ definition "uninit_bit_side_def"]
) >- (
 simp[Once $ theorem "init_out_v_gen_side_def", Once $ definition "uninit_string_side_def"]
) >- (
 simp[Once $ theorem "init_out_v_gen_side_def"] >>
 rpt strip_tac >- (
  gvs[] >>
  Cases_on ‘init_out_v_gen_side uninit_zero x6’ >> (gs[]) >>
  Cases_on ‘x8’ >- (gs[]) >>
  metis_tac[FOLDL_and_elem_nonempty]
 ) >>
 gvs[] >>
 (* If x3 is a member, it must hold, or else the other premise would be false *)
 ‘(λv. init_out_v_gen_side uninit_zero (SND v)) (x4,x3)’ suffices_by gs[] >>
 irule FOLDL_and_member >>
 metis_tac[]
) >- (
 simp[Once $ theorem "init_out_v_gen_side_def"] >>
 rpt strip_tac >- (
  gvs[] >>
  Cases_on ‘init_out_v_gen_side uninit_zero x13’ >> (gs[]) >>
  Cases_on ‘x15’ >- (gs[]) >>
  metis_tac[FOLDL_and_elem_nonempty]
 ) >>
 gvs[] >>
 (* If x3 is a member, it must hold, or else the other premise would be false *)
 ‘(λv. init_out_v_gen_side uninit_zero (SND v)) (x11,x10)’ suffices_by gs[] >>
 irule FOLDL_and_member >>
 metis_tac[]
) >- (
 simp[Once $ theorem "init_out_v_gen_side_def"]
) >- (
 simp[Once $ theorem "init_out_v_gen_side_def"] >>
 rpt strip_tac >>
 simp[Once $ definition "uninit_bit_side_def"]
) >- (
 FULL_SIMP_TAC bool_ss [listTheory.FOLDL]
) >>
FULL_SIMP_TAC bool_ss [SND]
QED
val _ = update_precondition init_out_v_gen_side_thm;
val _ = translate one_arg_val_for_newscope_exec_def;
Theorem one_arg_val_for_newscope_exec_side_thm:
!uninit.
uninit <> uninit_arb ==>
!d e scope_list.
one_arg_val_for_newscope_exec_side uninit d e scope_list
Proof
strip_tac >>
strip_tac >>
Cases_on ‘uninit’ >> (gs[]) >>
 simp[Once $ definition "one_arg_val_for_newscope_exec_side_def"] >>
rpt strip_tac >>
gs[init_out_v_gen_side_thm]
QED

val _ = translate AFUPDKEY_def;
val _ = translate AUPDATE_def;
val _ = translate update_arg_for_newscope_exec_def;
Theorem update_arg_for_newscope_exec_side_thm:
!uninit.
uninit <> uninit_arb ==>
!scope_list scope_opt d_x_e.
update_arg_for_newscope_exec_side uninit scope_list scope_opt d_x_e
Proof
strip_tac >>
strip_tac >>
Cases_on ‘uninit’ >> (gs[]) >>
simp[Once $ definition "update_arg_for_newscope_exec_side_def", one_arg_val_for_newscope_exec_side_thm]
QED
val _ = update_precondition one_arg_val_for_newscope_exec_side_thm;

val _ = translate listTheory.FOLDL;
val _ = translate all_arg_update_for_newscope_exec_def;
Theorem all_arg_update_for_newscope_exec_side_thm:
!uninit.
uninit <> uninit_arb ==>
!xlist dlist elist ss.
all_arg_update_for_newscope_exec_side uninit xlist dlist elist ss
Proof
strip_tac >>
strip_tac >>
Cases_on ‘uninit’ >> (gs[]) >>
simp[Once $ definition "all_arg_update_for_newscope_exec_side_def", update_arg_for_newscope_exec_side_thm]
QED
val _ = update_precondition all_arg_update_for_newscope_exec_side_thm;

val _ = translate copyin_exec_def;
Theorem copyin_exec_side_thm:
!uninit.
uninit <> uninit_arb ==>
!xlist dlist elist scope_list scope_list'.
copyin_exec_side uninit xlist dlist elist scope_list scope_list'
Proof
strip_tac >>
strip_tac >>
Cases_on ‘uninit’ >> (gs[]) >>
simp[Once $ definition "copyin_exec_side_def", all_arg_update_for_newscope_exec_side_thm]
QED

val _ = translate oEL_def;

(* Select *)

val _ = translate p4_match_range_exec_def;
val _ = translate p4_match_mask_exec_def;
val _ = translate match_exec_def;
val _ = translate match_all_exec_def;
val _ = translate pre_match_check_def;
val _ = translate e_exec_select_def;

(* Struct *)

val _ = translate unred_mem_def;
val _ = translate unred_mem_index_def;

val _ = translate get_v_def;
val _ = translate vl_of_el_exec_def;

(* The whole expression-level semantics: *)
val _ = translate e_exec_def;

Theorem LLOOKUP_MEM:
!l n e.
LLOOKUP l n = SOME e ==>
MEM e l
Proof
Induct >> gs[LLOOKUP_def] >>
rpt strip_tac >>
cases_on ‘n = 0’ >> gs[] >>
metis_tac[]
QED

Theorem LLOOKUP_MAP_SND:
!l n e.
LLOOKUP (MAP SND l) n = SOME e ==>
?x. LLOOKUP l n = SOME (x,e)
Proof
Induct >> gs[LLOOKUP_def] >>
rpt strip_tac >>
cases_on ‘n = 0’ >> gvs[] >>
qexists_tac ‘FST h’ >>
gs[]
QED

Theorem e_exec_side_thm:
!uninit.
uninit <> uninit_arb ==>
!e_ctx g_scope_list scope_list e.
e_exec_side uninit e_ctx g_scope_list scope_list e
Proof
strip_tac >>
strip_tac >>
Cases_on ‘uninit’ >> (gs[]) >>
strip_tac >> strip_tac >> strip_tac >>          
‘(!e. (\e. e_exec_side uninit_zero e_ctx g_scope_list scope_list e) e) /\
 (!l. (\l:((string # p4$e) list). FOLDL (\b x_e. e_exec_side uninit_zero e_ctx g_scope_list scope_list (SND x_e) /\ b) T l) l) /\
 (!(p:(string # p4$e)). (\x_e. e_exec_side uninit_zero e_ctx g_scope_list scope_list (SND x_e)) p) /\
 (!e_l. (\e_l. FOLDL (\b e. e_exec_side uninit_zero e_ctx g_scope_list scope_list e /\ b) T e_l) e_l)’ suffices_by (
 gs[]
) >>
irule e_induction >>
rpt strip_tac >- (
 simp[Once $ theorem "e_exec_side_def"]
) >- (
 simp[Once $ theorem "e_exec_side_def"]
) >- (
 simp[Once $ theorem "e_exec_side_def"] >>
 rpt strip_tac >>
 gs[]
) >- (
 simp[Once $ theorem "e_exec_side_def"] >>
 rpt strip_tac >>
 gs[]
) >- (
 simp[Once $ theorem "e_exec_side_def"] >>
 rpt strip_tac >>
 gs[]
) >- (
 FULL_SIMP_TAC bool_ss [listTheory.FOLDL]
) >- (
 simp[Once $ theorem "e_exec_side_def"] >>
 rpt strip_tac >>
 gs[]
) >- (
 simp[Once $ theorem "e_exec_side_def"] >>
 rpt strip_tac >>
 gs[]
) >- (
 gs[]
) >- (
 simp[Once $ theorem "e_exec_side_def"] >>
 rpt strip_tac >>
 gs[]
) >- (
 simp[Once $ theorem "e_exec_side_def"] >>
 rpt strip_tac >>
 gs[]
) >- (
 simp[Once $ theorem "e_exec_side_def"] >>
 rpt strip_tac >>
 gs[]
) >- (
 simp[Once $ theorem "e_exec_side_def"] >>
 rpt strip_tac >- (
  gvs[copyin_exec_side_thm]
 ) >>
 gvs[] >>
 irule FOLDL_and_member >>
 ‘MEM x26 l’ by (
  metis_tac[LLOOKUP_MEM]
 ) >>
 metis_tac[]
) >- (
 simp[Once $ theorem "e_exec_side_def"] >>
 rpt strip_tac >>
 gvs[] >>
 ‘?x. LLOOKUP l x36 = SOME (x,x35)’ by metis_tac[LLOOKUP_MAP_SND] >>
 ‘MEM (x,x35) l’ by (
  metis_tac[LLOOKUP_MEM]
 ) >>
 ‘(λx_e. e_exec_side uninit_zero e_ctx g_scope_list scope_list (SND x_e)) (x,x35)’ suffices_by gs[] >>
 irule FOLDL_and_member >>
 metis_tac[]
) >- (
 simp[Once $ theorem "e_exec_side_def"] >>
 rpt strip_tac >>
 gvs[]
) >- (
 FULL_SIMP_TAC bool_ss [listTheory.FOLDL]
) >- (
 simp[Once $ theorem "e_exec_side_def"] >>
 rpt strip_tac >>
 gs[]
) >>
simp[Once $ theorem "e_exec_side_def"] >>
rpt strip_tac >>
gs[]
QED

(*************************)
(** Statement semantics **)

val _ = translate get_e_ctx_def;

(* Assignment *)
val _ = translate separate_exec_def;

val _ = translate lookup_out_def;
val _ = translate replace_bits_def;
val _ = translate assign_to_slice'_def;
val _ = translate listTheory.INDEX_OF_def;
val _ = translate assign'_def;
val _ = translate stmt_exec_ass_def;

(* Conditional *)
val _ = translate is_v_bool_def;
val _ = translate stmt_exec_cond_def;

(* Block *)
(* TODO: Fix this hack *)
val _ = translate init_v_from_tau_cake_def;
(*
val _ = translate declare_list_in_fresh_scope_exec'_def;
*)
val _ = translate uninit_num_def;
val _ = translate arb_from_tau_gen_def;
Theorem arb_from_tau_gen_side_thm:
!uninit.
uninit <> uninit_arb ==>
!tau.
arb_from_tau_gen_side uninit tau
Proof
strip_tac >>
strip_tac >>
Cases_on ‘uninit’ >> (gs[]) >>
‘(!tau. (\tau. arb_from_tau_gen_side uninit_zero tau) tau) /\
 (!l. (\l:((string # p4$tau) list). FOLDL (\b x_tau. arb_from_tau_gen_side uninit_zero (SND x_tau) /\ b) T l) l) /\
 (!(x_tau:(string # p4$tau)). (\x_tau. arb_from_tau_gen_side uninit_zero (SND x_tau)) x_tau)’ suffices_by (
 gs[]
) >>
irule tau_induction >>
rpt strip_tac >- (
 simp[Once $ theorem "arb_from_tau_gen_side_def", Once $ definition "uninit_bit_side_def"]
) >- (
 simp[Once $ theorem "arb_from_tau_gen_side_def"]
) >- (
 simp[Once $ theorem "arb_from_tau_gen_side_def", Once $ definition "uninit_num_side_def"]
) >- (
 simp[Once $ theorem "arb_from_tau_gen_side_def"]
) >- (
 simp[Once $ theorem "arb_from_tau_gen_side_def"] >>
 rpt strip_tac >- (
  gvs[] >>
  ‘(λx_tau. arb_from_tau_gen_side uninit_zero (SND x_tau)) (x2,x1)’ suffices_by gs[] >>
  irule FOLDL_and_member >>
  metis_tac[]
 ) >- (
  simp[Once $ definition "uninit_bit_side_def"]
 ) >>
 gvs[] >>
 ‘(λx_tau. arb_from_tau_gen_side uninit_zero (SND x_tau)) (x5,x4)’ suffices_by gs[] >>
 irule FOLDL_and_member >>
 metis_tac[]
) >- (
 simp[Once $ theorem "arb_from_tau_gen_side_def"] >>
 simp[Once $ definition "uninit_bit_side_def"]
) >- (
 FULL_SIMP_TAC bool_ss [listTheory.FOLDL]
) >>
FULL_SIMP_TAC bool_ss [SND]
QED
val _ = translate declare_list_in_fresh_scope_exec_def;
Theorem declare_list_in_fresh_scope_exec_side_thm:
!uninit.
uninit <> uninit_arb ==>
!scope.
declare_list_in_fresh_scope_exec_side uninit scope
Proof
strip_tac >>
strip_tac >>
Cases_on ‘uninit’ >> (gs[]) >>
simp[Once $ definition "declare_list_in_fresh_scope_exec_side_def", arb_from_tau_gen_side_thm]
QED
val _ = update_precondition declare_list_in_fresh_scope_exec_side_thm;

(* Return *)

(* Sequence *)
val _ = translate is_empty_def;

(* Transition *)
val _ = translate is_v_str_def;
val _ = translate stmt_exec_trans_def;

(* Apply *)
val _ = translate index_not_const_def;

val _ = translate is_consts_exec_def;

(* Extern *)
val _ = translate lookup_ext_fun_def;


(* ??? Why? *)
val _ = translate oDROP_def;
val _ = translate oTAKE_def;

(* The whole stmt semantics *)
val _ = translate stmt_exec_stack_finish_def;
val _ = translate stmt_exec_seq_finish_def;
(* ~14 mins of nothing, then

<<HOL warning: ThmSetData.revise_data: 
  Theorems in set "compute":
    ADD<scratch$generated_definition_def>
  invalidated by DelConstant(scratch$generated_definition)>>
  
then 3 minutes of silence, then

     Translating stmt_exec

then around a minute before finishing.

Total time: 16m52s
*)
val _ = translate stmt_exec_def;
Theorem stmt_exec_side_thm:
!uninit.
uninit <> uninit_arb ==>
!ctx frame_list ascope g_scope_list status.
stmt_exec_side uninit ctx (ascope, g_scope_list, frame_list, status)
Proof
strip_tac >>
strip_tac >>
Cases_on ‘uninit’ >> (gs[]) >>
strip_tac >>
Induct >- (
 simp[Once $ theorem "stmt_exec_side_def"]
) >>
Induct >> Induct_on ‘p_2’ >> Induct_on ‘p_1’ >> (
(* Three duplicate cases *)
 Induct_on ‘p_1'’ >- (
  simp[Once $ theorem "stmt_exec_side_def"]
 ) >>
 Induct >> (rpt strip_tac >> (gvs[])) >- (
  simp[Once $ theorem "stmt_exec_side_def"] >>
  simp[Once $ theorem "stmt_exec_side_def"]
 ) >- (
  simp[Once $ theorem "stmt_exec_side_def"] >>
  simp[e_exec_side_thm] >>
  simp[Once $ theorem "stmt_exec_side_def"] >>
  simp[e_exec_side_thm]
 ) >- (
  (* Cond *)
  simp[Once $ theorem "stmt_exec_side_def"] >>
  simp[e_exec_side_thm] >>
  simp[Once $ theorem "stmt_exec_side_def"] >>
  simp[e_exec_side_thm]
 ) >- (
  (* Block *)
  simp[Once $ theorem "stmt_exec_side_def"] >>
  simp[Once $ theorem "stmt_exec_side_def"] >>
  simp[declare_list_in_fresh_scope_exec_side_thm]
 ) >- (
  (* Return *)
  simp[Once $ theorem "stmt_exec_side_def"] >>
  simp[e_exec_side_thm] >>
  simp[Once $ theorem "stmt_exec_side_def"] >>
  simp[e_exec_side_thm]
 ) >- (
  (* Sequence *)
  simp[Once $ theorem "stmt_exec_side_def"] >>
  rpt strip_tac >> (gvs[]) >>
  simp[Once $ theorem "stmt_exec_side_def"] >>
  rpt strip_tac >> (gvs[]) >>
  TRY $ qpat_x_assum ‘∀s p_2' ascope g_scope_list status'.
           stmt_exec_side uninit_zero (x89,x87,x85,x83,x81,x80)
             (ascope,g_scope_list,[(_,h::x34::x33,p_2')],status')’ (fn thm => assume_tac $ SIMP_RULE std_ss [Once $ theorem "stmt_exec_side_def"] thm) >>
  TRY $ qpat_x_assum ‘∀s s0 p_2' ascope g_scope_list status'.
           stmt_exec_side uninit_zero (x89,x87,x85,x83,x81,x80)
             (ascope,g_scope_list,[(_,h::x34::x33,p_2')],status')’ (fn thm => assume_tac $ SIMP_RULE std_ss [Once $ theorem "stmt_exec_side_def"] thm) >>
  gs[] >>
  TRY $ qpat_x_assum ‘∀s p_2' ascope g_scope_list status' x65 x64 x63 x62 x61 x60 x59 x58
             x57 x56 x55 x54 x53. _’ (fn thm => assume_tac $ Q.SPECL [‘s’, ‘x32::x31’, ‘ascope’, ‘g_scope_list’, ‘status_running’] thm) >>
  (* funn_ext case *)
  TRY $ qpat_x_assum ‘∀s s0 p_2' ascope g_scope_list status' x65 x64 x63 x62 x61 x60 x59 x58
             x57 x56 x55 x54 x53. _’ (fn thm => assume_tac $ Q.SPECL [‘s’, ‘x32::x31’, ‘ascope’, ‘g_scope_list’, ‘status_running’] thm) >>
  cases_on ‘h’ >> (gs[])
 ) >- (
  simp[Once $ theorem "stmt_exec_side_def"] >>
  simp[e_exec_side_thm] >>
  simp[Once $ theorem "stmt_exec_side_def"] >>
  simp[e_exec_side_thm]
 ) >- (
  simp[Once $ theorem "stmt_exec_side_def"] >>
  simp[e_exec_side_thm] >>
  simp[Once $ theorem "stmt_exec_side_def"] >>
  simp[e_exec_side_thm]
 ) >- (
  simp[Once $ theorem "stmt_exec_side_def"] >>
  simp[Once $ theorem "stmt_exec_side_def"] >>
  simp[Once $ theorem "stmt_exec_side_def"]
 )
)
QED


(*********************)
(** Frame semantics **)

val _ = translate scopes_to_pass_exec_def;
val _ = translate scopes_to_retrieve_exec_def;
val _ = translate map_to_pass_def;
val _ = translate tbl_to_pass_def;
val _ = translate is_d_none_in_def;

val _ = translate update_return_frame_exec_def;
val _ = translate copyout_exec_def;

(* 29s *)
val _ = translate frames_exec_def;
Theorem frames_exec_side_thm:
!uninit.
uninit <> uninit_arb ==>
!ctx frame_list ascope g_scope_list status.
frames_exec_side uninit ctx (ascope, g_scope_list, frame_list, status)
Proof
strip_tac >>
strip_tac >>
Cases_on ‘uninit’ >> (gs[]) >>
strip_tac >>
Induct >- (
 simp[Once $ definition "frames_exec_side_def"]
) >>
Induct >> Induct_on ‘p_2’ >>
simp[Once $ definition "frames_exec_side_def"] >>
simp[stmt_exec_side_thm]
QED

(********************)
(** Arch semantics **)
val _ = translate lookup_block_body_def;
val _ = translate oLASTN_def;

val _ = translate declare_list_in_scope_exec_def;
Theorem declare_list_in_scope_exec_side_thm:
!uninit.
uninit <> uninit_arb ==>
!t_scope scope.
declare_list_in_scope_exec_side uninit (t_scope,scope)
Proof
strip_tac >>
strip_tac >>
Cases_on ‘uninit’ >> (gs[]) >>
simp[Once $ definition "declare_list_in_scope_exec_side_def", arb_from_tau_gen_side_thm]
QED

val _ = translate AUPDATE_LIST_def;
val _ = translate var_star_updates_of_func_map_def;
val _ = translate var_star_updates_of_ext_map_def;
val _ = translate initialise_var_stars_def;

val _ = translate state_fin_exec_def;
val _ = translate set_fin_status_def;

(* 90s *)
val _ = translate arch_exec_def;
Theorem arch_exec_side_thm:
!uninit.
uninit <> uninit_arb ==>
!ctx arch_frame_list ascope g_scope_list status.
arch_exec_side uninit ctx (ascope, g_scope_list, arch_frame_list, status)
Proof
strip_tac >>
strip_tac >>
Cases_on ‘uninit’ >> (gs[]) >>
strip_tac >>
Induct >- (
 simp[Once $ definition "arch_exec_side_def"] >>
 simp[frames_exec_side_thm, declare_list_in_scope_exec_side_thm]
) >>
Induct >> (
 simp[Once $ definition "arch_exec_side_def"] >>
 simp[frames_exec_side_thm, declare_list_in_scope_exec_side_thm]
) >>
simp[Once $ definition "arch_exec_side_def"] >>
simp[frames_exec_side_thm, declare_list_in_scope_exec_side_thm]
QED

val _ = translate arch_multi_exec_def;
val _ = translate arch_multi_exec_total_def;
Theorem arch_multi_exec_total_side_thm:
!uninit.
uninit <> uninit_arb ==>
!actx arch_frame_list ascope g_scope_list status n.
arch_multi_exec_total_side uninit actx (ascope, g_scope_list, arch_frame_list, status) n
Proof
strip_tac >>
strip_tac >>
Cases_on ‘uninit’ >> (gs[]) >>
strip_tac >>
Induct_on ‘n’ >> (
 simp[Once $ theorem "arch_multi_exec_total_side_def"]
) >>
rpt strip_tac >- (
 gs[arch_exec_side_thm]
) >>
simp[Once $ theorem "arch_multi_exec_total_side_def"] >>
rpt strip_tac >- (
 PairCases_on ‘x1’ >>
 gs[arch_exec_side_thm]
) >>
gs[Once $ theorem "arch_multi_exec_total_side_def"] >>
PairCases_on ‘x1’ >>
‘arch_exec_side uninit_zero actx
          ((x10,x11,x12,x13),x14,x15,x16)’ suffices_by (
 rpt strip_tac >>
 res_tac
) >>
gs[arch_exec_side_thm]
QED

(* Note this is the only newly defined function, and the only one used by *)
Definition arch_multi_exec_total_zero_def:
 arch_multi_exec_total_zero actx astate n = arch_multi_exec_total uninit_zero actx astate n
End
val _ = translate arch_multi_exec_total_zero_def;
Theorem arch_multi_exec_total_zero_side_thm:
!actx arch_frame_list ascope g_scope_list status n.
arch_multi_exec_total_zero_side actx (ascope, g_scope_list, arch_frame_list, status) n
Proof
strip_tac >>
Induct >- (
 simp[Once $ definition "arch_multi_exec_total_zero_side_def"] >>
 simp[arch_multi_exec_total_side_thm]
) >>
Induct >> (
 simp[Once $ definition "arch_multi_exec_total_zero_side_def"] >>
 simp[arch_multi_exec_total_side_thm]
) >>
simp[Once $ definition "arch_multi_exec_total_zero_side_def"] >>
simp[arch_multi_exec_total_side_thm]
QED
val _ = update_precondition arch_multi_exec_total_zero_side_thm;

(******************************)
(** Core arch implementation **)

val _ = translate header_is_valid_def;

val _ = translate header_set_valid_def;

val _ = translate header_set_invalid_def;

(* Common extern functions: *)
val _ = translate oTAKE_DROP_def;
val _ = translate v2w16s'''_def;
val _ = translate header_entries2v_def;
val _ = translate v2w16s''_def;
val _ = translate get_checksum_incr''_def;

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

(* Shared over all architectures, so goes here *)
val _ = translate p4_append_input_list_def;
val _ = translate p4_get_output_list_def;
val _ = translate word_def;

val _ = ml_prog_update (close_module NONE);

val _ = export_theory ();
