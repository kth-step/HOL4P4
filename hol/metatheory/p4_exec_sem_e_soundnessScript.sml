open HolKernel boolLib Parse bossLib;

val _ = new_theory "p4_exec_sem_e_soundness";

open p4Lib;
open ottTheory listTheory rich_listTheory arithmeticTheory p4_auxTheory p4Theory p4_exec_semTheory;

Definition e_exec_sound:
 (e_exec_sound (type:('a itself)) e =
  !(ctx:'a ctx) g_scope_list scopes_stack e' frame_list.
  e_exec (get_e_ctx ctx) g_scope_list scopes_stack e = SOME (e', frame_list) ==>
  e_red ctx g_scope_list scopes_stack e e' frame_list)
End

Definition x_e_exec_sound:
 (x_e_exec_sound type (x:string, e) = e_exec_sound type e)
End

Definition l_sound_exec:
 (l_sound_exec type [] = T) /\
 (l_sound_exec type ((h::t):e list) = 
  (e_exec_sound type h /\ l_sound_exec type t))
End

Definition l_sound:
 (l_sound type [] = T) /\
 (l_sound type (l:e list) = 
  !x e. (SOME e = oEL x l) ==> e_exec_sound type e)
End

Theorem l_sound_cons:
!type h l. l_sound type (h::l) ==> l_sound type l
Proof
rpt strip_tac >>
Induct_on `l` >> (
 fs [l_sound]
) >>
rpt strip_tac >>
PAT_X_ASSUM ``!x e. _`` (fn thm => ASSUME_TAC (SPECL [``SUC x``, ``e:e``] thm)) >>
rfs [] >>
`oEL x (h'::l) = oEL (SUC x) (h::h'::l)` suffices_by (
 fs []
) >>
Induct_on `x` >> (
 fs [oEL_def]
)
QED

Theorem l_sound_equiv:
!type l. l_sound type l <=> l_sound_exec type l
Proof
rpt strip_tac >>
EQ_TAC >| [
 Induct_on `l` >> (
  fs [l_sound, l_sound_exec]
 ) >>
 rpt strip_tac >| [
  PAT_X_ASSUM ``!x e. _`` (fn thm => ASSUME_TAC (SPEC ``0:num`` thm)) >>
  fs [oEL_def],

  `l_sound type (h::l)` suffices_by (
   METIS_TAC [l_sound_cons]
  ) >>
  METIS_TAC [l_sound]
 ],

 Induct_on `l` >> (
  fs [l_sound, l_sound_exec]
 ) >>
 NTAC 3 strip_tac >>
 Induct_on `x` >> (
  fs [oEL_def]
 ) >>
 `!x e. SOME e = oEL x l ==> e_exec_sound type e` suffices_by (
  METIS_TAC [oEL_cons_PRE]
 ) >>
 fs [] >>
 Cases_on `l` >- (
  fs [oEL_def]
 ) >>
 METIS_TAC [l_sound]
]
QED

Theorem l_sound_MEM:
 !type e l.
 MEM e l ==>
 l_sound type l ==>
 e_exec_sound type e
Proof
Induct_on `l` >> (
 fs []
) >>
rpt strip_tac >> (
 fs [l_sound_equiv, l_sound_exec]
)
QED

Definition x_e_l_exec_sound:
 (x_e_l_exec_sound type (x_e_l:(string # e) list) = l_sound type (MAP SND x_e_l))
End

Theorem e_concat_exec_sound_red:
!type e1 e2.
e_exec_sound type e1 ==>
e_exec_sound type e2 ==>
e_exec_sound type (e_concat e1 e2)
Proof
fs [e_exec_sound] >>
rpt strip_tac >>
fs [e_exec_def] >>
Cases_on `is_v_bit e1` >> Cases_on `is_v_bit e2` >> (
 fs []
) >| [
 Cases_on `e_exec_concat e1 e2` >> (
  fs []
 ) >>
 Cases_on `e1` >> Cases_on `e2` >> (
  fs [is_v_bit_def]
 ) >>
 Cases_on `v` >> Cases_on `v'` >> (
  fs [e_exec_concat_def]
 ) >>
 Cases_on `x` >> (
  fs []
 ) >>
 rw [] >>
 irule ((valOf o find_clause_e_red) "e_concat_v") >>
 fs [clause_name_def],

 Cases_on `e_exec (get_e_ctx ctx) g_scope_list scopes_stack e2` >> (
  fs [e_exec_def]
 ) >>
 Cases_on `x` >> (
  fs []
 ) >>
 Cases_on `e1` >> (
  fs [is_v_bit_def]
 ) >>
 Cases_on `v` >> (
  fs [is_v_bit_def]
 ) >>
 metis_tac[((valOf o find_clause_e_red) "e_concat_arg2"), clause_name_def],

 Cases_on `e_exec (get_e_ctx ctx) g_scope_list scopes_stack e1` >> (
  fs [e_exec_def]
 ) >>
 Cases_on `x` >> (
  fs []
 ) >>
 Cases_on `e2` >> (
  fs [is_v_bit_def]
 ) >>
 Cases_on `v` >> (
  fs [is_v_bit_def]
 ) >>
 metis_tac[((valOf o find_clause_e_red) "e_concat_arg1"), clause_name_def],


 Cases_on `e_exec (get_e_ctx ctx) g_scope_list scopes_stack e1` >> (
  fs [e_exec_def]
 ) >>
 Cases_on `x` >> (
  fs []
 ) >>
 metis_tac[((valOf o find_clause_e_red) "e_concat_arg1"), clause_name_def]
]
QED

Theorem e_slice_exec_sound_red:
!type e1 e2 e3.
e_exec_sound type e1 ==>
e_exec_sound type e2 ==>
e_exec_sound type e3 ==>
e_exec_sound type (e_slice e1 e2 e3)
Proof
fs [e_exec_sound] >>
rpt strip_tac >>
fs [e_exec_def] >>
Cases_on `is_v_bit e1` >> (
 fs []
) >| [
 Cases_on `e_exec_slice e1 e2 e3` >> (
  fs []
 ) >>
 Cases_on `e1` >> Cases_on `e2` >> Cases_on `e3` >> (
  fs [is_v_bit_def]
 ) >>
 Cases_on `v` >> Cases_on `v'` >> Cases_on `v''` >> (
  fs [e_exec_slice_def]
 ) >>
 rw [] >>
 gvs[AllCaseEqs()] >>
 irule ((valOf o find_clause_e_red) "e_slice_v") >>
 fs [clause_name_def] >>
 Cases_on ‘p’ >> Cases_on ‘p'’ >> Cases_on ‘p''’ >>
 fs[slice_def, slice'_def, AllCaseEqs()],

 Cases_on `e_exec (get_e_ctx ctx) g_scope_list scopes_stack e1` >> (
  fs [e_exec_def]
 ) >>
 Cases_on `x` >> (
  fs []
 ) >>
 Cases_on `e2` >> Cases_on `e3` >> (
  fs [is_v_bit_def]
 ) >>
 Cases_on `v` >> Cases_on `v'` >> (
  fs [is_v_bit_def]
 ) >>
 METIS_TAC [((valOf o find_clause_e_red) "e_slice_arg1"), clause_name_def]
]
QED

Theorem e_acc_exec_sound_red:
!type e x.
e_exec_sound type e ==>
e_exec_sound type (e_acc e x)
Proof
fs [e_exec_sound] >>
rpt strip_tac >>
fs [e_exec_def] >>
Cases_on `is_v e` >> (
 fs []
) >| [
 Cases_on `e_exec_acc (e_acc e x)` >> (
  fs []
 ) >>
 Cases_on `e` >> (
  fs [is_v_def]
 ) >>
 Cases_on `v` >> (
  fs [e_exec_acc_def]
 ) >> (
  Cases_on `FIND (\(k,v). k = x) l` >> (
   fs []
  ) >>
  PairCases_on `x''` >>
  fs [] >>
  rw []
 ) >| [
  irule ((valOf o find_clause_e_red) "e_s_acc"),

  irule ((valOf o find_clause_e_red) "e_h_acc")
 ] >> (
  fs [clause_name_def, FIND_def] >>
  Cases_on `z` >>
  IMP_RES_TAC index_find_first >>
  Cases_on `r` >>
  fs []
 ),

 Cases_on `e_exec (get_e_ctx ctx) g_scope_list scopes_stack e` >- (
  fs []
 ) >>
 Cases_on `x'` >>
 fs [] >>
 rw [] >>
 irule ((valOf o find_clause_e_red) "e_acc_arg1") >>
 fs [clause_name_def]
]
QED

Theorem band'_eq_band:
!a b.
LENGTH a = LENGTH b ==>
band' a b = band a b
Proof
gs[band'_def, bitstringTheory.band_def, bitstringTheory.bitwise_def, pairTheory.ELIM_UNCURRY]
QED

Theorem bor'_eq_bor:
!a b.
LENGTH a = LENGTH b ==>
bor' a b = bor a b
Proof
gs[bor'_def, bitstringTheory.bor_def, bitstringTheory.bitwise_def, pairTheory.ELIM_UNCURRY]
QED

Theorem e_binop_exec_sound_red:
!type e1 e2 b.
e_exec_sound type e1 ==>
e_exec_sound type e2 ==>
e_exec_sound type (e_binop e1 b e2)
Proof
fs [e_exec_sound] >>
rpt strip_tac >>
Cases_on `is_v e1` >> Cases_on `is_v e2` >| [
 (* Both operands are fully reduced *)
 Cases_on `e1` >> (
  fs [is_v_def]
 ) >>
 Cases_on `is_short_circuitable b` >- (
  (* Short-circuit *)
  Cases_on `b` >> Cases_on `v` >> (
   fs [is_short_circuitable_def, e_exec_def, is_v_def, e_exec_short_circuit_def]
  ) >> (
   Cases_on `b` >> (
    fs [is_short_circuitable_def, e_exec_def, is_v_def, e_exec_short_circuit_def]
   )
  ) >| [
   irule ((valOf o find_clause_e_red) "e_bin_and2") >>
   fs [clause_name_def],
   
   irule ((valOf o find_clause_e_red) "e_bin_and1") >>
   fs [clause_name_def],
  
   irule ((valOf o find_clause_e_red) "e_bin_or1") >>
   fs [clause_name_def],

   irule ((valOf o find_clause_e_red) "e_bin_or2") >>
   fs [clause_name_def]
  ]
 ) >>
 fs [] >>
 Cases_on `e_exec_binop (e_v v) b e2` >> (
  fs [e_exec_def] >>
  rw []
 ) >>
 (* Different concrete cases *)
 Cases_on `b` >> (
  Cases_on `e2` >> (
   fs [is_v_def]
  ) >>
  Cases_on `v` >> Cases_on `v'` >> (
   fs [e_exec_binop_def, binop_exec_def]
  ) >>
  rw []
 ) >| [
   Cases_on `bitv_binop binop_mul p p'` >> (
    fs []
   ) >>
   Cases_on `x` >> (
    fs []
   ) >>
   irule ((valOf o find_clause_e_red) "e_mul"),

   Cases_on `bitv_binop binop_div p p'` >> (
    fs []
   ) >>
   Cases_on `x` >> (
    fs []
   ) >>
   irule ((valOf o find_clause_e_red) "e_div"),

   Cases_on `bitv_binop binop_mod p p'` >> (
    fs []
   ) >>
   Cases_on `x` >> (
    fs []
   ) >>
   irule ((valOf o find_clause_e_red) "e_mod"),

   Cases_on `bitv_binop binop_add p p'` >> (
    fs []
   ) >>
   Cases_on `x` >> (
    fs []
   ) >>
   irule ((valOf o find_clause_e_red) "e_add"),

   Cases_on `bitv_binop binop_sat_add p p'` >> (
    fs []
   ) >>
   Cases_on `x` >> (
    fs []
   ) >>
   irule ((valOf o find_clause_e_red) "e_sat_add"),

   Cases_on `bitv_binop binop_sub p p'` >> (
    fs []
   ) >>
   Cases_on `x` >> (
    fs []
   ) >>
   irule ((valOf o find_clause_e_red) "e_sub"),

   Cases_on `bitv_binop binop_sat_sub p p'` >> (
    fs []
   ) >>
   Cases_on `x` >> (
    fs []
   ) >>
   irule ((valOf o find_clause_e_red) "e_sat_sub"),

   irule ((valOf o find_clause_e_red) "e_shl"),

   Cases_on ‘p’ >> Cases_on ‘p'’ >> (
    fs []
   ) >>
   gs[binop_exec_def, AllCaseEqs()] >> (
    Cases_on `x` >> (
     fs []
    ) >>
    irule ((valOf o find_clause_e_red) "e_shr") >>
    gs[bitv_bl_binop_def, bitstringTheory.shiftr_def]
   ) >| [
    ALL_TAC,
    
    gvs[] >>
    ‘LENGTH q − v2n q' = 0’ by gs[] >>
    ASM_REWRITE_TAC[] >>
    gs[]
   ],

   Cases_on `bitv_binpred binop_le p p'` >> (
    fs []
   ) >>
   Cases_on `x` >> (
    fs []
   ) >>
   irule ((valOf o find_clause_e_red) "e_le"),

   Cases_on `bitv_binpred binop_ge p p'` >> (
    fs []
   ) >>
   Cases_on `x` >> (
    fs []
   ) >>
   irule ((valOf o find_clause_e_red) "e_ge"),

   Cases_on `bitv_binpred binop_lt p p'` >> (
    fs []
   ) >>
   Cases_on `x` >> (
    fs []
   ) >>
   irule ((valOf o find_clause_e_red) "e_lt"),

   Cases_on `bitv_binpred binop_gt p p'` >> (
    fs []
   ) >>
   Cases_on `x` >> (
    fs []
   ) >>
   irule ((valOf o find_clause_e_red) "e_gt"),

   irule ((valOf o find_clause_e_red) "e_neq_bool"),

   irule ((valOf o find_clause_e_red) "e_neq"),

   irule ((valOf o find_clause_e_red) "e_eq_bool"),

   irule ((valOf o find_clause_e_red) "e_eq"),

   Cases_on ‘p’ >> Cases_on ‘p'’ >> Cases_on ‘x’ >> (
    gs[binop_exec_def]
   ) >>
   irule ((valOf o find_clause_e_red) "e_and") >>
   ‘band q q' = band' q q'’ by (
    metis_tac[band'_eq_band]
   ) >>
   gs[bitv_bl_binop_def],

   irule ((valOf o find_clause_e_red) "e_xor"),

   Cases_on ‘p’ >> Cases_on ‘p'’ >> Cases_on ‘x’ >> (
    gs[binop_exec_def]
   ) >>
   irule ((valOf o find_clause_e_red) "e_or") >>
   ‘bor q q' = bor' q q'’ by (
    metis_tac[bor'_eq_bor]
   ) >>
   gs[bitv_bl_binop_def]
 ] >> (
  fs [clause_name_def]
 ),

 (* Second operand is not fully reduced *)
 Cases_on `e1` >> (
  fs [is_v_def]
 ) >>
 Cases_on `is_short_circuitable b` >- (
  (* Short-circuit *)
  fs [] >>
  rw [] >>
  Cases_on `v` >> (
   fs [is_short_circuitable_def, e_exec_def, is_v_def, e_exec_short_circuit_def]
  ) >>
  Cases_on `b'` >> Cases_on `b` >> (
   fs [is_short_circuitable_def, e_exec_def, is_v_def, e_exec_short_circuit_def]
  ) >| [
   irule ((valOf o find_clause_e_red) "e_bin_and2") >>
   fs [clause_name_def],

   irule ((valOf o find_clause_e_red) "e_bin_or1") >>
   fs [clause_name_def],
   
   irule ((valOf o find_clause_e_red) "e_bin_and1") >>
   fs [clause_name_def],

   irule ((valOf o find_clause_e_red) "e_bin_or2") >>
   fs [clause_name_def]
  ]
 ) >>
 Cases_on `e_exec (get_e_ctx ctx) g_scope_list scopes_stack e2` >> (
  fs [e_exec_def]
 ) >>
 Cases_on `x` >> (
  fs [is_v_def]
 ) >>
 METIS_TAC [((valOf o find_clause_e_red) "e_binop_arg2"), clause_name_def],

 (* First operand is not fully reduced *)
 Cases_on `e_exec (get_e_ctx ctx) g_scope_list scopes_stack e1` >> (
  fs [e_exec_def]
 ) >> (
  Cases_on `e1` >> (
   fs [is_v_def]
  ) >> (
   Cases_on `x` >>
   fs [] >>
   METIS_TAC [((valOf o find_clause_e_red) "e_binop_arg1"), clause_name_def]
  )
 ),

 (* No operand is fully reduced *)
 Cases_on `e_exec (get_e_ctx ctx) g_scope_list scopes_stack e1` >> (
  fs [e_exec_def]
 ) >> (
  Cases_on `e1` >> (
   fs [is_v_def]
  ) >> (
   Cases_on `x` >>
   fs [] >>
   METIS_TAC [((valOf o find_clause_e_red) "e_binop_arg1"), clause_name_def]
  )
 )
]
QED

Theorem match_exec_eq_match:
!h0 h1.
match_exec h0 h1 = match h0 h1
Proof
gs[match_exec_def, match_def, p4_match_range_exec_def, p4_match_range_def,
   p4_match_mask_exec_def, p4_match_mask_def]
QED

Theorem match_all_exec_eq_match_all:
!v_s_l.
match_all_exec v_s_l = match_all v_s_l
Proof
Induct >> (
 gs[match_all_exec_def, match_all_def]
) >>
rpt strip_tac >>
PairCases_on ‘h’ >>
gs[match_all_exec_def, match_all_def, match_exec_eq_match]
QED

Theorem e_select_exec_sound_red:
!type e l s.
e_exec_sound type e ==>
e_exec_sound type (e_select e l s)
Proof
gs[e_exec_sound] >>
rpt strip_tac >>
Cases_on ‘is_v e’ >- (
 Cases_on ‘e’ >> (
  gs[is_v_def]
 ) >>
 gvs[e_exec_def, e_exec_select_def, is_v_def, AllCaseEqs()] >> (
  irule ((valOf o find_clause_e_red) "e_sel_acc") >>
  gs[sel_def, clause_name_def]
 ) >>
 gs[match_all_exec_eq_match_all]
) >>
gvs[e_exec_def, e_exec_select_def, match_all_exec_eq_match_all, AllCaseEqs()] >>
irule ((valOf o find_clause_e_red) "e_sel_arg") >>
gs[clause_name_def]
QED

Theorem e_unop_exec_sound_red:
!type e u.
e_exec_sound type e ==>
e_exec_sound type (e_unop u e)
Proof
fs[e_exec_sound] >>
rpt strip_tac >>
Cases_on `is_v e` >| [
 Cases_on `e_exec_unop u e` >> (
  gs[e_exec_def] >>
  rw[]
 ) >>
 Cases_on `e` >> (
  gs[is_v_def]
 ) >>
 (* Different concrete cases *)
 Cases_on `u` >> (
  Cases_on `v` >> (
   gs [e_exec_unop_def, unop_exec_def]
  ) >>
  rw[]
 ) >| [
  irule ((valOf o find_clause_e_red) "e_neg_bool"),

  PairCases_on ‘p’ >>
  gs[unop_exec_def] >>
  Cases_on ‘x’ >> (
   gvs[]
  ) >>
  irule ((valOf o find_clause_e_red) "e_compl") >>
  gs[bitv_bl_unop_def, bitv_unop_def, bitstringTheory.bnot_def, bitv_1comp_def],

  PairCases_on ‘p’ >>
  gvs[e_exec_unop_def, unop_exec_def] >>
  irule ((valOf o find_clause_e_red) "e_neg_signed"),

  irule ((valOf o find_clause_e_red) "e_un_plus")
 ] >>
 gs[clause_name_def],

 Cases_on `e_exec (get_e_ctx ctx) g_scope_list scopes_stack e` >> (
  gs[e_exec_def]
 ) >>
 Cases_on `x` >>
 gs[] >>
 METIS_TAC [(valOf o find_clause_e_red) "e_unop_arg", clause_name_def]
]
QED

Theorem oHD_SOME:
!l h.
oHD l = SOME h ==>
HD l = h
Proof
Induct >> (
 fs[listTheory.oHD_thm]
)
QED

Theorem e_cast_exec_sound_red:
!type e c.
e_exec_sound type e ==>
e_exec_sound type (e_cast c e)
Proof
fs [e_exec_sound] >>
rpt strip_tac >>
Cases_on `is_v e` >| [
 Cases_on `e_exec_cast c e` >> (
  fs [e_exec_def] >>
  rw []
 ) >>
 Cases_on `e` >> (
  fs [is_v_def]
 ) >>
 (* Different concrete cases *)
 Cases_on `c` >> (
  Cases_on `v` >> (
   fs [e_exec_cast_def, cast_exec_def]
  ) >>
  rw []
 ) >| [
  irule ((valOf o find_clause_e_red) "e_cast_bool") >>
  fs [clause_name_def],

  irule ((valOf o find_clause_e_red) "e_cast_bitv") >>
  fs [clause_name_def],

  Cases_on `x` >> (
   fs[to_bool_cast_exec_def, AllCaseEqs()]
  ) >>
  irule ((valOf o find_clause_e_red) "e_cast_to_bool") >>
  Cases_on `p` >> Cases_on `q` >> (
   fs [clause_name_def, to_bool_cast_def, oHD_SOME]
  )
 ],

 Cases_on `e_exec (get_e_ctx ctx) g_scope_list scopes_stack e` >> (
  fs [e_exec_def]
 ) >>
 Cases_on `x` >>
 fs [] >>
 METIS_TAC [(valOf o find_clause_e_red) "e_cast_arg", clause_name_def]
]
QED

(*
Definition init_out_v_gen_equiv_list_def:
init_out_v_gen_equiv_list l = (MAP (λ(x':string,v'). (x',init_out_v_gen v')) l = MAP (λ(x',v'). (x',init_out_v v')) l)
End

Theorem init_out_v_gen_equiv:
!v.
init_out_v_gen v = init_out_v v
Proof
‘(!v. (\v. init_out_v_gen v = init_out_v v) v) /\
 (!l. init_out_v_gen_equiv_list l) /\
 (!(p:(string # v)). (\p. init_out_v_gen (SND p) = init_out_v (SND p)) p)’ suffices_by (
 gs[]
) >>
irule v_induction >>
gs[init_out_v_gen_equiv_list_def] >>
rpt strip_tac >> (
 gs[init_out_v_gen_def, init_out_v_def, uninit_string_def, uninit_bit_def]
) >- (
 Induct_on ‘l’ >> (
  gs[init_out_v_gen_def, init_out_v_def]
 ) >>
 rpt strip_tac >>
 Cases_on ‘h’ >>
 gs[init_out_v_gen_def, init_out_v_def]
) >- (
 Induct_on ‘l’ >> (
  gs[init_out_v_gen_def, init_out_v_def]
 ) >>
 rpt strip_tac >>
 Cases_on ‘h’ >>
 gs[init_out_v_gen_def, init_out_v_def]
) >- (
 Induct_on ‘p’ >> (
  gs[init_out_v_gen_def, init_out_v_def, uninit_bit_def]
 )
) >- (
 Cases_on ‘p’ >>
 gs[]
)
QED
*)

Theorem slice'_imp:
!v bl v1 bl1 v2 bl2 bitv.
slice' (v,bl) (v1,bl1) (v2,bl2) = SOME bitv ==>
slice (v,bl) (v1,bl1) (v2,bl2) = bitv
Proof
gs[slice'_def, slice_def]
QED

Theorem slice_lval'_imp:
!v e0 e v'.
slice_lval' v e0 e = SOME v' ==>
slice_lval v e0 e = SOME v'
Proof
gs[slice_lval'_def] >>
rpt strip_tac >>
gvs[slice_lval_def, slice'_imp, AllCaseEqs()]
QED

Theorem lookup_lval'_imp:
!lval ss v.
lookup_lval' ss lval = SOME v ==>
lookup_lval ss lval = SOME v
Proof
Induct >> (
 gs[lookup_lval'_def, lookup_lval_def] >>
 rpt strip_tac >>
 gvs[AllCaseEqs()] >>
 metis_tac[slice_lval'_imp]
)
QED

(* TODO: ARB *)
Theorem init_out_v_cake_eq_init_out_v:
init_out_v_cake = init_out_v
Proof
cheat
QED

Theorem update_arg_for_newscope_imp:
!scopes l1 l2 scopes'.
update_arg_for_newscope_exec scopes l1 l2 = SOME scopes' ==>
update_arg_for_newscope scopes l1 l2 = SOME scopes'
Proof
Cases_on ‘l2’ >>
Cases_on ‘r’ >>
gs[update_arg_for_newscope_exec_def, update_arg_for_newscope_def, one_arg_val_for_newscope_exec_def,
   one_arg_val_for_newscope_def (* , init_out_v_gen_equiv *), lookup_lval'_imp,
   init_out_v_cake_eq_init_out_v, AllCaseEqs()] >>
rpt strip_tac >>
gvs[] >>
metis_tac[lookup_lval'_imp]
QED

(* TODO: Use oFOLDL instead if possible *)
Theorem FOLDL_NONE:
!l f.
(!l'. f NONE l' = NONE) ==>
FOLDL f NONE l = NONE
Proof
Induct >> (
 gs[]
)
QED

(* TODO: Use oFOLDL instead if possible *)
Theorem FOLDL_IMP:
!f f' a b res.
(!g. f' NONE g = NONE) ==>
(!c d e. (f' c d = SOME e) ==> (f c d = SOME e)) ==>
FOLDL f' a b = SOME res ==>
FOLDL f a b = SOME res
Proof
Induct_on ‘b’ >> (
 gs[]
) >>
rpt strip_tac >>
qpat_x_assum ‘!f f'. _’ (fn thm => irule thm) >>
qexists_tac ‘f'’ >>
gs[] >>
Cases_on ‘f' a h’ >- (
 gs[] >>
 Cases_on ‘b’ >> (
  gs[FOLDL_NONE]
 )
) >>
res_tac >>
ASM_REWRITE_TAC[]
QED

Theorem update_arg_for_newscope_exec_NONE:
!d_x_e scopes_stack g_scope_list. update_arg_for_newscope_exec (scopes_stack ++ g_scope_list) NONE d_x_e = NONE
Proof
strip_tac >>
PairCases_on ‘d_x_e’ >>
gs[update_arg_for_newscope_exec_def]
QED

Theorem copyin_exec_equiv:
!s_l d_l l g_scope_list scopes_stack scopes_stack'.
copyin_exec s_l d_l l g_scope_list scopes_stack = SOME scopes_stack' ==>
copyin s_l d_l l g_scope_list scopes_stack = SOME scopes_stack'
Proof
gs[copyin_exec_def, copyin_def, all_arg_update_for_newscope_exec_def, all_arg_update_for_newscope_def] >>
rw[] >>
irule FOLDL_IMP >>
qexistsl_tac [‘update_arg_for_newscope_exec (scopes_stack ++ g_scope_list)’] >>
gs[update_arg_for_newscope_exec_NONE] >>
metis_tac[update_arg_for_newscope_imp]
QED

Theorem e_call_exec_sound_red:
!type f l.
l_sound type l ==>
e_exec_sound type (e_call f l)
Proof
fs [e_exec_sound] >>
rpt strip_tac >>
PairCases_on `ctx` >>
rename1 `(apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)` >>
fs [e_exec_def, get_e_ctx_def] >>
Cases_on `lookup_funn_sig_body f func_map b_func_map ext_map` >> (
 fs []
) >>
Cases_on `x` >> (
 fs []
) >>
Cases_on `unred_arg_index (MAP SND r) l` >> (
 fs []
) >| [
 (* e_call_newframe *)
 Cases_on `copyin_exec (MAP FST r) (MAP SND r) l g_scope_list scopes_stack` >> (
  fs []
 ) >>
 IMP_RES_TAC map_tri_zip12 >>
 gvs[] >>
 METIS_TAC [copyin_exec_equiv, ISPEC ``ZIP (l,r):(e # string # d) list`` ((valOf o find_clause_e_red) "e_call_newframe"), unred_arg_index_NONE,
            clause_name_def],

 (* e_call_args *)
 gs[AllCaseEqs()] >>
(*
 Cases_on `e_exec (ext_map,func_map,b_func_map) g_scope_list scopes_stack (EL x l)` >> (
  fs []
 ) >>
 Cases_on `x'` >>
 fs [] >>
*)
 rw [] >>
 Q.SUBGOAL_THEN `((MAP (\(a_,b_,c_,d_). a_) (ZIP (l,ZIP (LUPDATE e'' x l,r))) = l) /\
                 (MAP (\(a_,b_,c_,d_). b_) (ZIP (l,ZIP (LUPDATE e'' x l,r))) = LUPDATE e'' x l) /\
                 (MAP (\(a_,b_,c_,d_). c_) (ZIP (l,ZIP (LUPDATE e'' x l,r))) = MAP FST r) /\
                 (MAP (\(a_,b_,c_,d_). d_) (ZIP (l,ZIP (LUPDATE e'' x l,r))) = MAP SND r) /\
                 (MAP (\(a_,b_,c_,d_). (c_,d_)) (ZIP (l,ZIP (LUPDATE e'' x l,r))) = r))` (
  fn thm => (irule (SIMP_RULE std_ss [thm] (ISPEC ``ZIP (l:e list, ZIP ((LUPDATE e'' x l), r:(string # d) list))``
                                                  ((valOf o find_clause_e_red) "e_call_args"))))
 ) >- (
  subgoal `LENGTH l = LENGTH (ZIP (LUPDATE e'' x l,r))` >- (
   fs [LENGTH_ZIP]
  ) >>
  subgoal `LENGTH (LUPDATE e'' x l) = LENGTH r` >- (
   fs []
  ) >>
  fs [map_quad_zip112]
 ) >>
 fs [clause_name_def] >>
 rpt strip_tac >| [
  fs [lookup_funn_sig_def],

  Cases_on `l` >> (
   fs [unred_arg_index_empty]
  ) >>
  fs [e_exec_sound, l_sound] >>
  PAT_X_ASSUM ``!x' e. _`` (fn thm => ASSUME_TAC (SPECL [``x:num``, ``(EL x (h::t)):e``] thm)) >>
  IMP_RES_TAC unred_arg_index_max >>
  gvs[oEL_EQ_EL, get_e_ctx_def]
 ]
]
QED

Theorem get_v_eq:
!h v.
get_v h = SOME v <=>
v_of_e h = SOME v
Proof
Induct >> (
 gs[get_v_def, v_of_e_def]
)
QED

Theorem vl_of_el_exec_imp:
!e_l v_l.
vl_of_el_exec e_l = SOME v_l ==>
vl_of_el e_l = v_l
Proof
gs[vl_of_el_exec_def, vl_of_el_def] >>
Induct >- (
 gs[vl_of_el_exec_def]
) >>
rpt strip_tac >>
gvs[vl_of_el_exec_def, get_v_eq, AllCaseEqs()]
QED

Theorem e_struct_exec_sound_red:
!type x_e_l.
x_e_l_exec_sound type x_e_l ==>
e_exec_sound type (e_struct x_e_l)
Proof
fs [e_exec_sound] >>
rpt strip_tac >>
fs [e_exec_def] >>
Cases_on `unred_mem_index (MAP SND x_e_l)` >> (
 fs []
) >| [
 gvs[AllCaseEqs()] >>
 subgoal `?x_l. x_l = MAP FST x_e_l` >- (
  fs []
 ) >>
 subgoal `?e_l. e_l = MAP SND x_e_l` >- (
  fs []
 ) >>
 imp_res_tac vl_of_el_exec_imp >>
 gs[] >> 
 qpat_x_assum ‘vl_of_el (MAP SND x_e_l) = v_l’ (fn thm => gs[GSYM thm]) >>
 Q.SUBGOAL_THEN `((MAP ( \ (f_,e_,v_). (f_,e_)) (ZIP (x_l,ZIP (e_l,vl_of_el (MAP SND x_e_l))))) = x_e_l) /\
                 ((MAP ( \ (f_,e_,v_). (f_,v_)) (ZIP (x_l,ZIP (e_l,vl_of_el (MAP SND x_e_l))))) = ZIP (MAP FST x_e_l,vl_of_el (MAP SND x_e_l)))` (fn thm => (irule (SIMP_RULE std_ss [thm] (ISPEC ``ZIP (x_l:string list, ZIP (e_l:e list, vl_of_el (MAP SND (x_e_l:(string # e) list))))``
                                                  ((valOf o find_clause_e_red) "e_eStruct_to_v"))))) >- (
  subgoal `LENGTH (MAP FST x_e_l) = LENGTH (ZIP (MAP SND x_e_l,vl_of_el (MAP SND x_e_l)))` >- (
   fs [LENGTH_ZIP_MIN, MIN_DEF] >>
   CASE_TAC >>
   fs [vl_of_el_LENGTH]
  ) >>
  fs [map_tri_zip12] >>
  subgoal `LENGTH (MAP SND x_e_l) = LENGTH (vl_of_el (MAP SND x_e_l))` >- (
   fs [vl_of_el_LENGTH]
  ) >>
  fs [map_tri_zip12, listTheory.MAP_ZIP, GSYM UNZIP_MAP]
 ) >>
 fs [clause_name_def] >>
 rpt strip_tac >> (
  fs [lambda_unzip_tri] >>
  subgoal `LENGTH (MAP FST x_e_l) = LENGTH (ZIP (MAP SND x_e_l,vl_of_el (MAP SND x_e_l)))` >- (
   fs [LENGTH_ZIP_MIN, MIN_DEF] >>
   CASE_TAC >>
   fs [vl_of_el_LENGTH]
  ) >>
  fs [UNZIP_ZIP] >>
  subgoal `LENGTH (MAP SND x_e_l) = LENGTH (vl_of_el (MAP SND x_e_l))` >- (
   fs [vl_of_el_LENGTH]
  ) >>
  fs [UNZIP_ZIP, unred_mem_index_NONE]
 ),

 Cases_on `e_exec (get_e_ctx ctx) g_scope_list scopes_stack (EL x (MAP SND x_e_l))` >> (
  fs []
 ) >>
 gvs[AllCaseEqs()] >> (
  (* Hack... *)
  TRY $ PairCases_on `x'` >>
  fs [] >>
  rw [] >>
  Q.SUBGOAL_THEN `((MAP ( \ (f_,e_,e'_). (f_,e_)) (ZIP (MAP FST x_e_l, ZIP (MAP SND x_e_l, LUPDATE e'' x (MAP SND x_e_l))))) = x_e_l) /\
                  ((MAP ( \ (f_,e_,e'_). (f_,e'_)) (ZIP (MAP FST x_e_l,ZIP (MAP SND x_e_l, LUPDATE e'' x (MAP SND x_e_l))))) = ZIP (MAP FST x_e_l, LUPDATE e'' x (MAP SND x_e_l)))`
   (fn thm => (irule (SIMP_RULE std_ss [thm] (ISPEC ``ZIP (MAP FST (x_e_l:(string # e) list), ZIP (MAP SND x_e_l, LUPDATE e'' x (MAP SND x_e_l)))``
                                                   ((valOf o find_clause_e_red) "e_eStruct"))))) >- (
   subgoal `LENGTH (MAP FST x_e_l) = LENGTH (ZIP (MAP SND x_e_l, LUPDATE e'' x (MAP SND x_e_l)))` >- (
    fs []
   ) >>
   fs [map_tri_zip12] >>
   subgoal `LENGTH (MAP SND x_e_l) = LENGTH (LUPDATE e'' x (MAP SND x_e_l))` >- (
    fs [vl_of_el_LENGTH]
   ) >>
   fs [map_tri_zip12, listTheory.MAP_ZIP, GSYM UNZIP_MAP]
  ) >>
  fs [clause_name_def] >>
  qexistsl_tac [`e''`, `x`] >>
  rpt strip_tac >> (
   fs [lambda_unzip_tri]
  ) >>
  fs [x_e_l_exec_sound] >>
  IMP_RES_TAC unred_mem_index_in_range >>
  subgoal `MEM (EL x (MAP SND x_e_l)) (MAP SND x_e_l)` >- (
   metis_tac [MEM_EL]
  ) >>
  IMP_RES_TAC l_sound_MEM >>
  ‘EL x (MAP SND x_e_l) = x_e’ by gs[listTheory.oEL_EQ_EL] >>
  fs [e_exec_sound, get_e_ctx_def]
 )
]
QED

Theorem e_exec_sound_red:
!type e. e_exec_sound type e
Proof
strip_tac >>
`(!e. e_exec_sound type e) /\ (!l. x_e_l_exec_sound type l) /\ (!p. x_e_exec_sound type p) /\ (!l. l_sound type l)` suffices_by (
 fs []
) >>
irule e_induction >>
rpt strip_tac >| [
 (* x_e list: base case *)
 fs [x_e_l_exec_sound, l_sound],

 (* e list: base case *)
 fs [l_sound],

 (* Bitvector slice *)
 fs [e_slice_exec_sound_red],

 (* Bitvector concatenation *)
 fs [e_concat_exec_sound_red],

 (* Binary operation *)
 fs [e_binop_exec_sound_red],

 (* e list: inductive step *)
 fs [l_sound_equiv, l_sound_exec],

 (* Cast *)
 fs [e_cast_exec_sound_red],

 (* Field access *)
 fs [e_acc_exec_sound_red],

 (* x_e *)
 fs [x_e_exec_sound],

 (* Select expression *)
 fs [e_select_exec_sound_red],

 (* Unary operation *)
 fs [e_unop_exec_sound_red],

 (* TODO: List expression - not in exec sem yet *)
 fs [e_exec_sound, e_exec_def],

 (* Function/extern call *)
 fs [e_call_exec_sound_red],

 (* Struct *)
 fs [e_struct_exec_sound_red],

 (* TODO: Header expression - not in exec sem yet *)
 fs [e_exec_sound, e_exec_def],

 (* x_e list: inductive case *)
 Cases_on `p` >>
 fs [x_e_l_exec_sound, l_sound, x_e_exec_sound] >>
 rpt strip_tac >>
 Cases_on `x` >> (
  fs [oEL_def]
 ) >>
 subgoal `MEM e (MAP SND l)` >- (
  fs [oEL_EQ_EL, EL_MEM]
 ) >>
 metis_tac [l_sound_MEM],

 (* Constant value: Irreducible *)
 fs [e_exec_sound, e_exec_def],

 (* Variable lookup *)
 fs [e_exec_sound, e_exec_def] >>
 rpt strip_tac >>
 Cases_on `lookup_vexp2 scopes_stack g_scope_list v` >> (
  fs []
 ) >>
 rw [] >>
 METIS_TAC [(valOf o find_clause_e_red) "e_lookup", clause_name_def]
]
QED

val _ = export_theory ();
