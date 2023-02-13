open HolKernel boolLib Parse bossLib;

val _ = new_theory "p4_exec_sem_e_soundness";

open p4Lib;
open ottTheory listTheory rich_listTheory arithmeticTheory p4_auxTheory p4Theory p4_exec_semTheory;

Definition e_exec_sound:
 (e_exec_sound (type:('a itself)) e =
  !(ctx:'a ctx) g_scope_list scopes_stack e' frame_list.
  e_exec ctx g_scope_list scopes_stack e = SOME (e', frame_list) ==>
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

(* TODO: Move *)
Theorem oEL_cons_PRE:
!e x h l.
(x > 0) /\ (SOME e = oEL x (h::l)) ==>
(SOME e = oEL (PRE x) l)
Proof
rpt strip_tac >>
fs [oEL_def, PRE_SUB1]
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
  PAT_X_ASSUM ``!x. _`` (fn thm => ASSUME_TAC (SPEC ``(0:num)`` thm)) >>
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

Theorem e_acc_exec_sound_red:
!type e x.
e_exec_sound type e ==>
e_exec_sound type (e_acc e x)
Proof
fs [e_exec_sound] >>
rpt strip_tac >>
fs [e_exec] >>
Cases_on `is_v e` >> (
 fs []
) >| [
 Cases_on `e_exec_acc (e_acc e x)` >> (
  fs []
 ) >>
 Cases_on `e` >> (
  fs [is_v]
 ) >>
 Cases_on `v` >> (
  fs [e_exec_acc]
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

 Cases_on `e_exec ctx g_scope_list scopes_stack e` >- (
  fs []
 ) >>
 Cases_on `x'` >>
 fs [] >>
 rw [] >>
 irule ((valOf o find_clause_e_red) "e_acc_arg1") >>
 fs [clause_name_def]
]
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
  fs [is_v]
 ) >>
 Cases_on `is_short_circuitable b` >- (
  (* Short-circuit *)
  Cases_on `b` >> Cases_on `v` >> (
   fs [is_short_circuitable_def, e_exec, is_v, e_exec_short_circuit]
  ) >> (
   Cases_on `b` >> (
    fs [is_short_circuitable_def, e_exec, is_v, e_exec_short_circuit]
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
  fs [e_exec] >>
  rw []
 ) >>
 (* Different concrete cases *)
 Cases_on `b` >> (
  Cases_on `e2` >> (
   fs [is_v]
  ) >>
  Cases_on `v` >> Cases_on `v'` >> (
   fs [e_exec_binop, binop_exec]
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

   Cases_on `bitv_binop binop_sub p p'` >> (
    fs []
   ) >>
   Cases_on `x` >> (
    fs []
   ) >>
   irule ((valOf o find_clause_e_red) "e_sub"),

   irule ((valOf o find_clause_e_red) "e_shl"),

   irule ((valOf o find_clause_e_red) "e_shr"),

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

   irule ((valOf o find_clause_e_red) "e_neq_error"),

   irule ((valOf o find_clause_e_red) "e_eq_bool"),

   irule ((valOf o find_clause_e_red) "e_eq"),

   irule ((valOf o find_clause_e_red) "e_eq_error"),

   irule ((valOf o find_clause_e_red) "e_and"),

   irule ((valOf o find_clause_e_red) "e_xor"),

   irule ((valOf o find_clause_e_red) "e_or")
 ] >> (
  fs [clause_name_def]
 ),

 (* Second operand is not fully reduced *)
 Cases_on `e1` >> (
  fs [is_v]
 ) >>
 Cases_on `is_short_circuitable b` >- (
  (* Short-circuit *)
  fs [] >>
  rw [] >>
  Cases_on `v` >> (
   fs [is_short_circuitable_def, e_exec, is_v, e_exec_short_circuit]
  ) >>
  Cases_on `b'` >> Cases_on `b` >> (
   fs [is_short_circuitable_def, e_exec, is_v, e_exec_short_circuit]
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
 Cases_on `e_exec ctx g_scope_list scopes_stack e2` >> (
  fs [e_exec]
 ) >>
 Cases_on `x` >> (
  fs [is_v]
 ) >>
 METIS_TAC [((valOf o find_clause_e_red) "e_binop_arg2"), clause_name_def],

 (* First operand is not fully reduced *)
 Cases_on `e_exec ctx g_scope_list scopes_stack e1` >> (
  fs [e_exec]
 ) >> (
  Cases_on `e1` >> (
   fs [is_v]
  ) >> (
   Cases_on `x` >>
   fs [] >>
   METIS_TAC [((valOf o find_clause_e_red) "e_binop_arg1"), clause_name_def]
  )
 ),

 (* No operand is fully reduced *)
 Cases_on `e_exec ctx g_scope_list scopes_stack e1` >> (
  fs [e_exec]
 ) >> (
  Cases_on `e1` >> (
   fs [is_v]
  ) >> (
   Cases_on `x` >>
   fs [] >>
   METIS_TAC [((valOf o find_clause_e_red) "e_binop_arg1"), clause_name_def]
  )
 )
]
QED

Theorem e_select_exec_sound_red:
!type e l s.
e_exec_sound type e ==>
e_exec_sound type (e_select e l s)
Proof
fs [e_exec_sound] >>
rpt strip_tac >>
Cases_on `is_v e` >| [
 Cases_on `e` >> (
  fs [is_v]
 ) >>
 fs [e_exec, e_exec_select] >>
 Cases_on `FIND (\(v',x'). v' = v) l` >> (
  fs [is_v]
 ) >- (
  rw [] >>
  irule ((valOf o find_clause_e_red) "e_sel_acc") >>
  fs [sel_def, clause_name_def]
 ) >>
 Cases_on `x` >>
 fs [] >>
 rw [] >>
 irule ((valOf o find_clause_e_red) "e_sel_acc") >>
 fs [sel_def, clause_name_def],

 fs [e_exec, e_exec_select] >>
 Cases_on `e_exec ctx g_scope_list scopes_stack e` >- (
  fs []
 ) >>
 Cases_on `x` >>
 fs [] >>
 rw [] >>
 irule ((valOf o find_clause_e_red) "e_sel_arg") >>
 fs [clause_name_def]
]
QED

Theorem e_unop_exec_sound_red:
!type e u.
e_exec_sound type e ==>
e_exec_sound type (e_unop u e)
Proof
fs [e_exec_sound] >>
rpt strip_tac >>
Cases_on `is_v e` >| [
 Cases_on `e_exec_unop u e` >> (
  fs [e_exec] >>
  rw []
 ) >>
 Cases_on `e` >> (
  fs [is_v]
 ) >>
 (* Different concrete cases *)
 Cases_on `u` >> (
  Cases_on `v` >> (
   fs [e_exec_unop, unop_exec]
  ) >>
  rw []
 ) >| [
  irule ((valOf o find_clause_e_red) "e_neg_bool"),

  irule ((valOf o find_clause_e_red) "e_compl"),

  irule ((valOf o find_clause_e_red) "e_neg_signed"),

  irule ((valOf o find_clause_e_red) "e_un_plus")
 ] >>
 fs [clause_name_def],

 Cases_on `e_exec ctx g_scope_list scopes_stack e` >> (
  fs [e_exec]
 ) >>
 Cases_on `x` >>
 fs [] >>
 METIS_TAC [(valOf o find_clause_e_red) "e_unop_arg", clause_name_def]
]
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
fs [e_exec] >>
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
 Cases_on `copyin (MAP FST r) (MAP SND r) l g_scope_list scopes_stack` >> (
  fs []
 ) >>
 IMP_RES_TAC map_tri_zip12 >>
 METIS_TAC [ISPEC ``ZIP (l,r):(e # string # d) list`` ((valOf o find_clause_e_red) "e_call_newframe"), unred_arg_index_NONE,
            clause_name_def],

 (* e_call_args *)
 Cases_on `e_exec (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map) g_scope_list scopes_stack (EL x l)` >> (
  fs []
 ) >>
 Cases_on `x'` >>
 fs [] >>
 rw [] >>
 Q.SUBGOAL_THEN `((MAP (\(a_,b_,c_,d_). a_) (ZIP (l,ZIP (LUPDATE q' x l,r))) = l) /\
                 (MAP (\(a_,b_,c_,d_). b_) (ZIP (l,ZIP (LUPDATE q' x l,r))) = LUPDATE q' x l) /\
                 (MAP (\(a_,b_,c_,d_). c_) (ZIP (l,ZIP (LUPDATE q' x l,r))) = MAP FST r) /\
                 (MAP (\(a_,b_,c_,d_). d_) (ZIP (l,ZIP (LUPDATE q' x l,r))) = MAP SND r) /\
                 (MAP (\(a_,b_,c_,d_). (c_,d_)) (ZIP (l,ZIP (LUPDATE q' x l,r))) = r))` (
  fn thm => (irule (SIMP_RULE std_ss [thm] (ISPEC ``ZIP (l:e list, ZIP ((LUPDATE q' x l), r:(string # d) list))``
                                                  ((valOf o find_clause_e_red) "e_call_args"))))
 ) >- (
  subgoal `LENGTH l = LENGTH (ZIP (LUPDATE q' x l,r))` >- (
   fs [LENGTH_ZIP]
  ) >>
  subgoal `LENGTH (LUPDATE q' x l) = LENGTH r` >- (
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
  fs [oEL_EQ_EL]
 ]
]
QED

Theorem e_struct_exec_sound_red:
!type x_e_l.
x_e_l_exec_sound type x_e_l ==>
e_exec_sound type (e_struct x_e_l)
Proof
fs [e_exec_sound] >>
rpt strip_tac >>
fs [e_exec] >>
Cases_on `unred_mem_index (MAP SND x_e_l)` >> (
 fs []
) >| [
 rw [] >>
 subgoal `?x_l. x_l = MAP FST x_e_l` >- (
  fs []
 ) >>
 subgoal `?e_l. e_l = MAP SND x_e_l` >- (
  fs []
 ) >>
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

 Cases_on `e_exec ctx g_scope_list scopes_stack (EL x (MAP SND x_e_l))` >> (
  fs []
 ) >>
 PairCases_on `x'` >>
 fs [] >>
 rw [] >>
 Q.SUBGOAL_THEN `((MAP ( \ (f_,e_,e'_). (f_,e_)) (ZIP (MAP FST x_e_l, ZIP (MAP SND x_e_l, LUPDATE x'0 x (MAP SND x_e_l))))) = x_e_l) /\
                 ((MAP ( \ (f_,e_,e'_). (f_,e'_)) (ZIP (MAP FST x_e_l,ZIP (MAP SND x_e_l, LUPDATE x'0 x (MAP SND x_e_l))))) = ZIP (MAP FST x_e_l, LUPDATE x'0 x (MAP SND x_e_l)))`
  (fn thm => (irule (SIMP_RULE std_ss [thm] (ISPEC ``ZIP (MAP FST (x_e_l:(string # e) list), ZIP (MAP SND x_e_l, LUPDATE x'0 x (MAP SND x_e_l)))``
                                                  ((valOf o find_clause_e_red) "e_eStruct"))))) >- (
  subgoal `LENGTH (MAP FST x_e_l) = LENGTH (ZIP (MAP SND x_e_l, LUPDATE x'0 x (MAP SND x_e_l)))` >- (
   fs []
  ) >>
  fs [map_tri_zip12] >>
  subgoal `LENGTH (MAP SND x_e_l) = LENGTH (LUPDATE x'0 x (MAP SND x_e_l))` >- (
   fs [vl_of_el_LENGTH]
  ) >>
  fs [map_tri_zip12, listTheory.MAP_ZIP, GSYM UNZIP_MAP]
 ) >>
 fs [clause_name_def] >>
 qexistsl_tac [`x'0`, `x`] >>
 rpt strip_tac >> (
  fs [lambda_unzip_tri]
 ) >>
 fs [x_e_l_exec_sound] >>
 IMP_RES_TAC unred_mem_index_in_range >>
 subgoal `MEM (EL x (MAP SND x_e_l)) (MAP SND x_e_l)` >- (
  metis_tac [MEM_EL]
 ) >>
 IMP_RES_TAC l_sound_MEM >>
 fs [e_exec_sound]
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

 (* TODO: bitvector slice - not in exec sem yet *)
 fs [e_exec_sound, e_exec],

 (* TODO: bitvector concatenation - not in exec sem yet *)
 fs [e_exec_sound, e_exec],

 (* Binary operation *)
 fs [e_binop_exec_sound_red],

 (* e list: inductive step *)
 fs [l_sound_equiv, l_sound_exec],

 (* Field access *)
 fs [e_acc_exec_sound_red],

 (* x_e *)
 fs [x_e_exec_sound],

 (* Select expression *)
 fs [e_select_exec_sound_red],

 (* Unary operation *)
 fs [e_unop_exec_sound_red],

 (* TODO: List expression - not in exec sem yet *)
 fs [e_exec_sound, e_exec],

 (* Function/extern call *)
 fs [e_call_exec_sound_red],

 (* Struct *)
 fs [e_struct_exec_sound_red],

 (* TODO: Header expression - not in exec sem yet *)
 fs [e_exec_sound, e_exec],

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
 fs [e_exec_sound, e_exec],

 (* Variable lookup *)
 fs [e_exec_sound, e_exec] >>
 rpt strip_tac >>
 Cases_on `lookup_vexp2 scopes_stack g_scope_list v` >> (
  fs []
 ) >>
 rw [] >>
 METIS_TAC [(valOf o find_clause_e_red) "e_lookup", clause_name_def]
]
QED

val _ = export_theory ();
