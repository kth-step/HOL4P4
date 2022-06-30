open HolKernel boolLib Parse bossLib;

val _ = new_theory "p4_exec_sem_e_soundness";

open p4Lib;
open ottTheory listTheory p4_auxTheory p4Theory p4_exec_semTheory;

Definition e_exec_sound:
 (e_exec_sound e =
  !ctx g_scope_list scopes_stack e' frame_list.
  e_exec ctx g_scope_list scopes_stack e = SOME (e', frame_list) ==>
  e_red ctx g_scope_list scopes_stack e e' frame_list)
End

Definition l_sound_exec:
 (l_sound_exec [] = T) /\
 (l_sound_exec ((h::t):e list) = 
  (e_exec_sound h /\ l_sound_exec t))
End

Definition l_sound:
 (l_sound [] = T) /\
 (l_sound (l:e list) = 
  !x e. (SOME e = oEL x l) ==> e_exec_sound e)
End

Theorem l_sound_cons:
!h l. l_sound (h::l) ==> l_sound l
Proof
REPEAT STRIP_TAC >>
Induct_on `l` >> (
 fs [l_sound]
) >>
REPEAT STRIP_TAC >>
PAT_X_ASSUM ``!x e. _`` (fn thm => ASSUME_TAC (SPECL [``SUC x``, ``e:e``] thm)) >>
rfs [] >>
`oEL x (h'::l) = oEL (SUC x) (h::h'::l)` suffices_by (
 fs []
) >>
Induct_on `x` >> (
 fs [oEL_def]
)
QED

Theorem oEL_cons:
!h l.
(!x e. SOME e = oEL x l ==> e_exec_sound e) ==>
(!x e. SOME e = oEL x (h::l) ==> e_exec_sound e)
Proof
cheat
QED

Theorem oEL_cons_PRE:
!e x h l.
(x > 0) /\ (SOME e = oEL x (h::l)) ==>
(SOME e = oEL (PRE x) l)
Proof
REPEAT STRIP_TAC >>
fs [oEL_def, arithmeticTheory.PRE_SUB1]
QED

Theorem l_sound_equiv:
!l. l_sound l <=> l_sound_exec l
Proof
REPEAT STRIP_TAC >>
EQ_TAC >| [
 Induct_on `l` >> (
  fs [l_sound, l_sound_exec]
 ) >>
 REPEAT STRIP_TAC >| [
  PAT_X_ASSUM ``!x. _`` (fn thm => ASSUME_TAC (SPEC ``0`` thm)) >>
  fs [oEL_def],

  `l_sound (h::l)` suffices_by (
   METIS_TAC [l_sound_cons]
  ) >>
  METIS_TAC [l_sound]
 ],

 Induct_on `l` >> (
  fs [l_sound, l_sound_exec]
 ) >>
 NTAC 2 STRIP_TAC >>
 Induct_on `x` >> (
  fs [oEL_def]
 ) >>
 `!x e. SOME e = oEL x l ==> e_exec_sound e` suffices_by (
  METIS_TAC [oEL_cons_PRE]
 ) >>
 fs [] >>
 Cases_on `l` >- (
  fs [oEL_def]
 ) >>
 METIS_TAC [l_sound]
]
QED

Theorem e_acc_exec_sound_red:
!e1 x.
e_exec_sound e1 ==>
e_exec_sound (e_acc e1 x)
Proof
fs [e_exec_sound] >>
REPEAT STRIP_TAC >>
Cases_on `is_v e1` >| [
 (* 1st case is base case *)
 Cases_on `e1` >> (
  fs [is_v]
 ) >>
 Cases_on `v` >> (
  fs [e_exec, e_exec_acc, is_v]
 ) >> (
  Cases_on `FIND (\(k,v). k = x) l` >>
  fs [] >>
  Cases_on `x'` >>
  fs [] >>
  rw []
 ) >| [
  irule ((valOf o find_clause_e_red) "e_s_acc"),

  irule ((valOf o find_clause_e_red) "e_h_acc")
 ] >> (
  fs [clause_name_def, listTheory.FIND_def] >>
  subgoal `(\(k,v). k = x) (q,r)` >- (
   Cases_on `z` >>
   fs [] >>
   rw [] >>
   IMP_RES_TAC (ISPECL [``(l':((string # v) list))``, ``(\(k,v). k = x):(string # v -> bool)``, ``(q,r):string # v``, ``0``] index_find_first) >>
   fs []
  ) >>
  fs []
 ),
(*
 (* Second case is reduction of 2nd argument (field name) *)
 Cases_on `e_exec ctx g_scope_list scopes_stack e2` >> (
  fs [e_exec]
 ) >>
 Cases_on `x` >>
 fs [] >>
 subgoal `~fully_reduced e2` >- (
  Cases_on `e2` >> (
   fs [fully_reduced_def, is_v]
  )
 ) >>
 METIS_TAC [((valOf o find_clause_e_red) "e_acc_arg2"), clause_name_def],
*)
 (* Third case is reduction of 1st argument (struct value) *)
 Cases_on `e_exec ctx g_scope_list scopes_stack e1` >> (
  fs [e_exec]
 ) >>
 Cases_on `x'` >> (
  fs [is_v]
 ) >>
(*
 Cases_on `v` >> (
  fs [is_v_str]
 ) >>
*)
 METIS_TAC [((valOf o find_clause_e_red) "e_acc_arg1"), clause_name_def]

(*
,

 (* Fourth case determines case when both arguments are unreduced *)
 Cases_on `e_exec ctx g_scope_list scopes_stack e2` >> (
  fs [e_exec]
 ) >>
 Cases_on `x` >>
 fs [] >>
 subgoal `~fully_reduced e2` >- (
  Cases_on `e2` >> (
   fs [fully_reduced_def, is_v]
  )
 ) >>
 METIS_TAC [(valOf o find_clause_e_red) "e_acc_arg2", clause_name_def]
*)
]
QED

Theorem e_binop_exec_sound_red:
!e1 e2 b.
e_exec_sound e1 ==>
e_exec_sound e2 ==>
e_exec_sound (e_binop e1 b e2)
Proof
fs [e_exec_sound] >>
REPEAT STRIP_TAC >>
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
!e l s.
e_exec_sound e ==>
e_exec_sound (e_select e l s)
Proof
fs [e_exec_sound] >>
REPEAT STRIP_TAC >>
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
!e u.
e_exec_sound e ==>
e_exec_sound (e_unop u e)
Proof
fs [e_exec_sound] >>
REPEAT STRIP_TAC >>
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
!f l.
l_sound l ==>
e_exec_sound (e_call f l)
Proof
fs [e_exec_sound] >>
REPEAT STRIP_TAC >>
PairCases_on `ctx` >>
rename1 `(ext_map,func_map,tbl_map)` >>
fs [e_exec] >>
Cases_on `lookup_funn_sig_body f func_map ext_map` >> (
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
 Cases_on `e_exec (ext_map,func_map,tbl_map) g_scope_list scopes_stack (EL x l)` >> (
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
 REPEAT STRIP_TAC >| [
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

Theorem e_exec_sound_red:
!e. e_exec_sound e
Proof
`(!e. e_exec_sound e) /\ (!l. l_sound l)` suffices_by (
 fs []
) >>
irule e_induction >>
REPEAT STRIP_TAC >| [
 (* e list: base case *)
 fs [l_sound],

 (* bitvector slice - not in exec sem yet *)
 fs [e_exec_sound, e_exec],

 (* bitvector concatenation - not in exec sem yet *)
 fs [e_exec_sound, e_exec],

 (* Binary operation *)
 fs [e_binop_exec_sound_red],

 (* e list: inductive step *)
 fs [l_sound_equiv, l_sound_exec],

 (* Field access *)
 fs [e_acc_exec_sound_red],

 (* Select expression *)
 fs [e_select_exec_sound_red],

 (* Unary operation *)
 fs [e_unop_exec_sound_red],

 (* List expression - not in exec sem yet *)
 fs [e_exec_sound, e_exec],

 (* Function/extern call *)
 fs [e_call_exec_sound_red],

 (* Constant value: Irreducible *)
 fs [e_exec_sound, e_exec],

 (* Variable lookup *)
 fs [e_exec_sound, e_exec] >>
 REPEAT STRIP_TAC >>
 Cases_on `lookup_vexp2 scopes_stack g_scope_list v` >> (
  fs []
 ) >>
 rw [] >>
 METIS_TAC [(valOf o find_clause_e_red) "e_lookup", clause_name_def]
]
QED

val _ = export_theory ();
