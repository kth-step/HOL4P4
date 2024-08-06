open HolKernel boolLib liteLib simpLib Parse bossLib;
open p4Theory p4_auxTheory p4_exec_semTheory;

val _ = new_theory "p4_bigstep";

open listTheory;

(* This file contains a big-step semantics for a fragment of P4 that
 * contains mostly local instructions *)

(* The symbolic execution should attempt to use this when
 * then next statement to be reduced is stmt_empty, (stmt_seq stmt_ass _)
 * or (stmt_seq stmt_empty _) *)

Theorem is_v_is_const:
!e. is_v e = is_const e
Proof
strip_tac >>
Cases_on ‘e’ >> (
 gs[is_v_def, is_const_def]
)
QED

(* TODO: Merge with the above? *)
Theorem EVERY_is_v_unred_mem_index:
!e_l.
EVERY is_v e_l ==>
unred_mem_index e_l = NONE
Proof
rpt strip_tac >>
CCONTR_TAC >>
gs[GSYM quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE, optionTheory.IS_SOME_EXISTS] >>
imp_res_tac unred_mem_not_const >>
gs[is_consts_def] >>
FULL_SIMP_TAC pure_ss [EVERY_NOT_EXISTS] >>
gs[is_v_is_const] >>
metis_tac[EVERY_NOT_EXISTS]
QED

Theorem not_EVERY_is_v_unred_mem_index:
!e_l.
~EVERY is_v e_l ==>
?i. unred_mem_index e_l = SOME i
Proof
rpt strip_tac >>
gs [unred_mem_index_def, unred_mem_def, is_consts_def, ZIP_def, INDEX_FIND_def, AllCaseEqs()] >>
Cases_on ‘INDEX_FIND 0 (\e. ~is_const e) e_l’ >> (
 gs[]
) >- (
 imp_res_tac INDEX_FIND_NONE_EVERY >>
 gs[GSYM is_v_is_const] >>
 metis_tac[EVERY_NOT_EXISTS]
) >>
PairCases_on ‘x’ >>
gs[]
QED

(***********************)
(*   Main semantics    *)

Definition lookup_vexp_def:
 lookup_vexp scope_list x =
  case lookup_map scope_list x of
  | SOME (v,str_opt) => SOME v
  | NONE => NONE
End

(* Uses INL/INR directly for easier proofs *)
Definition bigstep_e_exec_def:
 (********************)
 (* Variable look-up *)
 (bigstep_e_exec (scope_lists:scope_list) (INL (e_var x)) n =
  case lookup_vexp scope_lists x of
  | SOME v => SOME (INL $ e_v v, n + 1)
  | NONE => NONE)
  /\
 (******************************)
 (* Struct/header field access *)
 (bigstep_e_exec scope_lists (INL (e_acc e_v_struct x)) n =
  (case bigstep_e_exec scope_lists (INL e_v_struct) n of
   | SOME (INL $ e_v_struct', n') =>
    if is_v e_v_struct'
    then
     (case e_exec_acc (e_acc e_v_struct' x) of
      | SOME v => SOME (INL $ v, n'+1)
      | NONE => NONE)
    else SOME (INL $ e_acc e_v_struct' x, n')
   | _ => NONE))
  /\
 (*********************************)
 (* Struct/header field reduction *)
 (bigstep_e_exec scope_lists (INL (e_struct x_e_l)) n =
  case bigstep_e_exec scope_lists (INR (MAP SND x_e_l)) n of
  | SOME (INR $ e_l', n') =>
   if (EVERY is_v e_l')
   then
    SOME (INL $ e_v $ v_struct (ZIP (MAP FST x_e_l, vl_of_el e_l')) , n'+1)
   else
    SOME (INL $ e_struct (ZIP (MAP FST x_e_l, e_l')) , n')
  | _ => NONE)
  /\
 (********)
 (* Cast *)
 (bigstep_e_exec scope_lists (INL (e_cast cast e)) n =
  (case bigstep_e_exec scope_lists (INL e) n of
   | SOME (INL $ e', n') =>
    if is_v e'
    then
     (case e_exec_cast cast e' of
      | SOME v => SOME (INL $ e_v v, n'+1)
      | NONE => NONE)
    else
     SOME (INL $ e_cast cast e', n')
   | _ => NONE))
  /\
 (********************)
 (* Unary arithmetic *)
 (bigstep_e_exec scope_lists (INL (e_unop unop e)) n =
  (case bigstep_e_exec scope_lists (INL e) n of
   | SOME (INL $ e', n') =>
    if is_v e'
    then 
     (case e_exec_unop unop e' of
      | SOME v => SOME (INL $ e_v v, n'+1)
      | NONE => NONE)
    else
     SOME (INL $ e_unop unop e', n')
   | _ => NONE))
  /\
 (*********************)
 (* Binary arithmetic *)
 (bigstep_e_exec scope_lists (INL (e_binop e1 binop e2)) n =
  (case bigstep_e_exec scope_lists (INL e1) n of
   | SOME (INL $ e1', n') =>
    (case e1' of
     | (e_v v) =>
      if is_short_circuitable binop
      then
       (case e_exec_short_circuit v binop e2 of
        | SOME e' => SOME (INL $ e', n'+1)
        | NONE => NONE)
      else
       (case bigstep_e_exec scope_lists (INL e2) n' of
        | SOME (INL $ e2', n'') =>
         if is_v e2'
         then
          (case e_exec_binop e1' binop e2' of
           | SOME v' => SOME (INL $ e_v v', n''+1)
           | NONE => NONE)
         else
          SOME (INL $ e_binop e1' binop e2', n'')
        | _ => NONE)
     | _ =>
      SOME (INL $ e_binop e1' binop e2, n'))
   | _ => NONE))
  /\
 (*****************)
 (* Concatenation *)
 (bigstep_e_exec scope_lists (INL (e_concat e1 e2)) n =
  case bigstep_e_exec scope_lists (INL e1) n of
  | SOME (INL $ e1', n') =>
   if is_v_bit e1'
   then
    (case bigstep_e_exec scope_lists (INL e2) n' of
     | SOME (INL $ e2', n'') =>
      (if is_v_bit e2'
       then 
        (case e_exec_concat e1' e2' of
         | SOME v => SOME (INL $ e_v v, n''+1)
         | NONE => NONE)
       else
        SOME (INL $ e_concat e1' e2', n''))
     | _ => NONE)
   else
    SOME (INL $ e_concat e1' e2, n')
  | _ => NONE)
  /\
 (***********)
 (* Slicing *)
 (bigstep_e_exec scope_lists (INL (e_slice e1 e2 e3)) n =
  if (is_v_bit e2 /\ is_v_bit e3)
  then
   (case bigstep_e_exec scope_lists (INL e1) n of
    | SOME (INL $ e1', n') =>
     if is_v_bit e1'
     then 
      (case e_exec_slice e1' e2 e3 of
       | SOME v => SOME (INL $ e_v v, n'+1)
       | NONE => NONE)
     else
      SOME (INL $ e_slice e1' e2 e3, n')
    | _ => NONE)
   else NONE)
  /\
 (**********************)
 (* NESTED EXPRESSIONS *)
 (**********************)
(*
 (************************)
 (* Function/extern call *)
 (* TODO: Needs directions... *)
 (bigstep_e_exec scope_lists (INL (e_call funn e_l)) n =
  case bigstep_e_exec scope_lists (INR e_l) n of
  | SOME (INR $ e_l', n') =>
   SOME (INL $ e_call funn e_l', n')
  | _ => NONE)
 /\
*)
 (**********)
 (* Select *)
 (bigstep_e_exec scope_lists (INL (e_select e s_l_x_l x)) n =
  case bigstep_e_exec scope_lists (INL e) n of
  | SOME (INL $ e', n') =>
   SOME (INL $ e_select e' s_l_x_l x, n')
  | _ => NONE)
 /\
 (bigstep_e_exec scope_lists (INL e) n = SOME (INL $ e,n))
 /\
 (bigstep_e_exec scope_lists (INR []) n = SOME (INR $ [],n))
 /\
 (bigstep_e_exec scope_lists (INR (h::t)) n =
  case bigstep_e_exec scope_lists (INL h) n of
  | SOME (INL h', n') =>
   if is_v h'
   then
    (case bigstep_e_exec scope_lists (INR t) n' of
     | SOME (INR t', n'') => SOME (INR $ h'::t', n'')
     | _ => NONE)
   else SOME (INR $ h'::t, n')
  | _ => NONE)
Termination
WF_REL_TAC `measure ( \ (scope_lists, t, n). case t of
                           | (INL e) => e_size e
                           | (INR e_l) => e3_size e_l)` >>
gs[e_size_def] >>
Induct_on ‘x_e_l’ >> (
 gs[e_size_def]
) >>
rpt strip_tac >>
PairCases_on ‘h’ >>
gs[e_size_def]
End

(* TODO: No reduction to L-values, for now *)
Definition bigstep_f_arg_exec'_def:
 (bigstep_f_arg_exec' scope_lists (d,e) n =
  if ~((d = d_out) \/ (d = d_inout))
  then bigstep_e_exec scope_lists (INL e) n
  else if is_e_lval e
  then SOME (INL e, n)
  else NONE
 )
End

Definition bigstep_f_arg_exec_l_def:
 (bigstep_f_arg_exec_l scope_lists [] n = SOME ([],n))
 /\
 (bigstep_f_arg_exec_l scope_lists (h::t) n =
  case bigstep_f_arg_exec' scope_lists h n of
  | SOME (INL h', n') =>
   (case bigstep_f_arg_exec_l scope_lists t n' of
    | SOME (t', n'') => SOME (h'::t', n'')
    | NONE => NONE)
  | _ => NONE)
End

Definition oZIP_def:
 (oZIP ([], []) = SOME []) /\
 (oZIP (h1::t1, h2::t2) =
  case oZIP (t1, t2) of
  | SOME t' =>
   SOME ((h1, h2)::t')
  | NONE => NONE) /\
 (oZIP _ = NONE)
End

(* NOTE: This can return no reductions in case the next item to be reduced in
 * e_l is a function call *)
Definition bigstep_f_arg_exec_def:
 (bigstep_f_arg_exec func_maps_opt scope_lists (funn, e_l) n =
  (case func_maps_opt of
   | SOME (func_map, b_func_map, ext_fun_map) =>
    (case lookup_funn_sig funn func_map b_func_map ext_fun_map of
     | SOME x_d_l =>
      (case oZIP (MAP SND x_d_l, e_l) of
       | SOME d_e_l =>
        bigstep_f_arg_exec_l scope_lists d_e_l n
       | NONE => NONE)
     | NONE => NONE)
   | NONE => SOME (e_l, n))
 )
End

Definition bigstep_stmt_exec_def:
 (bigstep_stmt_exec (func_maps_opt:(func_map # b_func_map # 'a ext_map) option) scope_lists (stmt_ass lval e) n =
 (* Note that reduction of e_call arguments on top level only is allowed *)
  (case e of
   | e_call funn e_l =>
    (case bigstep_f_arg_exec func_maps_opt scope_lists (funn, e_l) n of
     | SOME (e_l', n') => SOME (stmt_ass lval (e_call funn e_l'), scope_lists, n')
     | NONE => NONE)
   | _ =>
    (case bigstep_e_exec scope_lists (INL e) n of
     | SOME (INL e', n') =>
      if is_v e'
      then
       (case stmt_exec_ass lval e' scope_lists of
        | SOME scope_lists' =>
         SOME (stmt_empty, scope_lists', n'+1)
        | NONE => NONE)
      else SOME (stmt_ass lval e', scope_lists, n')
     | _ => NONE))
      )
  /\
 (bigstep_stmt_exec func_maps_opt scope_lists (stmt_seq stmt1 stmt2) n =
  if is_empty stmt1
  then bigstep_stmt_exec func_maps_opt scope_lists stmt2 (n+1)
  else
   (case bigstep_stmt_exec func_maps_opt scope_lists stmt1 n of
    | SOME (stmt1', scope_lists', n') =>
     if is_empty stmt1'
     then bigstep_stmt_exec func_maps_opt scope_lists' stmt2 (n'+1)
     else SOME (stmt_seq stmt1' stmt2, scope_lists', n')
    | _ => NONE)) /\
 (**********************)
 (* NESTED EXPRESSIONS *)
 (**********************)
 (bigstep_stmt_exec func_maps_opt scope_lists (stmt_ret e) n =
  (case bigstep_e_exec scope_lists (INL e) n of
   | SOME (INL e', n') =>
    SOME (stmt_ret e', scope_lists, n')
   | _ => NONE))
  /\
 (bigstep_stmt_exec func_maps_opt scope_lists (stmt_trans e) n =
  (case bigstep_e_exec scope_lists (INL e) n of
   | SOME (INL e', n') =>
    SOME (stmt_trans e', scope_lists, n')
   | _ => NONE))
  /\
 (bigstep_stmt_exec func_maps_opt scope_lists (stmt_cond e stmt1 stmt2) n =
  (case e of
   | e_call funn e_l =>
    (case bigstep_f_arg_exec func_maps_opt scope_lists (funn, e_l) n of
     | SOME (e_l', n') => SOME (stmt_cond (e_call funn e_l') stmt1 stmt2, scope_lists, n')
     | NONE => NONE)
   | _ =>
    (case bigstep_e_exec scope_lists (INL e) n of
     | SOME (INL e', n') =>
      SOME (stmt_cond e' stmt1 stmt2, scope_lists, n')
     | _ => NONE)) )
  /\
 (bigstep_stmt_exec func_maps_opt scope_lists (stmt_app t_name e_l) n =
  (case bigstep_e_exec scope_lists (INR e_l) n of
   | SOME (INR e_l', n') =>
    SOME (stmt_app t_name e_l', scope_lists, n')
   | _ => NONE))
  /\
 (bigstep_stmt_exec func_maps_opt scope_lists stmt n =
  SOME (stmt, scope_lists, n))
End

(* The result of this should be sound with respect to n steps of
 * the executable semantics running inside a programmable block *)
Definition bigstep_exec_def:
 bigstep_exec func_maps_opt (g_scope_list, scope_list) stmt =
  case bigstep_stmt_exec func_maps_opt (scope_list++g_scope_list) stmt 0 of
  | SOME (stmt', scope_lists, n) =>
   (case separate scope_lists of
    | (SOME g_scope_list', SOME scope_list') =>
     SOME (stmt', g_scope_list', scope_list', n)
    | _ => NONE)
  | NONE => NONE
End

(* This uses top-level constructs and might be more convenient to use *)
(* TODO: Take whole ctx or just function maps? Whole ctx might lead to faster composition,
 * just function maps to faster evaluation *)
Definition bigstep_arch_exec_def:
 (bigstep_arch_exec ctx_b_func_map_opt ([g_scope1; g_scope2]:g_scope_list) (arch_frame_list_regular frame_list) =
  case frame_list of
  | ((funn, stmt_stack, scope_list)::t) =>
   (case stmt_stack of
    | (stmt::t') =>
     let func_maps_opt = (case ctx_b_func_map_opt of
                          | NONE => NONE
                          | SOME (((ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map):'a actx), b_func_map) => SOME (func_map, b_func_map, ext_map)) in
       (case bigstep_exec func_maps_opt ([g_scope1; g_scope2], scope_list) stmt of
        | SOME (stmt', g_scope_list', scope_list', n) =>
         SOME (g_scope_list', arch_frame_list_regular ((funn, (stmt'::t'), scope_list')::t), n)
        | _ => NONE)
    | _ => NONE)
  | _ => NONE
 ) /\
 (bigstep_arch_exec _ _ _ = NONE)
End

(* Used for reduction of function arguments *)
(* Takes entire ctx, but no b_func_map. Hands over to bigstep_arch_exec when this has
 * been sorted *)
Definition bigstep_arch_exec'_def:
 (bigstep_arch_exec' (aenv_ctx_opt:('a aenv # 'a actx) option) ([g_scope1; g_scope2]:g_scope_list) (arch_frame_list_regular frame_list) =
  case aenv_ctx_opt of
  | NONE => bigstep_arch_exec (NONE:('a actx # b_func_map) option) ([g_scope1; g_scope2]:g_scope_list) (arch_frame_list_regular frame_list)
  | SOME ((i, _, _, _), (ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map)) =>
   (case EL i ab_list of
    | (arch_block_pbl x el) =>
     (case ALOOKUP pblock_map x of
      | SOME (_, _, b_func_map, _, _, _) =>
       bigstep_arch_exec (SOME ((ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map), b_func_map)) ([g_scope1; g_scope2]:g_scope_list) (arch_frame_list_regular frame_list)
      | NONE => NONE)
    | _ => NONE)
 ) /\
 (bigstep_arch_exec' _ _ _ = NONE)
End

Triviality e3_e1_size:
 !l. e3_size (MAP SND l) < e1_size l + 1
Proof
Induct_on ‘l’ >> (
 gs[e_size_def]
) >>
Induct_on ‘h’ >>
gen_tac >>
Cases_on ‘p_2’ >> (
 gs[e_size_def]
)
QED

Theorem bigstep_e_exec_var_REWR:
!scope_lists var n t' m v.
bigstep_e_exec scope_lists (INL (e_var var)) n = SOME (t',m) <=>
(m = n + 1 /\ ?v. lookup_vexp scope_lists var = SOME v /\ t' = (INL $ e_v v))
Proof
rpt strip_tac >>
eq_tac >> (
 rpt strip_tac >>
 gs[bigstep_e_exec_def, AllCaseEqs()]
)
QED

Theorem bigstep_e_exec_acc_REWR:
!scope_lists x s n t' m.
bigstep_e_exec scope_lists (INL (e_acc x s)) n = SOME (t',m) <=>
 ?n' e_v_struct.
 bigstep_e_exec scope_lists (INL x) n = SOME (INL e_v_struct, n') /\
 ((is_v e_v_struct /\ ?e'. e_exec_acc (e_acc e_v_struct s) = SOME e' /\ m = n' + 1 /\
  t' = (INL e')) \/
 (~is_v e_v_struct /\ t' = (INL (e_acc e_v_struct s)) /\ m = n'))
Proof
rpt strip_tac >>
eq_tac >> (
 rpt strip_tac >>
 gs[bigstep_e_exec_def, AllCaseEqs()]
)
QED

Theorem bigstep_e_exec_unop_REWR:
!scope_lists unop e n t' m.
bigstep_e_exec scope_lists (INL (e_unop unop e)) n = SOME (t',m) <=>
 ?e' n'.
 bigstep_e_exec scope_lists (INL e) n = SOME (INL e', n') /\
 ((is_v e' /\ ?v. e_exec_unop unop e' = SOME v /\ m = n' + 1 /\
  t' = (INL $ e_v v)) \/
 (~is_v e' /\ t' = (INL (e_unop unop e')) /\ m = n'))
Proof
rpt strip_tac >>
eq_tac >> (
 rpt strip_tac >>
 gs[bigstep_e_exec_def, AllCaseEqs()]
)
QED

Theorem bigstep_e_exec_cast_REWR:
!scope_lists cast x n t' m.
bigstep_e_exec scope_lists (INL (e_cast cast x)) n = SOME (t',m) <=>
 ?n' e'.
 bigstep_e_exec scope_lists (INL x) n = SOME (INL e', n') /\
 ((is_v e' /\ ?v. e_exec_cast cast e' = SOME v /\ m = n' + 1 /\
  t' = (INL $ e_v v)) \/
 (~is_v e' /\ t' = (INL (e_cast cast e')) /\ m = n'))
Proof
rpt strip_tac >>
eq_tac >> (
 rpt strip_tac >>
 gs[bigstep_e_exec_def, AllCaseEqs()]
)
QED

Theorem bigstep_e_exec_binop_REWR:
!scope_lists binop e1 e2 n t' m.
bigstep_e_exec scope_lists (INL (e_binop e1 binop e2)) n = SOME (t',m) <=>
 ?e1' n'.
 bigstep_e_exec scope_lists (INL e1) n = SOME (INL e1', n') /\
 ((is_v e1' /\
  ((is_short_circuitable binop /\
    ?v e'.
     (e1' = e_v v /\
      e_exec_short_circuit v binop e2 = SOME e' /\
      t' = INL e' /\ m = n' + 1)) \/
   (~is_short_circuitable binop /\
    ?e2' n''.
     bigstep_e_exec scope_lists (INL e2) n' = SOME (INL e2', n'') /\
     ((is_v e2' /\
       ?v'. e_exec_binop e1' binop e2' = SOME v' /\
        t' = (INL $ e_v v') /\ m = n'' + 1) \/
      (~is_v e2' /\
        t' = (INL $ e_binop e1' binop e2') /\ m = n''))))
  ) \/
  (~is_v e1' /\ t' = (INL (e_binop e1' binop e2)) /\ m = n'))
Proof
rpt strip_tac >>
eq_tac >> (
 rpt strip_tac >>
 gs[bigstep_e_exec_def]
) >- (
 Cases_on ‘bigstep_e_exec scope_lists (INL e1) n’ >> (
  gs[]
 ) >>
 PairCases_on ‘x’ >>
 gs[] >>
 Cases_on ‘x0’ >>
 gs[] >>
 Cases_on ‘is_v x’ >> (
  gs[]
 ) >> (
  Cases_on ‘x’ >> (
   gs[is_v_def]
  )
 ) >>
 gs[AllCaseEqs()]
) >> (
 Cases_on ‘e1'’ >> (
  gs[is_v_def]
 )
)
QED

Theorem bigstep_e_exec_concat_REWR:
!scope_lists e1 e2 n t' m.
bigstep_e_exec scope_lists (INL (e_concat e1 e2)) n = SOME (t',m) <=>
 ?e1' n'.
 bigstep_e_exec scope_lists (INL e1) n = SOME (INL e1', n') /\
 ((is_v_bit e1' /\
  (?e2' n''.
    bigstep_e_exec scope_lists (INL e2) n' = SOME (INL e2', n'') /\
    ((is_v_bit e2' /\
      ?v. e_exec_concat e1' e2' = SOME v /\
       t' = (INL $ e_v v) /\ m = n'' + 1) \/
     (~is_v_bit e2' /\
       t' = (INL $ e_concat e1' e2') /\ m = n'')))) \/
  (~is_v_bit e1' /\ t' = (INL (e_concat e1' e2)) /\ m = n'))
Proof
rpt strip_tac >>
eq_tac >> (
 rpt strip_tac >>
 gs[bigstep_e_exec_def, AllCaseEqs()]
)
QED

Theorem bigstep_e_exec_slice_REWR:
!scope_lists e1 e2 e3 n t' m.
bigstep_e_exec scope_lists (INL (e_slice e1 e2 e3)) n = SOME (t',m) <=>
 is_v_bit e2 /\ is_v_bit e3 /\
 ?e1' n'.
 bigstep_e_exec scope_lists (INL e1) n = SOME (INL e1', n') /\
 ((is_v_bit e1' /\
  (?v. e_exec_slice e1' e2 e3 = SOME v /\
   t' = (INL $ e_v v) /\ m = n' + 1)) \/
  (~is_v_bit e1' /\ t' = (INL (e_slice e1' e2 e3)) /\ m = n'))
Proof
rpt strip_tac >>
eq_tac >> (
 rpt strip_tac >>
 gs[bigstep_e_exec_def, AllCaseEqs()]
)
QED

Theorem bigstep_e_exec_select_REWR:
!scope_lists e s_l_x_l x n t' m.
bigstep_e_exec scope_lists (INL (e_select e s_l_x_l x)) n = SOME (t',m) <=>
 ?e' n'.
 bigstep_e_exec scope_lists (INL e) n = SOME (INL e', n') /\
 t' = (INL (e_select e' s_l_x_l x)) /\ m = n'
Proof
rpt strip_tac >>
eq_tac >> (
 rpt strip_tac >>
 gs[bigstep_e_exec_def, AllCaseEqs()]
)
QED

Theorem bigstep_e_exec_struct_REWR:
!scope_lists x_e_l n t' m.
bigstep_e_exec scope_lists (INL (e_struct x_e_l)) n = SOME (t',m) <=>
 ?e_l' n'.
 bigstep_e_exec scope_lists (INR (MAP SND x_e_l)) n = SOME (INR e_l', n') /\
 ((EVERY is_v e_l' /\ t' = (INL (e_v (v_struct (ZIP (MAP FST x_e_l,vl_of_el e_l'))))) /\ m = n' + 1) \/
  (~(EVERY is_v e_l') /\ t' = (INL (e_struct (ZIP (MAP FST x_e_l,e_l')))) /\ m = n')
 )
Proof
rpt strip_tac >>
eq_tac >> (
 rpt strip_tac >>
 gs [bigstep_e_exec_def, AllCaseEqs()]
)
QED

val bigstep_e_exec_ind_hyp_tac =
 qpat_x_assum ‘!y. _’ (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
 gs[e_size_def] >>
 res_tac >>
 decide_tac
;

val bigstep_e_exec_2_ind_hyp_tac =
 qpat_assum ‘!y. _’ (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
 qpat_x_assum ‘!y. _’ (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x')’] thm)) >>
 gs[e_size_def] >>
 res_tac >>
 decide_tac
;

Theorem bigstep_e_exec_incr:
!t n scope_lists t' m.
bigstep_e_exec scope_lists t n = SOME (t', m) ==>
n <= m
Proof
measureInduct_on ‘( \ t. case t of
                           | (INL e) => e_size e
                           | (INR e_l) => e3_size e_l) t’ >>
Induct_on ‘t’ >- (
 (* INL case *)
 Induct_on ‘x’ >> (
  rpt strip_tac
 ) >| [
  (* v *)
  gs[bigstep_e_exec_def],

  (* var *)
  gs[bigstep_e_exec_var_REWR],

  (* list *)
  gs[bigstep_e_exec_def],

  (* acc *)
  gs[bigstep_e_exec_acc_REWR] >>
  rpt strip_tac >> (
   bigstep_e_exec_ind_hyp_tac
  ),

  (* unop *)
  gs[bigstep_e_exec_unop_REWR] >>
  rpt strip_tac >> (
   bigstep_e_exec_ind_hyp_tac
  ),

  (* cast *)
  gs[bigstep_e_exec_cast_REWR] >>
  rpt strip_tac >> (
   bigstep_e_exec_ind_hyp_tac
  ),

  (* binop *)
  gs[bigstep_e_exec_binop_REWR] >>
  rpt strip_tac >- (
   bigstep_e_exec_ind_hyp_tac
  ) >- (
   bigstep_e_exec_2_ind_hyp_tac
  ) >- (
   bigstep_e_exec_2_ind_hyp_tac
  ) >>
  bigstep_e_exec_ind_hyp_tac,

  (* concat *)
  gs[bigstep_e_exec_concat_REWR] >>
  rpt strip_tac >- (
   bigstep_e_exec_2_ind_hyp_tac
  ) >- (
   bigstep_e_exec_2_ind_hyp_tac
  ) >>
  bigstep_e_exec_ind_hyp_tac,

  (* slice *)
  gs[bigstep_e_exec_slice_REWR] >>
  rpt strip_tac >> (
   bigstep_e_exec_ind_hyp_tac
  ),

  (* call *)
  gs[bigstep_e_exec_def],

  (* select *)
  gs[bigstep_e_exec_select_REWR] >>
  rpt strip_tac >>
  bigstep_e_exec_ind_hyp_tac,

  (* struct *)
  gs[bigstep_e_exec_struct_REWR] >>
  rpt strip_tac >> (
   PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INR (MAP SND (l:(string # e) list)))’] thm)) >>
   gs[e_size_def, e3_e1_size] >>
   res_tac >>
   decide_tac
  ),

  (* header *)
  gs[bigstep_e_exec_def]
 ]
(* INR *)
) >>
Induct_on ‘y’ >> (
 rpt strip_tac >>
 gs[bigstep_e_exec_def]
) >>
Cases_on ‘bigstep_e_exec scope_lists (INL h) n’ >> (
 gs[]
) >>
PairCases_on ‘x’ >>
gs[] >>
Cases_on ‘x0’ >>
gs[] >>
Cases_on ‘bigstep_e_exec scope_lists (INR y) x1’ >> (
 gs[]
) >- (
 PAT_ASSUM “!y'. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL h)’] thm)) >>
 gs[e_size_def] >>
 res_tac >>
 decide_tac
) >>
PairCases_on ‘x'’ >>
gs[] >>
Cases_on ‘x'0’ >>
gs[] >- (
 PAT_ASSUM “!y'. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL h)’] thm)) >>
 gs[e_size_def] >>
 res_tac >>
 decide_tac
) >>
PAT_ASSUM “!y'. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL h)’] thm)) >>
gs[e_size_def] >>
PAT_ASSUM “!y'. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INR y)’] thm)) >>
gs[e_size_def] >>
res_tac >>
Cases_on ‘is_v x’ >> (
 gs[]
)
QED

val bigstep_e_exec_unchanged_ind_hyp_tac =
 imp_res_tac bigstep_e_exec_incr >>
 PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
 gs[e_size_def] >>
 res_tac >>
 gs[]
;

val bigstep_e_exec_unchanged_2_ind_hyp_tac =
 imp_res_tac bigstep_e_exec_incr >>
 PAT_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
 PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x')’] thm)) >>
 gs[e_size_def] >>
 res_tac >>
 gs[]
;

Theorem bigstep_e_exec_unchanged:
!t t' scope_lists n.
bigstep_e_exec scope_lists t n = SOME (t', n) ==>
t = t'
Proof
measureInduct_on ‘( \ t. case t of
                           | (INL e) => e_size e
                           | (INR e_l) => e3_size e_l) t’ >>
Induct_on ‘t’ >- (
 (* INL case *)
 Induct_on ‘x’ >> (
  rpt strip_tac
 ) >| [
  (* v *)
  gs[bigstep_e_exec_def],

  (* var *)
  gs[bigstep_e_exec_var_REWR],

  (* list *)
  gs[bigstep_e_exec_def],

  (* acc *)
  gs[bigstep_e_exec_acc_REWR] >> (
   bigstep_e_exec_unchanged_ind_hyp_tac
  ),

  (* unop *)
  gs[bigstep_e_exec_unop_REWR] >> (
   bigstep_e_exec_unchanged_ind_hyp_tac
  ),

  (* cast *)
  gs[bigstep_e_exec_cast_REWR] >> (
   bigstep_e_exec_unchanged_ind_hyp_tac
  ),

  (* binop *)
  fs[bigstep_e_exec_binop_REWR] >- (
   bigstep_e_exec_unchanged_ind_hyp_tac
  ) >- (
   bigstep_e_exec_unchanged_2_ind_hyp_tac
  ) >- (
   imp_res_tac bigstep_e_exec_incr >>
   PAT_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
   PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x')’] thm)) >>
   fs[e_size_def] >>
   subgoal ‘n = n'’ >- (
    decide_tac
   ) >>
   fs[] >>
   res_tac >>
   gs[]
  ) >>
  bigstep_e_exec_unchanged_ind_hyp_tac,

  (* concat *)
  fs[bigstep_e_exec_concat_REWR] >- (
   bigstep_e_exec_unchanged_2_ind_hyp_tac
  ) >- (
   imp_res_tac bigstep_e_exec_incr >>
   PAT_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
   PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x')’] thm)) >>
   fs[e_size_def] >>
   subgoal ‘n = n'’ >- (
    decide_tac
   ) >>
   fs[] >>
   res_tac >>
   gs[]
  ) >>
  bigstep_e_exec_unchanged_ind_hyp_tac,

  (* slice *)
  gs[bigstep_e_exec_slice_REWR] >> (
   bigstep_e_exec_unchanged_ind_hyp_tac
  ),

  (* call *)
  gs[bigstep_e_exec_def],

  (* select *)
  gs[bigstep_e_exec_select_REWR] >>
  rpt strip_tac >>
  bigstep_e_exec_unchanged_ind_hyp_tac,

  (* struct *)
  gs[bigstep_e_exec_struct_REWR] >> (
   imp_res_tac bigstep_e_exec_incr >>
   PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INR (MAP SND (l:(string # e) list)))’] thm)) >>
   gs[e_size_def, e3_e1_size] >>
   res_tac >>
   gvs[GSYM ZIP_MAP_FST_SND]
  ),

  (* header *)
  gs[bigstep_e_exec_def]
 ]
(* INR *)
) >>
Induct_on ‘y’ >> (
 rpt strip_tac >>
 gs[bigstep_e_exec_def]
) >>
Cases_on ‘bigstep_e_exec scope_lists (INL h) n’ >> (
 gs[]
) >>
PairCases_on ‘x’ >>
gs[] >>
Cases_on ‘x0’ >>
gs[] >>
Cases_on ‘bigstep_e_exec scope_lists (INR y) x1’ >> (
 gs[]
) >- (
 PAT_ASSUM “!y'. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL h)’] thm)) >>
 gs[e_size_def] >>
 res_tac >>
 gs[]
) >>
PairCases_on ‘x'’ >>
gs[] >>
Cases_on ‘x'0’ >>
gs[] >- (
 PAT_ASSUM “!y'. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL h)’] thm)) >>
 gs[e_size_def] >>
 res_tac >>
 gs[]
) >>
imp_res_tac bigstep_e_exec_incr >>
PAT_ASSUM “!y'. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL h)’] thm)) >>
gs[e_size_def] >>
PAT_ASSUM “!y'.
          (case y' of INL e => e_size e | INR e_l => e3_size e_l) <
          e3_size y + (e_size h + 1) ==>
          !t' scope_lists n.
            bigstep_e_exec scope_lists y' n = SOME (t',n) ==> y' = t'” (fn thm => ASSUME_TAC (Q.SPECL [‘(INR y)’] thm)) >>
fs[e_size_def] >>
Cases_on ‘is_v x’ >> (
 gs[]
) >- (
 gvs[] >>
 subgoal ‘x1 = n’ >- (
  decide_tac
 ) >>
 fs[] >>
 res_tac >>
 gs[]
) >>
gvs[] >>
res_tac >>
gs[]
QED

(* TODO: Revisit this *)
fun bigstep_e_exec_not_eq_ind_hyp_tac tmq =
 PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
 fs[e_size_def] >>
 subgoal tmq >- (
  gs[]
 ) >>
 res_tac
;

Theorem bigstep_e_exec_not_eq:
!t t' scope_lists n.
t <> t' ==>
bigstep_e_exec scope_lists t 0 = SOME (t',n) ==>
n <> 0
Proof
measureInduct_on ‘( \ t. case t of
                           | (INL e) => e_size e
                           | (INR e_l) => e3_size e_l) t’ >>
Induct_on ‘t’ >- (
 (* INL case *)
 Induct_on ‘x’ >> (
  rpt strip_tac
 ) >| [
  (* v *)
  gs[bigstep_e_exec_def],

  (* var *)
  gs[bigstep_e_exec_var_REWR],

  (* list *)
  gs[bigstep_e_exec_def],

  (* acc *)
  gs[bigstep_e_exec_acc_REWR] >>
  bigstep_e_exec_not_eq_ind_hyp_tac ‘INL x <> ((INL e_v_struct):(e + e list))’,

  (* unop *)
  gs[bigstep_e_exec_unop_REWR] >>
  bigstep_e_exec_not_eq_ind_hyp_tac ‘INL x <> ((INL e'):(e + e list))’,

  (* cast *)
  gs[bigstep_e_exec_cast_REWR] >>
  bigstep_e_exec_not_eq_ind_hyp_tac ‘INL x <> ((INL e'):(e + e list))’,

  (* binop *)
  gs[bigstep_e_exec_binop_REWR] >- (
   imp_res_tac bigstep_e_exec_incr >>
   subgoal ‘n' = 0’ >- (
    gs[]
   ) >>
   gs[] >>
   imp_res_tac bigstep_e_exec_unchanged >>
   gs[]
  ) >>
  bigstep_e_exec_not_eq_ind_hyp_tac ‘INL x <> ((INL e1'):(e + e list))’,

  (* concat *)
  gs[bigstep_e_exec_concat_REWR] >- (
   imp_res_tac bigstep_e_exec_incr >>
   subgoal ‘n' = 0’ >- (
    gs[]
   ) >>
   gs[] >>
   imp_res_tac bigstep_e_exec_unchanged >>
   gs[]
  ) >>
  bigstep_e_exec_not_eq_ind_hyp_tac ‘INL x <> ((INL e1'):(e + e list))’,

  (* slice *)
  gs[bigstep_e_exec_slice_REWR] >>
  bigstep_e_exec_not_eq_ind_hyp_tac ‘INL x <> ((INL e1'):(e + e list))’,

  (* call *)
  gs[bigstep_e_exec_def],

  (* select *)
  gs[bigstep_e_exec_select_REWR] >>
  bigstep_e_exec_not_eq_ind_hyp_tac ‘INL x <> ((INL e'):(e + e list))’,

  (* struct *)
  gs[bigstep_e_exec_struct_REWR] >>
  PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INR (MAP SND (l:(string # e) list)))’] thm)) >>
  gs[e_size_def, e3_e1_size] >>
  imp_res_tac bigstep_e_exec_unchanged >>
  gvs[ZIP_MAP_FST_SND],

  (* header *)
  gs[bigstep_e_exec_def]
 ]
) >>
(* INR *)
Induct_on ‘y’ >> (
 rpt strip_tac >>
 gs[bigstep_e_exec_def]
) >>
Cases_on ‘bigstep_e_exec scope_lists (INL h) 0’ >> (
 gs[]
) >>
PairCases_on ‘x’ >>
gs[] >>
Cases_on ‘x0’ >>
gs[] >>
Cases_on ‘bigstep_e_exec scope_lists (INR y) x1’ >> (
 gs[]
) >- (
 gvs[] >>
 PAT_ASSUM “!y'. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL h)’] thm)) >>
 gs[e_size_def] >>
 res_tac
) >>
PairCases_on ‘x'’ >>
gs[] >>
Cases_on ‘x'0’ >>
gs[] >- (
 gvs[] >>
 PAT_ASSUM “!y'. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL h)’] thm)) >>
 gs[e_size_def] >>
 res_tac
) >>
imp_res_tac bigstep_e_exec_incr >>
PAT_ASSUM “!y'. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL h)’] thm)) >>
gs[e_size_def] >>
PAT_ASSUM “!y'.
          (case y' of INL e => e_size e | INR e_l => e3_size e_l) <
          e3_size y + (e_size h + 1) ==>
          !t'' scope_lists'.
            y' <> t'' ==> bigstep_e_exec scope_lists' y' 0 <> SOME (t'',0)” (fn thm => ASSUME_TAC (Q.SPECL [‘(INR y)’] thm)) >>
gs[e_size_def] >>
Cases_on ‘is_v x’ >> (
 gs[]
) >- (
 gvs[] >>
 imp_res_tac bigstep_e_exec_unchanged >>
 gs[]
) >>
gs[] >>
imp_res_tac bigstep_e_exec_unchanged >>
gs[]
QED

Theorem bigstep_e_exec_not_v_bit:
!e e' scope_lists n.
~is_v_bit e ==>
is_v_bit e' ==>
bigstep_e_exec scope_lists (INL e) 0 = SOME (INL e',n) ==>
n <> 0
Proof
rpt strip_tac >>
rw[] >>
imp_res_tac bigstep_e_exec_unchanged >>
gs[is_v_bit_def, AllCaseEqs()]
QED

Theorem bigstep_e_exec_not_v:
!e e' scope_lists n.
~is_v e ==>
is_v e' ==>
bigstep_e_exec scope_lists (INL e) 0 = SOME (INL e',n) ==>
n <> 0
Proof
rpt strip_tac >>
rw[] >>
imp_res_tac bigstep_e_exec_unchanged >>
gs[is_v_def, AllCaseEqs()]
QED

Theorem bigstep_e_exec_v:
!v scope_list g_scope_list' n.
bigstep_e_exec (scope_list ++ g_scope_list') (INL (e_v v)) n = SOME (INL $ e_v v, n)
Proof
gs[bigstep_e_exec_def]
QED

Triviality unred_mem_index_NONE:
!e_l.
EVERY is_v e_l ==>
unred_mem_index e_l = NONE
Proof
Induct >- (
 gs[unred_mem_index_def, unred_mem_def, INDEX_FIND_def]
) >>
rpt strip_tac >>
gs[unred_mem_index_def, unred_mem_def, INDEX_FIND_def] >>
subgoal ‘is_const h’ >- (
 Cases_on ‘h’ >> (
  gs[is_v_def, is_const_def]
 )
) >>
gs[] >>
 Cases_on ‘INDEX_FIND 1 (\e. ~is_const e) e_l’ >> (
  gs[]
 ) >>
PairCases_on ‘x’ >>
gs[] >>
imp_res_tac index_find_first >>
Cases_on ‘INDEX_FIND 0 (\e. ~is_const e) e_l’ >- (
 gs[] >>
 gs[Q.SPECL [‘e_l’, ‘1:num’] (INDEX_FIND_add)]
) >>
PairCases_on ‘x’ >>
gs[]
QED

Theorem bigstep_e_exec_sound:
!t scope_list g_scope_list' t' e e_l apply_table_f (ext_map:'a ext_map) func_map b_func_map pars_map tbl_map.
bigstep_e_exec (scope_list ++ g_scope_list') t 0 = SOME (t', 1) ==>
(t = (INL e) ==>
(?e'. (t' = (INL e')) /\
 e_exec (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)
        g_scope_list' scope_list e = SOME (e', []))) /\
(t = INR e_l ==>
((e_l = []) \/
 ?i. unred_mem_index e_l = SOME i /\
 (?e'.
 e_exec (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)
        g_scope_list' scope_list (EL i e_l) = SOME (e', []) /\
 t' = INR (LUPDATE e' i e_l))))
Proof
measureInduct_on ‘( \ t. case t of
                           | (INL e) => e_size e
                           | (INR e_l) => e3_size e_l) t’ >>
Induct_on ‘t’ >- (
 (* INL case *)
 Induct_on ‘x’ >> (
  rpt strip_tac >>
  fs[]
 ) >| [
  (* v *)
  gvs[bigstep_e_exec_def],

  (* var *)
  rw[] >>
  gs[bigstep_e_exec_var_REWR] >>
  gs[e_exec_def, lookup_vexp_def, lookup_vexp2_def] >>
  Cases_on ‘lookup_map (scope_list ++ g_scope_list') v’ >> (
   gs[]
  ) >>
  PairCases_on ‘x’ >>
  gs[],

  (* list *)
  gvs[bigstep_e_exec_def],

  (* acc *)
  rw[] >>
  gs[bigstep_e_exec_acc_REWR] >> (
   rw[] >>
   gs[e_exec_def]
  ) >- (
   Cases_on ‘is_v x’ >> (
    gs[]
   ) >- (
    Cases_on ‘x’ >> (
     gs[is_v_def, bigstep_e_exec_def]
    )
   ) >>
   imp_res_tac bigstep_e_exec_unchanged >>
   gs[]
  ) >>
  PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
  gs[e_size_def] >>
  res_tac >>
  fs[] >>
  Cases_on ‘is_v x’ >> (
   fs[]
  ) >>
  Cases_on ‘x’ >> (
   gs[is_v_def, bigstep_e_exec_def, AllCaseEqs()]
  ),

  (* unop *)
  rw[] >>
  gs[bigstep_e_exec_unop_REWR] >> (
   rw[] >>
   gs[e_exec_def]
  ) >- (
   Cases_on ‘is_v x’ >> (
    gs[]
   ) >- (
    Cases_on ‘x’ >> (
     fs[is_v_def, bigstep_e_exec_def, AllCaseEqs()]
    )
   ) >>
   imp_res_tac bigstep_e_exec_unchanged >>
   gs[]
  ) >>
  gs[] >>
  PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
  gs[e_size_def] >>
  res_tac >>
  fs[] >>
  Cases_on ‘is_v x’ >> (
   gs[]
  ) >>
  Cases_on ‘x’ >> (
   gs[is_v_def, bigstep_e_exec_def]
  ),

  (* cast *)
  rw[] >>
  gs[bigstep_e_exec_cast_REWR] >> (
   rw[] >>
   gs[e_exec_def]
  ) >- (
   Cases_on ‘is_v x’ >> (
    gs[]
   ) >- (
    Cases_on ‘x’ >> (
     gs[is_v_def, bigstep_e_exec_def]
    )
   ) >>
   imp_res_tac bigstep_e_exec_unchanged >>
   gs[]
  ) >>
  gs[] >>
  PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
  gs[e_size_def] >>
  res_tac >>
  fs[] >>
  Cases_on ‘is_v x’ >> (
   gs[]
  ) >>
  Cases_on ‘x’ >> (
   gs[is_v_def, bigstep_e_exec_def]
  ),

  (* binop *)
  rw[] >>
  gs[bigstep_e_exec_binop_REWR] >> (
   rw[] >>
   gs[e_exec_def]
  ) >- (
   gs[] >>
   imp_res_tac bigstep_e_exec_unchanged >>
   gs[]
  ) >- (
   gs[] >>
   imp_res_tac bigstep_e_exec_incr >>
   gs[] >>
   imp_res_tac bigstep_e_exec_unchanged >>
   gs[] >>
   Cases_on ‘x’ >> (
    gvs[is_v_def]
   )
  ) >- (
   Cases_on ‘is_v x’ >> (
    gs[]
   ) >- (
    Cases_on ‘x’ >> (
     gvs[is_v_def]
    ) >- (
     Cases_on ‘is_v x'’ >> (
      gs[]
     ) >- (
      Cases_on ‘x'’ >> (
       gvs[is_v_def]
      ) >>
      gs[bigstep_e_exec_def]
     ) >>
     gs[bigstep_e_exec_def] >>
     gvs[] >>
     PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x')’] thm)) >>
     gs[e_size_def] >>
     res_tac >>
     fs[]
    )
   ) >>
   imp_res_tac bigstep_e_exec_incr >>
   subgoal ‘n' = 1’ >- (
    CCONTR_TAC >>
    subgoal ‘n' = 0’ >- (
     decide_tac
    ) >>
    fs[] >>
    imp_res_tac bigstep_e_exec_unchanged >>
    gs[]
   ) >>
   gs[] >>
   PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
   Cases_on ‘x’ >> (
    gvs[is_v_def]
   ) >> (
    gs[e_size_def] >>
    res_tac >>
    fs[] >>
    imp_res_tac bigstep_e_exec_unchanged >>
    gs[]
   )
  ) >- (
   gs[] >>
   PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
   gs[e_size_def] >>
   res_tac >>
   fs[] >>
   Cases_on ‘x’ >> (
    gs[bigstep_e_exec_def]
   )
  ),

  (* concat *)
  rw[] >>
  gs[bigstep_e_exec_concat_REWR] >> (
   rw[] >>
   gs[e_exec_def]
  ) >- (
   gs[] >>
   imp_res_tac bigstep_e_exec_incr >>
   gs[] >>
   imp_res_tac bigstep_e_exec_unchanged >>
   gs[]
  ) >- (
   Cases_on ‘is_v_bit x’ >> (
    gs[]
   ) >- (
    Cases_on ‘x’ >> (
     gvs[is_v_bit_def]
    ) >>
    Cases_on ‘v’ >> (
     gvs[is_v_bit_def]
    ) >>
    Cases_on ‘is_v_bit x'’ >> (
     gs[]
    ) >- (
     Cases_on ‘x'’ >> (
      gvs[is_v_bit_def]
     ) >>
     gs[bigstep_e_exec_def]
    ) >>
    subgoal ‘n' = 0’ >- (
     gs[bigstep_e_exec_def]
    ) >>
    gs[] >>
    PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x')’] thm)) >>
    gs[e_size_def] >>
    res_tac >>
    fs[] >>
    imp_res_tac bigstep_e_exec_unchanged >>
    gs[]
   ) >>
   imp_res_tac bigstep_e_exec_incr >>
   subgoal ‘n' = 1’ >- (
    CCONTR_TAC >>
    subgoal ‘n' = 0’ >- (
     decide_tac
    ) >>
    fs[] >>
    imp_res_tac bigstep_e_exec_unchanged >>
    gs[]
   ) >>
   gs[] >>
   PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
   gs[e_size_def] >>
   res_tac >>
   fs[] >>
   imp_res_tac bigstep_e_exec_unchanged >>
   gs[]
  ) >- (
   gs[] >>
   PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
   gs[e_size_def] >>
   res_tac >>
   fs[] >>
   Cases_on ‘is_v_bit x’ >> (
    gs[]
   ) >>
   Cases_on ‘x’ >> (
    gvs[is_v_bit_def]
   ) >>
   gs[bigstep_e_exec_def]
  ),

  (* slice *)
  rw[] >>
  gs[bigstep_e_exec_slice_REWR] >> (
   rw[] >>
   gs[e_exec_def]
  ) >- (
   Cases_on ‘is_v_bit x’ >> (
    gs[]
   ) >- (
    Cases_on ‘x’ >> (
     gs[is_v_bit_def, bigstep_e_exec_def]
    )
   ) >>
   imp_res_tac bigstep_e_exec_unchanged >>
   gs[]
  ) >>
  gs[] >>
  PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
  gs[e_size_def] >>
  res_tac >>
  fs[] >>
  Cases_on ‘is_v_bit x’ >> (
   gs[]
  ) >>
  Cases_on ‘x’ >> (
   gs[is_v_bit_def, bigstep_e_exec_def]
  ),

  (* call *) 
  gvs[bigstep_e_exec_def],

  (* select *)
  rw[] >>
  gs[bigstep_e_exec_select_REWR] >> (
   rw[] >>
   gs[e_exec_def]
  ) >>
  Cases_on ‘is_v x’ >> (
   gs[]
  ) >- (
   Cases_on ‘x’ >> (
    gs[is_v_def, bigstep_e_exec_def]
   )
  ) >>
  PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
  gs[e_size_def] >>
  res_tac >>
  fs[],

  (* struct *)
  rw[] >>
  gs[bigstep_e_exec_struct_REWR] >> (
   rw[] >>
   gs[e_exec_def]
  ) >- (
   gs[] >>
   imp_res_tac bigstep_e_exec_unchanged >>
   gs[] >>
   Cases_on ‘unred_mem_index e_l'’ >> (
    gs[]
   ) >>
   (* Contradiction on unreduced element in e_l' *)
   imp_res_tac unred_mem_index_NONE >>
   gs[]
  ) >>
  gs[] >>
  PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INR (MAP SND (l:(string # e) list)))’] thm)) >>
  gs[e_size_def, e3_e1_size] >>
  res_tac >>
  PAT_X_ASSUM “!tbl_map pars_map func_map ext_map b_func_map apply_table_f. _” (fn thm => ASSUME_TAC (Q.SPECL [‘tbl_map’, ‘pars_map’, ‘func_map’, ‘ext_map’, ‘b_func_map’, ‘apply_table_f’] thm)) >>
  Cases_on ‘l’ >- (
   gs[bigstep_e_exec_def, e_exec_def]
  ) >>
  fs[e_exec_def],

  (* header *)
  gvs[bigstep_e_exec_def]
 ]
) >>
(* INR *)
Induct_on ‘y’ >> (
 rpt strip_tac >>
 gs[bigstep_e_exec_def, AllCaseEqs()]
) >- (
 subgoal ‘n' = 0 \/ n' = 1’ >- (
  imp_res_tac bigstep_e_exec_incr >>
  decide_tac
 ) >- (
  (* x1 = 0: y reduction contributes the step *)
  gs[] >>
  imp_res_tac bigstep_e_exec_unchanged >>
  gs[] >>
  PAT_ASSUM “!y'. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INR y)’] thm)) >>
  fs[e_size_def] >>
  subgoal ‘e3_size y < e3_size e_l’ >- (
   gvs[e_size_def]
  ) >>
  fs[] >>
  res_tac >>
  PAT_X_ASSUM “!tbl_map pars_map func_map ext_map b_func_map apply_table_f. _” (fn thm => ASSUME_TAC (Q.SPECL [‘tbl_map’, ‘pars_map’, ‘func_map’, ‘ext_map’, ‘b_func_map’, ‘apply_table_f’] thm)) >>
  fs[] >>
  gvs[] >- (
   gs[bigstep_e_exec_def]
  ) >>
  gs[] >>
  qexists_tac ‘i+1’ >>
  gvs[] >>
  rpt strip_tac >- (
   (* Not true? h could be any expression that is not reduced further.. *)
   subgoal ‘is_const h’ >- (
    Cases_on ‘h’ >> (
     gs[is_v_def, is_const_def]
    )
   ) >>
   gs[unred_mem_index_def, unred_mem_def, INDEX_FIND_def] >>
   gs[Q.SPECL [‘y’, ‘1:num’] (INDEX_FIND_add)] >>
   Cases_on ‘INDEX_FIND 0 (\e. ~is_const e) y’ >> (
    gs[]
   ) >>
   PairCases_on ‘x’ >>
   gs[]
  ) >>
  qexists_tac ‘e'’ >>
  subgoal ‘(EL (i + 1) (h::y)) = (EL i y)’ >- (
   gs[GSYM p4_auxTheory.SUC_ADD_ONE, EL_restricted]
  ) >>
  gs[GSYM p4_auxTheory.SUC_ADD_ONE, LUPDATE_def]
 ) >>
 (* x1 = 1: h reduction contributes the step *)
 gvs[] >>
 subgoal ‘~is_const h’ >- (
  CCONTR_TAC >>
  Cases_on ‘h’ >> (
   gs[is_const_def, bigstep_e_exec_def]
  )
 ) >>
 PAT_ASSUM “!y'. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL h)’] thm)) >>
 fs[e_size_def] >>
 res_tac >>
 fs[] >>
 qexists_tac ‘0’ >>
 gs[unred_mem_index_def, unred_mem_def, INDEX_FIND_def, LUPDATE_def] >>
 imp_res_tac bigstep_e_exec_unchanged >>
 gs[]
) >>
(* New case *)
gvs[] >>
qexists_tac ‘0’ >>
subgoal ‘~is_const h’ >- (
 CCONTR_TAC >>
 Cases_on ‘h’ >> (
  gs[is_const_def, bigstep_e_exec_def]
 )
) >>
gs[unred_mem_index_def, unred_mem_def, INDEX_FIND_def, LUPDATE_def] >>
PAT_ASSUM “!y'. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL h)’] thm)) >>
fs[e_size_def] >>
res_tac >>
fs[]
QED

(* TODO: rename "fuel" to "nsteps" or something else, since it has to do with a
 * compelled number of reductions *)

(* This will just yield NONE for new frames *)
Definition e_multi_exec_def:
 (e_multi_exec _ _ _ e 0 = SOME e)
 /\
 (e_multi_exec (ctx:'a ctx) g_scope_list scope_list e (SUC fuel) =
  case e_exec ctx g_scope_list scope_list e of
  | SOME (e', []) => e_multi_exec ctx g_scope_list scope_list e' fuel
  | _ => NONE)
End

Definition e_multi_exec'_def:
 (e_multi_exec' _ _ _ e 0 = SOME e)
 /\
 (e_multi_exec' (ctx:'a ctx) g_scope_list scope_list e (SUC fuel) =
  case e_multi_exec' ctx g_scope_list scope_list e fuel of
  | SOME e' =>
   (case e_exec ctx g_scope_list scope_list e' of
    | SOME (e'', []) => SOME e''
    | _ => NONE)
  | _ => NONE)
End

(* Version for use with e_multi_exec'_list *)
Definition e_multi_exec'_count_def:
 (e_multi_exec'_count _ _ _ e 0 = SOME (e, 0))
 /\
 (e_multi_exec'_count (ctx:'a ctx) g_scope_list scope_list e (SUC fuel) =
  case e_multi_exec'_count ctx g_scope_list scope_list e fuel of
  | SOME (e', n) =>
   (case e_exec ctx g_scope_list scope_list e' of
    | SOME (e'', []) => SOME (e'', n+1)
    | _ => NONE)
  | _ => NONE)
End

Definition e_multi_exec'_list_def:
 (e_multi_exec'_list _ _ _ e_l 0 = SOME e_l)
 /\
 (e_multi_exec'_list _ _ _ [] _ = SOME [])
 /\
 (e_multi_exec'_list (ctx:'a ctx) g_scope_list scope_list (h::t) (SUC fuel) =
  if is_v h
  then
   (case e_multi_exec'_list (ctx:'a ctx) g_scope_list scope_list t (SUC fuel) of
    | SOME t' => SOME (h::t')
    | NONE => NONE)
  else
   (case e_multi_exec'_count ctx g_scope_list scope_list h (SUC fuel) of
    | SOME (h', fuel_spent) =>
     (case e_multi_exec'_list (ctx:'a ctx) g_scope_list scope_list t ((SUC fuel)-fuel_spent) of
      | SOME t' => SOME (h'::t')
      | NONE => NONE)
    | _ => NONE))
End
(* For the purposes of bigstep_stmt_app_exec_sound_n, it would be useful if
 * e_multi_exec'_list would find the first instance of a non-v expression in the expression
 * list and start reducing it stepwise using e_exec *)
Definition e_multi_exec'_list'_def:
 (e_multi_exec'_list' _ _ _ e_l 0 = SOME e_l)
 /\
 (e_multi_exec'_list' (ctx:'a ctx) g_scope_list scope_list e_l (SUC fuel) =
  case e_multi_exec'_list' (ctx:'a ctx) g_scope_list scope_list e_l fuel of
  | SOME e_l' =>
   (case unred_mem_index e_l' of
    | SOME i =>
     (case e_exec ctx g_scope_list scope_list (EL i e_l') of
      | SOME (e', []) =>
       SOME (LUPDATE e' i e_l')
      | _ => NONE)
    | NONE => NONE)
  | NONE => NONE)
End

(* TODO: Move *)
Theorem e_exec_not_v:
!ctx g_scope_list scope_list e e'.
e_exec ctx g_scope_list scope_list e = SOME (e',[]) ==>
~is_v e
Proof
rpt strip_tac >>
Cases_on ‘e'’ >> (
 gs[is_v_def]
) >> (
 Cases_on ‘e’ >> (
  gs[is_v_def, e_exec_def]
 )
)
QED

Theorem bigstep_e_acc_exec_sound_n_not_v:
!ctx g_scope_list' scope_list e e' n f.
~is_v e' ==>
e_multi_exec' (ctx:'a ctx) g_scope_list' scope_list e n = SOME e' ==>
e_multi_exec' (ctx:'a ctx) g_scope_list' scope_list (e_acc e f) n = SOME (e_acc e' f)
Proof
Induct_on ‘n’ >- (
 gs[e_multi_exec'_def]
) >>
rpt strip_tac >>
gs[e_multi_exec'_def, AllCaseEqs()] >>
subgoal ‘~is_v e''’ >- (
 metis_tac[e_exec_not_v]
) >>
res_tac >>
fs[e_exec_def]
QED

Theorem bigstep_e_acc_exec_sound_n_v:
!ctx g_scope_list' scope_list e e' n f.
is_v e' ==>
e_multi_exec' (ctx:'a ctx) g_scope_list' scope_list e n = SOME e' ==>
e_multi_exec' (ctx:'a ctx) g_scope_list' scope_list (e_acc e f) (SUC n) = e_exec_acc (e_acc e' f)
Proof
Induct_on ‘n’ >- (
 rpt strip_tac >>
 gs[e_multi_exec'_def] >>
 Cases_on ‘e_exec ctx g_scope_list' scope_list (e_acc e' f)’ >> (
  gs[]
 ) >>
 gs[AllCaseEqs(), e_exec_def]
) >>
rpt strip_tac >>
gs[e_multi_exec'_def] >>
Cases_on ‘e_multi_exec' ctx g_scope_list' scope_list e n’ >> (
 gs[]
) >>
subgoal ‘~is_v x’ >- (
 rpt strip_tac >>
 Cases_on ‘e_exec ctx g_scope_list' scope_list x’ >> (
  gs[]
 ) >>
 PairCases_on ‘x'’ >>
 gs[] >>
 Cases_on ‘x'1’ >> (
  gs[]
 ) >>
 Cases_on ‘x’ >> (
  gs[is_v_def, e_exec_def]
 )
) >>
imp_res_tac bigstep_e_acc_exec_sound_n_not_v >>
gs[] >>
Cases_on ‘e_exec ctx g_scope_list' scope_list x’ >> (
 gs[]
) >>
PairCases_on ‘x'’ >>
gs[] >>
Cases_on ‘x'1’ >> (
 gs[]
) >>
gvs[] >>
Cases_on ‘e_exec ctx g_scope_list' scope_list (e_acc x f)’ >> (
 gs[e_exec_def]
) >>
PairCases_on ‘x'’ >>
gs[] >>
Cases_on ‘x'1’ >> (
 gs[]
) >>
gvs[] >>
Cases_on ‘e_exec ctx g_scope_list' scope_list (e_acc e' f)’ >> (
 gs[e_exec_def, AllCaseEqs()]
)
QED

Theorem bigstep_e_unop_exec_sound_n_not_v:
!ctx g_scope_list scope_list e e' n unop.
~is_v e' ==>
e_multi_exec' (ctx:'a ctx) g_scope_list scope_list e n = SOME e' ==>
e_multi_exec' (ctx:'a ctx) g_scope_list scope_list (e_unop unop e) n = SOME (e_unop unop e')
Proof
Induct_on ‘n’ >> (
 gs[e_multi_exec'_def, e_exec_def, AllCaseEqs()]
) >>
rpt strip_tac >>
imp_res_tac e_exec_not_v >>
res_tac >>
fs[] >>
gs[e_exec_def, AllCaseEqs()]
QED

Theorem bigstep_e_unop_exec_sound_n_v:
!ctx g_scope_list scope_list e e' v n unop.
is_v e' ==>
e_multi_exec' (ctx:'a ctx) g_scope_list scope_list e n = SOME e' ==>
e_exec_unop unop e' = SOME v ==>
e_multi_exec' (ctx:'a ctx) g_scope_list scope_list (e_unop unop e) (SUC n) = SOME (e_v v)
Proof
Induct_on ‘n’ >> (
 gs[e_multi_exec'_def, e_exec_def, AllCaseEqs()]
) >>
rpt strip_tac >>
imp_res_tac e_exec_not_v >>
imp_res_tac bigstep_e_unop_exec_sound_n_not_v >>
gs[e_exec_def]
QED

Theorem bigstep_e_cast_exec_sound_n_not_v:
!ctx g_scope_list scope_list e e' n cast.
~is_v e' ==>
e_multi_exec' (ctx:'a ctx) g_scope_list scope_list e n = SOME e' ==>
e_multi_exec' (ctx:'a ctx) g_scope_list scope_list (e_cast cast e) n = SOME (e_cast cast e')
Proof
Induct_on ‘n’ >> (
 gs[e_multi_exec'_def, e_exec_def, AllCaseEqs()]
) >>
rpt strip_tac >>
imp_res_tac e_exec_not_v >>
res_tac >>
fs[] >>
gs[e_exec_def, AllCaseEqs()]
QED

Theorem bigstep_e_cast_exec_sound_n_v:
!ctx g_scope_list scope_list e e' v n cast.
is_v e' ==>
e_multi_exec' (ctx:'a ctx) g_scope_list scope_list e n = SOME e' ==>
e_exec_cast cast e' = SOME v ==>
e_multi_exec' (ctx:'a ctx) g_scope_list scope_list (e_cast cast e) (SUC n) = SOME (e_v v)
Proof
Induct_on ‘n’ >> (
 gs[e_multi_exec'_def, e_exec_def, AllCaseEqs()]
) >>
rpt strip_tac >>
imp_res_tac e_exec_not_v >>
imp_res_tac bigstep_e_cast_exec_sound_n_not_v >>
gs[e_exec_def]
QED

Theorem bigstep_e_binop_exec_sound_n_first:
!ctx g_scope_list scope_list e1 e1' e2 binop n.
e_multi_exec' (ctx:'a ctx) g_scope_list scope_list e1 n = SOME e1' ==>
e_multi_exec' (ctx:'a ctx) g_scope_list scope_list (e_binop e1 binop e2) n = SOME (e_binop e1' binop e2)
Proof
Induct_on ‘n’ >> (
 gs[e_multi_exec'_def, e_exec_def, AllCaseEqs()]
) >>
rpt strip_tac >>
imp_res_tac e_exec_not_v >>
res_tac >>
fs[e_exec_def] >>
Cases_on ‘e'’ >> (
 gs[is_v_def]
)
QED

Theorem bigstep_e_binop_exec_sound_n_first_shortcircuit:
!ctx g_scope_list scope_list e e' binop v n.
e_multi_exec' (ctx:'a ctx) g_scope_list scope_list e n = SOME (e_v v) ==>
is_short_circuitable binop ==>
e_multi_exec' (ctx:'a ctx) g_scope_list scope_list (e_binop e binop e')
          (SUC n) =
        e_exec_short_circuit v binop e'
Proof
Induct_on ‘n’ >- (
 rpt strip_tac >>
 gs[e_multi_exec'_def] >>
 Cases_on ‘e_exec ctx g_scope_list scope_list (e_binop (e_v v) binop e')’ >> (
  gs[e_exec_def, AllCaseEqs()]
 )
) >>
rpt strip_tac >>
gs[e_multi_exec'_def] >>
Cases_on ‘e_multi_exec' ctx g_scope_list scope_list e n’ >> (
 gs[]
) >>
Cases_on ‘e_exec ctx g_scope_list scope_list x’ >> (
 gs[]
) >>
PairCases_on ‘x'’ >>
gs[] >>
Cases_on ‘x'1’ >> (
 gs[]
) >>
subgoal ‘~is_v x’ >- (
 metis_tac[e_exec_not_v]
) >>
imp_res_tac bigstep_e_binop_exec_sound_n_first >>
gvs[] >>
Cases_on ‘e_exec ctx g_scope_list scope_list (e_binop x binop e')’ >> (
 gs[e_exec_def]
) >- (
 Cases_on ‘x’ >> (
  gs[is_v_def]
 )
) >>
PairCases_on ‘x'’ >>
gs[] >>
Cases_on ‘x'1’ >> (
 gs[]
) >- (
 Cases_on ‘x’ >> (
  gs[is_v_def]
 ) >> (
  gvs[e_exec_def] >>
  Cases_on ‘e_exec_short_circuit v binop e'’ >> (
   gs[]
  )
 )
) >>
gs[AllCaseEqs()]
QED

Theorem bigstep_e_binop_exec_sound_n_second:
!ctx g_scope_list scope_list e1 e1' e2 e2' binop n n'.
e_multi_exec' (ctx:'a ctx) g_scope_list scope_list e1 n = SOME e1' ==>
is_v e1' ==>
e_multi_exec' (ctx:'a ctx) g_scope_list scope_list e2 n' = SOME e2' ==>
~is_short_circuitable binop ==>
e_multi_exec' (ctx:'a ctx) g_scope_list scope_list (e_binop e1 binop e2)
           (n' + n) = SOME (e_binop e1' binop e2')
Proof
Induct_on ‘n'’ >> (
 rpt strip_tac >>
 gs[e_multi_exec'_def] >>
 imp_res_tac bigstep_e_binop_exec_sound_n_first >>
 gs[]
) >>
Cases_on ‘e_multi_exec' ctx g_scope_list scope_list e2 n'’ >> (
 gs[]
) >>
Cases_on ‘e_exec ctx g_scope_list scope_list x’ >> (
 gs[]
) >>
PairCases_on ‘x'’ >>
gs[] >>
Cases_on ‘x'1’ >> (
 gs[]
) >>
gvs[] >>
Q.SUBGOAL_THEN ‘n + SUC n' = SUC (n' + n)’ (fn thm => REWRITE_TAC [thm]) >- (
 decide_tac
) >>
gs[e_multi_exec'_def] >>
subgoal ‘e_multi_exec' ctx g_scope_list scope_list (e_binop e1 binop e2)
             (n' + n) = SOME (e_binop e1' binop x)’ >- (
  qpat_x_assum ‘!ctx. _’ (fn thm => irule thm) >>
  gs[]
) >>
fs[arithmeticTheory.ADD_SYM] >>
gs[e_exec_def] >>
Cases_on ‘e1'’ >> (
 gs[is_v_def]
) >>
subgoal ‘~is_v x’ >- (
 metis_tac[e_exec_not_v]
) >>
gs[]
QED

Theorem bigstep_e_binop_exec_sound_n_both:
!ctx g_scope_list scope_list e1 e1' e2 e2' binop v n n' n''.
e_multi_exec' (ctx:'a ctx) g_scope_list scope_list e1 n = SOME e1' ==>
is_v e1' ==>
e_multi_exec' (ctx:'a ctx) g_scope_list scope_list e2 n' = SOME e2' ==>
is_v e2' ==>
~is_short_circuitable binop ==>
e_exec_binop e1' binop e2' = SOME v ==>
e_multi_exec' (ctx:'a ctx) g_scope_list scope_list (e_binop e1 binop e2)
          (SUC (n' + n)) = SOME (e_v v)
Proof
rpt strip_tac >>
imp_res_tac bigstep_e_binop_exec_sound_n_second >>
imp_res_tac bigstep_e_binop_exec_sound_n_first >>
gs[e_multi_exec'_def, e_exec_def] >>
Cases_on ‘e1'’ >> (
 gs[is_v_def]
)
QED

Theorem bigstep_e_concat_exec_sound_n_first:
!ctx g_scope_list scope_list e1 e1' e2 n.
e_multi_exec' (ctx:'a ctx) g_scope_list scope_list e1 n = SOME e1' ==>
e_multi_exec' (ctx:'a ctx) g_scope_list scope_list (e_concat e1 e2) n = SOME (e_concat e1' e2)
Proof
Induct_on ‘n’ >> (
 gs[e_multi_exec'_def, e_exec_def, AllCaseEqs()]
) >>
rpt strip_tac >>
imp_res_tac e_exec_not_v >>
res_tac >>
fs[] >>
gs[e_exec_def, AllCaseEqs()] >>
Cases_on ‘e'’ >> (
 gs[is_v_def, is_v_bit_def]
)
QED

Theorem bigstep_e_concat_exec_sound_n_second:
!ctx g_scope_list scope_list e1 e1' e2 e2' n n'.
e_multi_exec' (ctx:'a ctx) g_scope_list scope_list e1 n = SOME e1' ==>
is_v_bit e1' ==>
e_multi_exec' (ctx:'a ctx) g_scope_list scope_list e2 n' = SOME e2' ==>
e_multi_exec' (ctx:'a ctx) g_scope_list scope_list (e_concat e1 e2)
           (n' + n) = SOME (e_concat e1' e2')
Proof
Induct_on ‘n'’ >> (
 rpt strip_tac >>
 gs[e_multi_exec'_def] >>
 imp_res_tac bigstep_e_concat_exec_sound_n_first >>
 gs[]
) >>
Cases_on ‘e_multi_exec' ctx g_scope_list scope_list e2 n'’ >> (
 gs[]
) >>
Cases_on ‘e_exec ctx g_scope_list scope_list x’ >> (
 gs[]
) >>
PairCases_on ‘x'’ >>
gs[] >>
Cases_on ‘x'1’ >> (
 gs[]
) >>
gvs[] >>
Q.SUBGOAL_THEN ‘n + SUC n' = SUC (n' + n)’ (fn thm => REWRITE_TAC [thm]) >- (
 decide_tac
) >>
gs[e_multi_exec'_def] >>
subgoal ‘e_multi_exec' ctx g_scope_list scope_list (e_concat e1 e2)
             (n' + n) = SOME (e_concat e1' x)’ >- (
  qpat_x_assum ‘!ctx. _’ (fn thm => irule thm) >>
  gs[]
) >>
fs[arithmeticTheory.ADD_SYM] >>
gs[e_exec_def] >>
Cases_on ‘e1'’ >> (
 gs[is_v_bit_def]
) >>
subgoal ‘~is_v_bit x’ >- (
 imp_res_tac e_exec_not_v >>
 Cases_on ‘x’ >> (
  gs[is_v_def, is_v_bit_def]
 )
) >>
gs[]
QED

Theorem bigstep_e_concat_exec_sound_n_both:
!ctx g_scope_list scope_list e1 e1' e2 e2' v n n' n''.
e_multi_exec' (ctx:'a ctx) g_scope_list scope_list e1 n = SOME e1' ==>
is_v_bit e1' ==>
e_multi_exec' (ctx:'a ctx) g_scope_list scope_list e2 n' = SOME e2' ==>
is_v_bit e2' ==>
e_exec_concat e1' e2' = SOME v ==>
e_multi_exec' (ctx:'a ctx) g_scope_list scope_list (e_concat e1 e2)
          (SUC (n' + n)) = SOME (e_v v)
Proof
rpt strip_tac >>
imp_res_tac bigstep_e_concat_exec_sound_n_second >>
imp_res_tac bigstep_e_concat_exec_sound_n_first >>
gs[e_multi_exec'_def, e_exec_def] >>
Cases_on ‘e1'’ >> (
 gs[is_v_bit_def]
)
QED

Theorem bigstep_e_slice_exec_sound_n_first:
!ctx g_scope_list scope_list e1 e1' e2 e3 n.
e_multi_exec' (ctx:'a ctx) g_scope_list scope_list e1 n = SOME e1' ==>
is_v_bit e2 ==>
is_v_bit e3 ==>
e_multi_exec' (ctx:'a ctx) g_scope_list scope_list (e_slice e1 e2 e3)
          n = SOME (e_slice e1' e2 e3)
Proof
Induct_on ‘n’ >> (
 rpt strip_tac >>
 gs[e_multi_exec'_def]
) >>
Cases_on ‘e_multi_exec' ctx g_scope_list scope_list e1 n’ >> (
 gs[]
) >>
Cases_on ‘e_exec ctx g_scope_list scope_list x’ >> (
 gs[]
) >>
PairCases_on ‘x'’ >>
gs[] >>
Cases_on ‘x'1’ >> (
 gs[]
) >>
gvs[] >>
imp_res_tac e_exec_not_v >>
res_tac >>
fs[e_exec_def] >>
Cases_on ‘x’ >> (
 gs[is_v_def, is_v_bit_def]
)
QED

Theorem bigstep_e_slice_exec_sound_n_full:
!ctx g_scope_list scope_list e1 e1' e2 e3 v n.
e_multi_exec' (ctx:'a ctx) g_scope_list scope_list e1 n = SOME e1' ==>
is_v_bit e1' ==>
is_v_bit e2 ==>
is_v_bit e3 ==>
e_exec_slice e1' e2 e3 = SOME v ==>
e_multi_exec' (ctx:'a ctx) g_scope_list scope_list (e_slice e1 e2 e3)
          (SUC n) = SOME (e_v v)
Proof
Induct_on ‘n’ >- (
 rpt strip_tac >>
 gs[e_multi_exec'_def] >>
 Cases_on ‘e_exec ctx g_scope_list scope_list (e_slice e1' e2 e3)’ >> (
  gs[]
 ) >> (
  gvs[e_exec_def]
 )
) >>
rpt strip_tac >>
gs[e_multi_exec'_def] >>
Cases_on ‘e_multi_exec' ctx g_scope_list scope_list e1 n’ >> (
 gs[]
) >>
(* TODO: Get this result direcly from lemma... *)
subgoal ‘~is_v_bit x’ >- (
 rpt strip_tac >>
 Cases_on ‘e_exec ctx g_scope_list scope_list x’ >> (
  gs[]
 ) >>
 PairCases_on ‘x'’ >>
 gs[] >>
 Cases_on ‘x'1’ >> (
  gs[]
 ) >>
 Cases_on ‘x’ >> (
  gs[is_v_bit_def, e_exec_def]
 )
) >>
imp_res_tac bigstep_e_slice_exec_sound_n_first >>
gs[] >>
Cases_on ‘e_exec ctx g_scope_list scope_list x’ >> (
 gs[]
) >>
PairCases_on ‘x'’ >>
gs[] >>
Cases_on ‘x'1’ >> (
 gs[]
) >>
gvs[] >>
Cases_on ‘e_exec ctx g_scope_list scope_list (e_slice x e2 e3)’ >> (
 gvs[e_exec_def]
)
QED

Theorem bigstep_e_select_exec_sound_n_first:
!ctx g_scope_list scope_list e1 e1' cases default n.
e_multi_exec' (ctx:'a ctx) g_scope_list scope_list e1 n = SOME e1' ==>
e_multi_exec' (ctx:'a ctx) g_scope_list scope_list (e_select e1 cases default)
          n = SOME (e_select e1' cases default)
Proof
Induct_on ‘n’ >> (
 rpt strip_tac >>
 gs[e_multi_exec'_def]
) >>
Cases_on ‘e_multi_exec' ctx g_scope_list scope_list e1 n’ >> (
 gs[]
) >>
Cases_on ‘e_exec ctx g_scope_list scope_list x’ >> (
 gs[]
) >>
PairCases_on ‘x'’ >>
gs[] >>
Cases_on ‘x'1’ >> (
 gs[]
) >>
gvs[] >>
imp_res_tac e_exec_not_v >>
res_tac >>
fs[e_exec_def] >>
Cases_on ‘x’ >> (
 gs[is_v_def, is_v_bit_def]
)
QED

(* TODO: Move *)
Theorem unred_mem_index_SOME:
!l i.
unred_mem_index l = SOME i ==>
~EVERY is_v l
Proof
rpt strip_tac >>
gs[EVERY_is_v_unred_mem_index]
QED

Theorem e_multi_exec'_list'_LENGTH:
!n ctx g_scope_list scope_list e_l e_l'.
e_multi_exec'_list' ctx g_scope_list scope_list
          e_l n =
        SOME e_l' ==> LENGTH e_l = LENGTH e_l'
Proof
Induct_on ‘n’ >> (
 rpt strip_tac >>
 gs[e_multi_exec'_list'_def, unred_mem_index_def, unred_mem_def, INDEX_FIND_def]
) >>
Cases_on ‘e_multi_exec'_list' ctx g_scope_list
               scope_list e_l n’ >- (
 gs[]
) >>
res_tac >>
gs[] >>
Cases_on ‘INDEX_FIND 0 (\e. ~is_const e) x’ >> (
 gs[]
) >>
PairCases_on ‘x'’ >>
gs[] >>
Cases_on ‘e_exec ctx g_scope_list scope_list (EL x'0 x)’ >> (
 gs[]
) >>
PairCases_on ‘x'’ >>
gs[] >>
Cases_on ‘$var$(x'1')’ >> (
 gvs[]
)
QED

Theorem e_multi_exec'_list'_empty:
!n ctx g_scope_list scope_list.
e_multi_exec'_list' ctx g_scope_list scope_list [] (SUC n) = NONE
Proof
Induct_on ‘n’ >> (
 gs[e_multi_exec'_list'_def, unred_mem_index_def, unred_mem_def, INDEX_FIND_def]
)
QED

Theorem bigstep_e_struct_exec_sound_n:
!ctx g_scope_list' scope_list n x_e_l e_l'.
e_multi_exec'_list' ctx g_scope_list' scope_list (MAP SND x_e_l) n = SOME e_l' ==>
x_e_l <> [] ==>
if EVERY is_v e_l' then (e_multi_exec' (ctx:'a ctx) g_scope_list' scope_list (e_struct x_e_l) (SUC n) = SOME (e_v $ v_struct (ZIP (MAP FST x_e_l,vl_of_el e_l')))) else (e_multi_exec' (ctx:'a ctx) g_scope_list' scope_list (e_struct x_e_l) n = SOME (e_struct (ZIP (MAP FST x_e_l, e_l'))))
Proof
Induct_on ‘n’ >- (
 rpt strip_tac >>
 gs[e_multi_exec'_def, e_multi_exec'_list'_def] >>
 gs[e_exec_def] >>
 Cases_on ‘EVERY is_v e_l'’ >> (
  FULL_SIMP_TAC pure_ss []
 ) >- (
  subgoal ‘unred_mem_index e_l' = NONE’ >- (
   gs[EVERY_is_v_unred_mem_index]
  ) >>
  gs[]
 ) >>
 subgoal ‘?i. unred_mem_index e_l' = SOME i’ >- (
  gs[not_EVERY_is_v_unred_mem_index]
 ) >>
 gvs[ZIP_MAP_FST_SND]
) >>
rpt strip_tac >>
gs[e_multi_exec'_list'_def, e_multi_exec'_def] >>
Cases_on ‘EVERY is_v e_l'’ >> (
 FULL_SIMP_TAC pure_ss []
) >- (
 gs[] >>
 Cases_on ‘x_e_l’ >> (
  gs[e_multi_exec'_list'_def, e_multi_exec'_def]
 ) >>
 gs[e_multi_exec'_list'_def, e_multi_exec'_def] >>
 Cases_on ‘e_multi_exec'_list' ctx g_scope_list' scope_list
              (SND h::MAP SND t) n’ >> (
  gs[]
 ) >>
 Cases_on ‘unred_mem_index x’ >- (
  gs[]
 ) >>
 gvs[] >>
 FULL_SIMP_TAC pure_ss [GSYM MAP] >>
 res_tac >>
 fs[] >>
 subgoal ‘~EVERY is_v x’ >- (
  metis_tac[unred_mem_index_SOME]
 ) >>
 FULL_SIMP_TAC pure_ss [] >>
 gs[e_exec_def] >>
 (* TODO: Prove the below earlier *)
 subgoal ‘LENGTH (MAP SND (h::t)) = LENGTH x’ >- (
  imp_res_tac e_multi_exec'_list'_LENGTH >>
  gs[]
 ) >>
 gs[MAP_ZIP] >>
 Cases_on ‘e_exec ctx g_scope_list' scope_list (EL x' x)’ >> (
  gs[]
 ) >>
 PairCases_on ‘x''’ >>
 gs[] >>
 Cases_on ‘x''1’ >> (
  gs[]
 ) >>
 gvs[] >>
 gs[e_exec_def, MAP_ZIP] >>
 subgoal ‘unred_mem_index (LUPDATE x''0 x' x) = NONE’ >- (
  gs[EVERY_is_v_unred_mem_index]
 ) >>
 gs[]
) >>
(* Pretty much identical to the above *)
gs[] >>
Cases_on ‘x_e_l’ >> (
 gs[e_multi_exec'_list'_def, e_multi_exec'_def]
) >>
Cases_on ‘e_multi_exec'_list' ctx g_scope_list' scope_list
             (SND h::MAP SND t) n’ >> (
 gs[]
) >>
Cases_on ‘unred_mem_index x’ >- (
 gs[]
) >>
gvs[] >>
FULL_SIMP_TAC pure_ss [GSYM MAP] >>
res_tac >>
fs[] >>
subgoal ‘~EVERY is_v x’ >- (
 gs[unred_mem_index_def, unred_mem_def, GSYM is_v_is_const] >>
 Cases_on ‘INDEX_FIND 0 (\e. ~is_v e) x’ >> (
  gs[]
 ) >>
 PairCases_on ‘x''’ >>
 subgoal ‘IS_SOME $ INDEX_FIND 0 (\e. ~is_v e) x’ >- (
  gs[optionTheory.IS_SOME_EXISTS]
 ) >>
 gs[INDEX_FIND_SOME_EXISTS] >>
 metis_tac[]
) >>
FULL_SIMP_TAC pure_ss [] >>
gs[e_exec_def] >>
subgoal ‘LENGTH (MAP SND (h::t)) = LENGTH x’ >- (
 imp_res_tac e_multi_exec'_list'_LENGTH >>
 gs[]
) >>
gs[MAP_ZIP] >>
Cases_on ‘e_exec ctx g_scope_list' scope_list (EL x' x)’ >> (
 gs[]
) >>
PairCases_on ‘x''’ >>
gs[] >>
Cases_on ‘x''1’ >> (
 gs[]
)
QED

Theorem e_multi_exec'_list'_comp:
!ctx g_scope_list scope_list e_l e_l' n n' e e'.
e_multi_exec' ctx g_scope_list scope_list e n' = SOME e' ==>
n >= n' ==>
(n > n' ==> is_v e') ==>
e_multi_exec'_list' ctx g_scope_list scope_list e_l (n - n') = SOME e_l' ==>
e_multi_exec'_list' ctx g_scope_list scope_list (e::e_l) n = SOME (e'::e_l')
Proof
Induct_on ‘n’ >- (
 rpt strip_tac >>
 gs[e_multi_exec'_list'_def, e_multi_exec'_def] >>
 subgoal ‘n' = 0’ >- (
  gs[]
 ) >>
 fs[e_multi_exec'_def]
) >>
rpt strip_tac >>
gs[e_multi_exec'_list'_def, e_multi_exec'_def] >>
Cases_on ‘SUC n = n'’ >- (
 gvs[] >>
 gs[e_multi_exec'_list'_def, e_multi_exec'_def] >>
 Cases_on ‘e_multi_exec' ctx g_scope_list scope_list e n’ >> (
  gs[]
 ) >>
 res_tac >>
 gvs[e_multi_exec'_list'_def, e_multi_exec'_def] >>
 Cases_on ‘e_exec ctx g_scope_list scope_list x’ >> (
  gs[]
 ) >>
 PairCases_on ‘x'’ >>
 gs[] >>
 Cases_on ‘x'1’ >>
 gvs[] >>
 subgoal ‘~is_v x’ >- (
  Cases_on ‘x’ >> (
   gs[is_v_def, e_exec_def]
  )
 ) >>
 subgoal ‘unred_mem_index (x::e_l) = SOME 0’ >- (
  gs[unred_mem_index_def, unred_mem_def, INDEX_FIND_def, is_v_is_const]
 ) >>
 gs[LUPDATE_def]
) >>
gvs[] >>
subgoal ‘SUC n - n' = SUC (n - n')’ >- (
 decide_tac
) >>
fs[] >>
Cases_on ‘e_l’ >> (
 gs[]
) >- (
 gs[e_multi_exec'_list'_empty]
) >>
gs[e_multi_exec'_list'_def, e_multi_exec'_def] >>
Cases_on ‘e_multi_exec'_list' ctx g_scope_list scope_list (h::t) (n - n')’ >> (
 gs[]
) >>
res_tac >>
gs[] >>
Cases_on ‘n > n'’ >> (
 gs[e_multi_exec'_list'_def, e_multi_exec'_def]
) >> (
 Cases_on ‘unred_mem_index x’ >> (
  gvs[]
 )
) >> (
 (* TODO: Resolve second case faster? *)
 res_tac >>
 fs[] >>
 subgoal ‘unred_mem_index (e'::x) = SOME (x'+1)’ >- (
  fs[unred_mem_index_def, unred_mem_def, INDEX_FIND_def, is_v_is_const, Once INDEX_FIND_add] >>
  Cases_on ‘INDEX_FIND 0 (\e. ~is_const e) x’ >> (
   gs[]
  ) >>
  PairCases_on ‘x''’ >>
  gs[] >>
  Cases_on ‘x''1’ >>
  gvs[]
 ) >>
 gs[] >>
 Cases_on ‘e_exec ctx g_scope_list scope_list (EL x' x)’ >> (
  gs[]
 ) >>
 PairCases_on ‘x''’ >>
 gs[] >>
 Cases_on ‘x''1’ >>
 gvs[] >>
 subgoal ‘e_exec ctx g_scope_list scope_list (EL (x' + 1) (e'::x)) = SOME (x''0,[])’ >- (
  ‘EL (x' + 1) (e'::x) = EL x' x’ suffices_by (
   gs[]
  ) >>
  gs[GSYM SUC_ADD_ONE]
 ) >>
 gs[GSYM SUC_ADD_ONE, LUPDATE_def]
)
QED

Theorem e_multi_exec'_list'_comp0:
!ctx g_scope_list scope_list e_l n e e'.
e_multi_exec' ctx g_scope_list scope_list e n = SOME e' ==>
e_multi_exec'_list' ctx g_scope_list scope_list (e::e_l) n = SOME (e'::e_l)
Proof
Induct_on ‘n’ >> (
 rpt strip_tac >>
 gs[e_multi_exec'_list'_def, e_multi_exec'_def]
) >>
Cases_on ‘e_multi_exec' ctx g_scope_list scope_list e n’ >> (
 gs[]
) >>
res_tac >>
fs[] >>
subgoal ‘~is_v x’ >- (
 Cases_on ‘x’ >> (
  gs[is_v_def, e_exec_def]
 )
) >>
subgoal ‘unred_mem_index (x::e_l) = SOME 0’ >- (
 gs[unred_mem_index_def, unred_mem_def, GSYM is_v_is_const, INDEX_FIND_def]
) >>
(* OK *)
gs[] >>
Cases_on ‘e_exec ctx g_scope_list scope_list x’ >> (
 gs[]
) >>
PairCases_on ‘x'’ >>
gs[] >>
Cases_on ‘x'1’ >>
gvs[LUPDATE_def]
QED

Theorem bigstep_e_exec_sound_n:
!t n n' scope_list e e_l g_scope_list' t' ctx.
bigstep_e_exec (scope_list ++ g_scope_list') t n' = SOME (t', n' + n) ==>
 (t = (INL e) ==>
  (?e'. (t' = (INL e')) /\
   e_multi_exec' (ctx:'a ctx)
    g_scope_list' scope_list e n = SOME e')) /\
 (t = INR e_l ==>
  (?e_l'. (t' = (INR e_l')) /\
   e_multi_exec'_list' ctx
    g_scope_list' scope_list e_l n = SOME e_l'))
Proof
measureInduct_on ‘( \ t. case t of
                           | (INL e) => e_size e
                           | (INR e_l) => e3_size e_l) t’ >>
Induct_on ‘t’ >- (
 (* INL case *)
 Induct_on ‘x’ >> (
  rpt strip_tac >>
  fs[]
 ) >- (
  (* value *)
  Cases_on ‘n’ >> (
   gvs[e_multi_exec'_def, bigstep_e_exec_def]
  )
 ) >- (
  (* variable *)
  gvs[bigstep_e_exec_var_REWR] >>
  Cases_on ‘n’ >> (
   gs[]
  ) >>
  FULL_SIMP_TAC pure_ss [Once arithmeticTheory.ONE, e_multi_exec'_def] >>
  gvs[e_exec_def, lookup_vexp_def, lookup_vexp2_def]
 ) >- (
  (* list *)
  Cases_on ‘n’ >> (
   gvs[e_multi_exec'_def, bigstep_e_exec_def]
  )
 ) >- (
  (* access *)
  (* 1. Compute result (results in case of multiple shapes) of e_multi_exec' of e_acc x s
   *    (in the goal).
   * 2. Use bigstep_e_acc_exec_sound_n_v to reduce goal to proving reduction of inner
   *    expression of e_acc x s, that is, x.
   * 3. Use the simple induction hypothesis with the nested expression x (i.e. INL x).
   * *)
  gvs[bigstep_e_exec_acc_REWR] >- (
   qpat_x_assum ‘e_exec_acc (e_acc e_v_struct s) = SOME e'’ (fn thm => REWRITE_TAC [GSYM thm]) >>
   (* After starting from n' *)
   Q.SUBGOAL_THEN ‘n = SUC (n'' - n')’ (fn thm => REWRITE_TAC [thm]) >- (
    imp_res_tac bigstep_e_exec_incr >>
    decide_tac
   ) >>
   gs[GSYM SUC_ADD_ONE] >>
   irule bigstep_e_acc_exec_sound_n_v >>
   gs[] >>
   qpat_x_assum ‘!y. _’ (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
   gs[e_size_def] >>
   res_tac >>
   gs[] >>
   (* Done after some arithmetic, use ((x'1 -n') + n') *)
   subgoal ‘n'' = (n - 1) + n'’ >- (
    imp_res_tac bigstep_e_exec_incr >>
    decide_tac
   ) >>
   FULL_SIMP_TAC pure_ss [] >>
   res_tac >>
   FULL_SIMP_TAC std_ss []
  ) >>
  gvs[] >>
  irule bigstep_e_acc_exec_sound_n_not_v >>
  gs[] >>
  PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
  gs[e_size_def] >>
  res_tac >>
  gs[]
 ) >- (
  (* unary arithmetic *)
  gvs[bigstep_e_exec_unop_REWR] >- (
   Q.SUBGOAL_THEN ‘n = SUC (n'' - n')’ (fn thm => REWRITE_TAC [thm]) >- (
    imp_res_tac bigstep_e_exec_incr >>
    decide_tac
   ) >>
   gs[GSYM SUC_ADD_ONE] >>
   irule bigstep_e_unop_exec_sound_n_v >>
   qexists_tac ‘e'’ >>
   gs[] >>
   qpat_x_assum ‘!y. _’ (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
   gs[e_size_def] >>
   res_tac >>
   gs[] >>
   (* Done after some arithmetic, use ((x'1 -n') + n') *)
   subgoal ‘n'' = (n - 1) + n'’ >- (
    imp_res_tac bigstep_e_exec_incr >>
    decide_tac
   ) >>
   FULL_SIMP_TAC pure_ss [] >>
   res_tac >>
   FULL_SIMP_TAC std_ss []
  ) >>
  gvs[] >>
  irule bigstep_e_unop_exec_sound_n_not_v >>
  gs[] >>
  PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
  gs[e_size_def] >>
  res_tac >>
  gs[]
 ) >- (
  (* cast *)
  gvs[bigstep_e_exec_cast_REWR] >- (
   Q.SUBGOAL_THEN ‘n = SUC (n'' - n')’ (fn thm => REWRITE_TAC [thm]) >- (
    imp_res_tac bigstep_e_exec_incr >>
    decide_tac
   ) >>
   gs[GSYM SUC_ADD_ONE] >>
   irule bigstep_e_cast_exec_sound_n_v >>
   qexists_tac ‘e'’ >>
   gs[] >>
   qpat_x_assum ‘!y. _’ (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
   gs[e_size_def] >>
   res_tac >>
   gs[] >>
   (* Done after some arithmetic, use ((x'1 -n') + n') *)
   subgoal ‘n'' = (n - 1) + n'’ >- (
    imp_res_tac bigstep_e_exec_incr >>
    decide_tac
   ) >>
   FULL_SIMP_TAC pure_ss [] >>
   res_tac >>
   FULL_SIMP_TAC std_ss []
  ) >>
  gvs[] >>
  irule bigstep_e_cast_exec_sound_n_not_v >>
  gs[] >>
  PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
  gs[e_size_def] >>
  res_tac >>
  gs[]
 ) >- (
  (* binary arithmetic *)
  gvs[bigstep_e_exec_binop_REWR] >- (
   (* Reduction of first operand, then short-circuit *)
   qpat_x_assum ‘e_exec_short_circuit v b x' = SOME e'’ (fn thm => REWRITE_TAC [GSYM thm]) >>
   Q.SUBGOAL_THEN ‘n = SUC (n'' - n')’ (fn thm => REWRITE_TAC [thm]) >- (
    imp_res_tac bigstep_e_exec_incr >>
    decide_tac
   ) >>
   gs[GSYM SUC_ADD_ONE] >>
   irule bigstep_e_binop_exec_sound_n_first_shortcircuit >>
   gs[] >>
   qpat_x_assum ‘!y. _’ (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
   gs[e_size_def] >>
   qpat_x_assum ‘!n''. _’ (fn thm => ASSUME_TAC (Q.SPECL [‘(n'' - n')’, ‘n'’] thm)) >>
   imp_res_tac bigstep_e_exec_incr >>
   gs[] >>
   res_tac >>
   fs[]
  ) >- (
   (* Full reduction of both operands *)
   Q.SUBGOAL_THEN ‘n = SUC ((n'3' - n'') + (n''- n'))’ (fn thm => REWRITE_TAC [thm]) >- (
    imp_res_tac bigstep_e_exec_incr >>
    decide_tac
   ) >>
   irule bigstep_e_binop_exec_sound_n_both >>
   gs[] >>
   qpat_assum ‘!y. _’ (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
   qpat_x_assum ‘!y. _’ (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x')’] thm)) >>
   gs[e_size_def] >>
   qpat_x_assum ‘!n''. _’ (fn thm => ASSUME_TAC (Q.SPECL [‘(n'3' - n'')’, ‘n''’] thm)) >>
   qpat_x_assum ‘!n''. _’ (fn thm => ASSUME_TAC (Q.SPECL [‘(n'' - n')’, ‘n'’] thm)) >>
   imp_res_tac bigstep_e_exec_incr >>
   gs[] >>
   res_tac >>
   fs[]
  ) >- (
   (* Reduction of 1st, then partially of 2nd operand *)
   Q.SUBGOAL_THEN ‘n = (((n + n') - n'') + (n''- n'))’ (fn thm => REWRITE_TAC [Once thm]) >- (
    imp_res_tac bigstep_e_exec_incr >>
    decide_tac
   ) >>
   irule bigstep_e_binop_exec_sound_n_second >>
   gs[] >>
   qpat_assum ‘!y. _’ (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
   qpat_x_assum ‘!y. _’ (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x')’] thm)) >>
   gs[e_size_def] >>
   qpat_x_assum ‘!n''. _’ (fn thm => ASSUME_TAC (Q.SPECL [‘(n + n') - n''’, ‘n''’] thm)) >>
   qpat_x_assum ‘!n''. _’ (fn thm => ASSUME_TAC (Q.SPECL [‘(n'' - n')’, ‘n'’] thm)) >>
   imp_res_tac bigstep_e_exec_incr >>
   gs[] >>
   res_tac >>
   fs[]
  ) >>
  (* Reduction of 1st operand only *)
  irule bigstep_e_binop_exec_sound_n_first >>
  qpat_x_assum ‘!y. _’ (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
  gs[e_size_def] >>
  qpat_x_assum ‘!n''. _’ (fn thm => ASSUME_TAC (Q.SPECL [‘(n + n') - n'’, ‘n'’] thm)) >>
  gs[] >>
  res_tac >>
  fs[]
 ) >- (
  (* concat *)
  gvs[bigstep_e_exec_concat_REWR] >- (
   (* All operands fully reduced *)
   Q.SUBGOAL_THEN ‘n = SUC ((n'3' - n'') + (n''- n'))’ (fn thm => REWRITE_TAC [Once thm]) >- (
    imp_res_tac bigstep_e_exec_incr >>
    decide_tac
   ) >>
   irule bigstep_e_concat_exec_sound_n_both >>
   gs[] >>
   qpat_assum ‘!y. _’ (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
   qpat_x_assum ‘!y. _’ (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x')’] thm)) >>
   gs[e_size_def] >>
   qpat_x_assum ‘!n''. _’ (fn thm => ASSUME_TAC (Q.SPECL [‘(n'3' - n'')’, ‘n''’] thm)) >>
   qpat_x_assum ‘!n''. _’ (fn thm => ASSUME_TAC (Q.SPECL [‘(n'' - n')’, ‘n'’] thm)) >>
   imp_res_tac bigstep_e_exec_incr >>
   gs[] >>
   res_tac >>
   fs[]
  ) >- (
   (* Reduction of 1st + 2nd operand *)
   Q.SUBGOAL_THEN ‘n = (((n + n') - n'') + (n''- n'))’ (fn thm => REWRITE_TAC [Once thm]) >- (
    imp_res_tac bigstep_e_exec_incr >>
    decide_tac
   ) >>
   irule bigstep_e_concat_exec_sound_n_second >>
   gs[] >>
   qpat_assum ‘!y. _’ (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
   qpat_x_assum ‘!y. _’ (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x')’] thm)) >>
   gs[e_size_def] >>
   qpat_x_assum ‘!n''. _’ (fn thm => ASSUME_TAC (Q.SPECL [‘(n + n') - n''’, ‘n''’] thm)) >>
   qpat_x_assum ‘!n''. _’ (fn thm => ASSUME_TAC (Q.SPECL [‘(n'' - n')’, ‘n'’] thm)) >>
   imp_res_tac bigstep_e_exec_incr >>
   gs[] >>
   res_tac >>
   fs[]
  ) >>
  (* Reduction of 1st operand *)
  irule bigstep_e_concat_exec_sound_n_first >>
  qpat_x_assum ‘!y. _’ (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
  gs[e_size_def] >>
  qpat_x_assum ‘!n''. _’ (fn thm => ASSUME_TAC (Q.SPECL [‘(n + n') - n'’, ‘n'’] thm)) >>
  gs[] >>
  res_tac >>
  fs[]
 ) >- (
  (* slicing *)
  gvs[bigstep_e_exec_slice_REWR] >- (
   Q.SUBGOAL_THEN ‘n = SUC (n'' - n')’ (fn thm => REWRITE_TAC [Once thm]) >- (
    imp_res_tac bigstep_e_exec_incr >>
    decide_tac
   ) >>
   irule bigstep_e_slice_exec_sound_n_full >>
   gs[] >>
   qpat_x_assum ‘!y. _’ (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
   gs[e_size_def] >>
   qpat_x_assum ‘!n''. _’ (fn thm => ASSUME_TAC (Q.SPECL [‘(n'' - n')’, ‘n'’] thm)) >>
   imp_res_tac bigstep_e_exec_incr >>
   gs[] >>
   res_tac >>
   fs[]
  ) >>
  (* Reduction of operand to be sliced *)
  irule bigstep_e_slice_exec_sound_n_first >>
  qpat_x_assum ‘!y. _’ (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
  gs[e_size_def] >>
  qpat_x_assum ‘!n''. _’ (fn thm => ASSUME_TAC (Q.SPECL [‘(n + n') - n'’, ‘n'’] thm)) >>
  gs[] >>
  res_tac >>
  fs[]
 ) >- (
  (* call *)
  Cases_on ‘n’ >> (
   gvs[e_multi_exec'_def, bigstep_e_exec_def]
  )
 ) >- (
  (* select *)
  gvs[bigstep_e_exec_select_REWR] >>
  irule bigstep_e_select_exec_sound_n_first >>
  qpat_x_assum ‘!y. _’ (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
  gs[e_size_def] >>
  qpat_x_assum ‘!n''. _’ (fn thm => ASSUME_TAC (Q.SPECL [‘(n + n') - n'’, ‘n'’] thm)) >>
  gs[] >>
  res_tac >>
  fs[]
 ) >- (
  (* struct *)
  gvs[bigstep_e_exec_struct_REWR] >- (
   Cases_on ‘l’ >- (
    gs[bigstep_e_exec_def, GSYM SUC_ADD_ONE] >>
    subgoal ‘n = 1’ >- (
     decide_tac
    ) >>
    fs[] >>
    FULL_SIMP_TAC pure_ss [Once arithmeticTheory.ONE] >>
    gs[e_multi_exec'_def, e_exec_def, unred_mem_index_def, unred_mem_def, INDEX_FIND_def]
   ) >>
   qpat_x_assum ‘!y. _’ (fn thm => assume_tac (Q.SPECL [‘(INR (MAP SND ((h::t):(string # e) list)))’] thm)) >>
   gs[e_size_def] >>
   subgoal ‘e3_size (MAP SND (h::t)) < e1_size (h::t) + 1’ >- (
    gs[e3_e1_size]
   ) >>
   gs[e_size_def] >>
   qpat_x_assum ‘!n'' n'3'. _’ (fn thm => assume_tac (Q.SPECL [‘n'' - n'’, ‘n'’] thm)) >>
   gs[] >>
   subgoal ‘n'' - n' + n' = n''’ >- (
    imp_res_tac bigstep_e_exec_incr >>
    decide_tac
   ) >>
   gs[] >>
   res_tac >>
   fs[] >>
   qpat_x_assum ‘!ctx. _’ (fn thm => assume_tac (Q.SPECL [‘ctx’] thm)) >>
   gs[] >>
   Cases_on ‘n’ >> (
    gs[]
   ) >>
   FULL_SIMP_TAC pure_ss [GSYM SUC_ADD_ONE, GSYM MAP] >>
   imp_res_tac bigstep_e_struct_exec_sound_n >>
   gs[] >>
   subgoal ‘n'3' = n'' - n'’ >- (
    decide_tac
   ) >>
   fs[]
  ) >>
  qpat_x_assum ‘!y. _’ (fn thm => assume_tac (Q.SPECL [‘(INR (MAP SND (l:(string # e) list)))’] thm)) >>
  gs[e_size_def] >>
  subgoal ‘e3_size (MAP SND l) < e1_size l + 1’ >- (
   gs[e3_e1_size]
  ) >>
  gs[e_size_def] >>
  qpat_x_assum ‘!n'' n'3'. _’ (fn thm => assume_tac (Q.SPECL [‘n’, ‘n'’] thm)) >>
  gs[] >>
  res_tac >>
  fs[] >>
  qpat_x_assum ‘!ctx. _’ (fn thm => assume_tac (Q.SPECL [‘ctx’] thm)) >>
  imp_res_tac bigstep_e_struct_exec_sound_n >>
  Cases_on ‘l’ >- (
   gvs[bigstep_e_exec_def]
  ) >>
  gs[] >>
  Q.SUBGOAL_THEN ‘~EVERY is_v e_l'’ (fn thm => gs[thm]) >- (
   gs[]
  )
 ) >> (
  (* header *)
  Cases_on ‘n’ >> (
   gvs[e_multi_exec'_def, bigstep_e_exec_def]
  )
 )
) >>
(* INR case *)
Induct_on ‘y’ >> (
 rpt strip_tac >>
 gs[bigstep_e_exec_def]
) >- (
 Cases_on ‘n’ >> (
  gs[e_multi_exec'_list'_def]
 )
) >>
Cases_on ‘bigstep_e_exec (scope_list ++ g_scope_list') (INL h) n'’ >> (
 gs[]
) >>
PairCases_on ‘x’ >>
gs[] >>
Cases_on ‘x0’ >>
gs[] >>
Cases_on ‘is_v x’ >> (
 gs[]
) >- (
 Cases_on ‘bigstep_e_exec (scope_list ++ g_scope_list') (INR y) x1’ >> (
  gs[]
 ) >>
 PairCases_on ‘x'’ >>
 gs[] >>
 Cases_on ‘x'0’ >>
 gs[] >>
 gvs[] >>
 PAT_ASSUM “!y'. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL h)’] thm)) >>
 gs[e_size_def] >>
 qpat_x_assum ‘!n'' n'3'. _’ (fn thm => assume_tac (Q.SPECL [‘x1 - n'’, ‘n'’] thm)) >>
 gs[] >>
 subgoal ‘x1 - n' + n' = x1’ >- (
  imp_res_tac bigstep_e_exec_incr >>
  decide_tac
 ) >>
 gs[] >>
 res_tac >>
 qpat_x_assum ‘!ctx. _’ (fn thm => assume_tac (Q.SPECL [‘ctx’] thm)) >>
 gs[] >>
 PAT_ASSUM “!y'. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INR y)’] thm)) >>
 gs[e_size_def] >>
 qpat_x_assum ‘!n'' n'3'. _’ (fn thm => assume_tac (Q.SPECL [‘n + n' - x1’, ‘x1’] thm)) >>
 gs[] >>
 subgoal ‘n + n' - x1 + x1 = n + n'’ >- (
  imp_res_tac bigstep_e_exec_incr >>
  decide_tac
 ) >>
 gs[] >>
 res_tac >>
 qpat_x_assum ‘!ctx. ?e_l'.
          INR y' = INR e_l' /\
          e_multi_exec'_list' ctx g_scope_list' scope_list y
            (n + n' - x1) =
          SOME e_l'’ (fn thm => assume_tac (Q.SPECL [‘ctx’] thm)) >>
 fs[] >>
 irule e_multi_exec'_list'_comp >>
 fs[] >>
 qexists_tac ‘x1 - n'’ >>
 fs[]
) >>
gvs[] >>
irule e_multi_exec'_list'_comp0 >>
PAT_ASSUM “!y'. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL h)’] thm)) >>
gs[e_size_def] >>
qpat_x_assum ‘!n'' n'3'. _’ (fn thm => assume_tac (Q.SPECL [‘n’, ‘n'’] thm)) >>
res_tac >>
qpat_x_assum ‘!ctx. _’ (fn thm => assume_tac (Q.SPECL [‘ctx’] thm)) >>
fs[]
QED

Theorem bigstep_e_exec_sound_n_INL:
!e e' n n' scope_list g_scope_list' ctx.
bigstep_e_exec (scope_list ++ g_scope_list') (INL e) n' = SOME (INL e', n'+n) ==>
 e_multi_exec' (ctx:'a ctx) g_scope_list' scope_list e n = SOME e'
Proof
rpt strip_tac >>
imp_res_tac bigstep_e_exec_sound_n >>
gvs[]
QED

(* Most commonly used version of bigstep_e_exec_sound_n_INL *)
Theorem bigstep_e_exec_sound_n_INL_zero:
!e e' n n' scope_list g_scope_list' ctx.
bigstep_e_exec (scope_list ++ g_scope_list') (INL e) n' = SOME (INL e', n' + n) ==>
 e_multi_exec' (ctx:'a ctx) g_scope_list' scope_list e n = SOME e'
Proof
rpt strip_tac >>
irule bigstep_e_exec_sound_n_INL >>
metis_tac[]
QED

Theorem bigstep_e_exec_sound_n_INR:
!e_l e_l' n n' scope_list g_scope_list' ctx.
bigstep_e_exec (scope_list ++ g_scope_list') (INR e_l) n' = SOME (INR e_l', n'+n) ==>
 e_multi_exec'_list' (ctx:'a ctx) g_scope_list' scope_list e_l n = SOME e_l'
Proof
rpt strip_tac >>
imp_res_tac bigstep_e_exec_sound_n >>
gvs[]
QED

Theorem bigstep_e_exec_sound_n_INR_zero:
!e_l e_l' n n' scope_list g_scope_list' ctx.
bigstep_e_exec (scope_list ++ g_scope_list') (INR e_l) n' = SOME (INR e_l', n'+n) ==>
 e_multi_exec'_list' (ctx:'a ctx) g_scope_list' scope_list e_l n = SOME e_l'
Proof
rpt strip_tac >>
irule bigstep_e_exec_sound_n_INR >>
metis_tac[]
QED

Definition stmt_multi_exec'_check_state_def:
 (stmt_multi_exec'_check_state ((ascope, [g_scope1; g_scope2], [(funn, stmt::stmts, scope_list)], status_running):'a state)
                               ((ascope', [g_scope1'; g_scope2'], [(funn', stmt'::stmts', scope_list')], status_running):'a state) =
  if ascope = ascope' /\ funn = funn' /\ stmts = stmts' /\ LENGTH scope_list = LENGTH scope_list'
  then SOME (ascope, [g_scope1'; g_scope2'], [(funn, stmt'::stmts, scope_list')], status_running)
  else NONE
)
 /\
 (stmt_multi_exec'_check_state _ _ = NONE)
End

Theorem stmt_multi_exec'_check_state_second:
!stmts ascope g_scope1 g_scope2 funn stmt stmt' scope_list scope_list' state2 g_scope_list'.
stmt_multi_exec'_check_state ((ascope, [g_scope1; g_scope2], [(funn, stmt::stmts, scope_list)], status_running):'a state) state2 = SOME (ascope,g_scope_list',[(funn,stmt'::stmts,scope_list')],status_running) ==>
?g_scope1' g_scope2'.
g_scope_list' = [g_scope1'; g_scope2'] /\
state2 = (ascope, g_scope_list', [(funn, stmt'::stmts, scope_list')], status_running)
Proof
rpt strip_tac >>
PairCases_on ‘state2’ >>
Cases_on ‘state21’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘t’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘t'’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘state22’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘t’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
PairCases_on ‘h''’ >>
Cases_on ‘state23’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘h''1’ >- (
 gs[stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘t’ >> (
 qexistsl_tac [‘h’, ‘h'’] >>
 (* Odd looping issue here... *)
 FULL_SIMP_TAC pure_ss [stmt_multi_exec'_check_state_def] >>
 gs[]
)
QED

Theorem stmt_multi_exec'_check_state_eq_NONE:
!ascope g_scope_list frame_list status.
stmt_multi_exec'_check_state (ascope,g_scope_list,frame_list,status)
 (ascope,g_scope_list,frame_list,status) = NONE <=>
(status <> status_running) \/ (LENGTH g_scope_list <> 2) \/
~(?funn stmt stmts scope_list.
  frame_list = [(funn,stmt::stmts,scope_list)])
Proof
rpt strip_tac >>
eq_tac >> (
 Cases_on ‘g_scope_list’ >> (
  gs[stmt_multi_exec'_check_state_def]
 ) >>
 Cases_on ‘t’ >> (
  gs[stmt_multi_exec'_check_state_def]
 ) >>
 Cases_on ‘t'’ >> (
  gs[stmt_multi_exec'_check_state_def]
 ) >>
 Cases_on ‘status’ >> (
  gs[stmt_multi_exec'_check_state_def]
 ) >>
 Cases_on ‘frame_list’ >> (
  gs[stmt_multi_exec'_check_state_def]
 ) >>
 Cases_on ‘t’ >> (
  gs[stmt_multi_exec'_check_state_def]
 ) >>
 PairCases_on ‘h''’ >>
 Cases_on ‘h''1’ >> (
  gs[stmt_multi_exec'_check_state_def]
 )
)
QED

Theorem stmt_multi_exec'_check_state_NONE:
!ascope g_scope_list frame_list status ascope' g_scope_list' frame_list' status'.
stmt_multi_exec'_check_state (ascope,g_scope_list,frame_list,status)
 (ascope',g_scope_list',frame_list',status') = NONE <=>
(ascope <> ascope') \/
(status <> status_running) \/ (status' <> status_running) \/
(LENGTH g_scope_list <> 2) \/ (LENGTH g_scope_list' <> 2) \/
~(?funn stmt stmt' stmts scope_list scope_list'.
  frame_list = [(funn,stmt::stmts,scope_list)] /\
  frame_list' = [(funn,stmt'::stmts,scope_list')] /\ LENGTH scope_list = LENGTH scope_list')
Proof
rpt strip_tac >>
eq_tac >- (
 Cases_on ‘g_scope_list’ >> (
  gs[stmt_multi_exec'_check_state_def]
 ) >>
 Cases_on ‘t’ >> (
  gs[stmt_multi_exec'_check_state_def]
 ) >>
 Cases_on ‘t'’ >> (
  gs[stmt_multi_exec'_check_state_def]
 ) >>
 Cases_on ‘status’ >> (
  gs[stmt_multi_exec'_check_state_def]
 ) >>
 Cases_on ‘frame_list’ >> (
  gs[stmt_multi_exec'_check_state_def]
 ) >>
 Cases_on ‘t’ >> (
  gs[stmt_multi_exec'_check_state_def]
 ) >>
 PairCases_on ‘h''’ >>
 Cases_on ‘h''1’ >> (
  gs[stmt_multi_exec'_check_state_def]
 ) >>
 Cases_on ‘frame_list'’ >> (
  gs[stmt_multi_exec'_check_state_def]
 ) >>
 Cases_on ‘t'’ >> (
  gs[stmt_multi_exec'_check_state_def]
 ) >>
 PairCases_on ‘h'3'’ >>
 Cases_on ‘h'''1’ >> (
  gs[stmt_multi_exec'_check_state_def]
 ) >>
 Cases_on ‘status'’ >> (
  gs[stmt_multi_exec'_check_state_def]
 ) >>
 rpt strip_tac >>
 gvs[stmt_multi_exec'_check_state_def] >>
 Cases_on ‘g_scope_list'’ >> (
  gs[stmt_multi_exec'_check_state_def]
 ) >>
 Cases_on ‘t'’ >> (
  gs[stmt_multi_exec'_check_state_def]
 )
) >>
rpt strip_tac >>
Cases_on ‘g_scope_list’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘t’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘t'’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘frame_list’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘t’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
PairCases_on ‘h''’ >>
Cases_on ‘status’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘h''1’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘g_scope_list'’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘t'’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘t''’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘frame_list'’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘t'’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
PairCases_on ‘h'5'’ >>
Cases_on ‘status'’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘h'''''1’ >> (
 gs[stmt_multi_exec'_check_state_def]
)
QED

Definition stmt_multi_exec'_def:
 (stmt_multi_exec' ctx state 0 = stmt_multi_exec'_check_state state state)
 /\
 (stmt_multi_exec' (ctx:'a ctx) state (SUC fuel) =
  case stmt_multi_exec' ctx state fuel of
  | SOME state' =>
   (case stmt_exec ctx state' of
    | SOME state'' => stmt_multi_exec'_check_state state state''
    | NONE => NONE)
  | _ => NONE)
End

Theorem stmt_multi_exec'_SOME_imp:
!ctx stmts ascope g_scope1 g_scope2 funn stmt scope_list n ascope' g_scope_list' arch_frame_list' status'.
stmt_multi_exec' (ctx:'a ctx) ((ascope, [g_scope1; g_scope2], [(funn, stmt::stmts, scope_list)], status_running):'a state) n =
 SOME ((ascope', g_scope_list', arch_frame_list', status'):'a state) ==>
ascope = ascope' /\ ?g_scope1' g_scope2'. g_scope_list' = [g_scope1'; g_scope2'] /\
?stmt' scope_list'. arch_frame_list' = [(funn, stmt'::stmts, scope_list')] /\
LENGTH scope_list = LENGTH scope_list' /\ status' = status_running
Proof
rpt gen_tac >> rpt disch_tac >>
Cases_on ‘n’ >> (
 gs[stmt_multi_exec'_def, stmt_multi_exec'_check_state_def]
) >- (
 metis_tac[]
) >>
Cases_on ‘stmt_multi_exec' ctx
             (ascope,[g_scope1; g_scope2],[(funn,stmt::stmts,scope_list)],
              status_running) n'’ >> (
 gs[]
) >>
Cases_on ‘stmt_exec ctx x’ >> (
 gs[]
) >>
PairCases_on ‘x'’ >>
Cases_on ‘x'1’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘t’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘t'’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘x'2’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘t’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
PairCases_on ‘h''’ >>
Cases_on ‘x'3’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘h''1’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘h''0’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >> (
 metis_tac[]
)
QED

Theorem stmt_multi_exec'_imp_NONE:
!ctx stmts ascope g_scope_list frame_list n status.
(status <> status_running \/ LENGTH g_scope_list <> 2 \/
 ~(?funn stmt stmts scope_list.
  frame_list = [(funn,stmt::stmts,scope_list)])) ==>
stmt_multi_exec' (ctx:'a ctx) ((ascope, g_scope_list, frame_list, status):'a state) n = NONE
Proof
rpt strip_tac >> (
 Cases_on ‘n’ >> (
   gs[stmt_multi_exec'_def, stmt_multi_exec'_check_state_def]
 ) >- (
  metis_tac[stmt_multi_exec'_check_state_NONE]
 ) >>
 Cases_on ‘stmt_multi_exec' ctx (ascope,g_scope_list,frame_list,status) n'’ >> (
  gs[]
 ) >>
 Cases_on ‘stmt_exec ctx x’ >> (
  gs[]
 ) >>
 PairCases_on ‘x'’ >>
 metis_tac[stmt_multi_exec'_check_state_NONE]
)
QED

Theorem bigstep_stmt_ass_exec_sound_n_not_v:
!n ctx g_scope1 g_scope2 top_scope scope_list ascope funn l e e'.
~is_v e' ==>
e_multi_exec' (ctx:'a ctx) [g_scope1; g_scope2] (top_scope::scope_list) e n = SOME e' ==>
stmt_multi_exec' (ctx:'a ctx)
 (ascope, [g_scope1; g_scope2],
  [(funn, [stmt_ass l e], (top_scope::scope_list))], status_running) n =
 SOME (ascope, [g_scope1; g_scope2],
       [(funn, [stmt_ass l e'], (top_scope::scope_list))],
       status_running)
Proof
Induct_on ‘n’ >- (
 rpt strip_tac >>
 gs[e_multi_exec'_def, stmt_multi_exec'_def, stmt_multi_exec'_check_state_def]
) >>
rpt strip_tac >>
gs[e_multi_exec'_def, stmt_multi_exec'_def] >>
Cases_on ‘e_multi_exec' ctx [g_scope1; g_scope2] (top_scope::scope_list) e n’ >> (
 gs[]
) >>
Cases_on ‘e_exec ctx [g_scope1; g_scope2] (top_scope::scope_list) x’ >> (
 gs[]
) >>
PairCases_on ‘x'’ >>
gs[] >>
Cases_on ‘x'1’ >> (
 gs[]
) >>
gvs[] >>
subgoal ‘~is_v x’ >- (
 imp_res_tac e_exec_not_v
) >>
res_tac >>
fs[stmt_exec_def, stmt_multi_exec'_check_state_def]
QED

Theorem separate_SOME_imp:
!scope_list g_scope_list' scope_list'.
separate scope_list = (SOME g_scope_list',SOME scope_list') ==>
LENGTH scope_list > 2 ==>
?g_scope1' g_scope2'. g_scope_list' = [g_scope1'; g_scope2'] /\
LENGTH scope_list' = (LENGTH scope_list - 2)
Proof
rpt strip_tac >>
subgoal ‘?scope_list_rev. scope_list = REVERSE scope_list_rev’ >- (
 qexists_tac ‘REVERSE scope_list’ >>
 gs[]
) >>
gs[separate_def] >>
Cases_on ‘scope_list_rev’ >> (
 gs[]
) >>
Cases_on ‘t’ >> (
 gs[]
) >>
gs[SUC_ADD_ONE, APPEND] >>
subgoal ‘LENGTH t' = LENGTH (REVERSE t')’ >- (
 gs[]
) >>
FULL_SIMP_TAC pure_ss [GSYM APPEND_ASSOC] >>
FULL_SIMP_TAC pure_ss [oDROP_APPEND, oTAKE_APPEND] >>
qexistsl_tac [‘h'’, ‘h’] >>
fs[LENGTH_REVERSE] >>
gvs[]
QED

Theorem separate_LENGTH_SOME:
!scope_list.
LENGTH scope_list > 2 ==>
?g_scope1' g_scope2' top_scope scope_list'.
separate scope_list = (SOME [g_scope1'; g_scope2'],SOME (top_scope::scope_list'))
Proof
Induct >> (
 gs[]
) >>
rpt strip_tac >>
Cases_on ‘LENGTH scope_list = 2’ >- (
 gs[] >>
 subgoal ‘?e1 e2. scope_list = [e1; e2]’ >- (
  Cases_on ‘scope_list’ >> (
   gs[]
  ) >>
  Cases_on ‘t’ >> (
   gs[]
  )
 ) >>
 qexistsl_tac [‘e1’, ‘e2’, ‘h’, ‘[]’] >>
 gs[separate_def] >>
 FULL_SIMP_TAC pure_ss [Once arithmeticTheory.ONE, oDROP_def] >>
 FULL_SIMP_TAC pure_ss [Once arithmeticTheory.ONE, oTAKE_def] >>
 gs[]
) >>
gs[] >>
FULL_SIMP_TAC pure_ss [separate_def, Once arithmeticTheory.ONE, oDROP_def, oTAKE_def] >>
subgoal ‘?i. i > 2 /\ i = LENGTH scope_list’ >- (
 gs[]
) >>
gs[] >>
qexistsl_tac [‘g_scope1'’, ‘g_scope2'’, ‘h’, ‘(top_scope::scope_list')’] >>
gs[] >>
Q.SUBGOAL_THEN ‘SUC (LENGTH scope_list) − 2 = SUC ((LENGTH scope_list) − 2)’ (fn thm => FULL_SIMP_TAC pure_ss [thm]) >- (
 decide_tac
) >>
gs[oDROP_def, oTAKE_def]
QED

Theorem bigstep_stmt_ass_exec_sound_n_v:
!n ctx g_scope1 g_scope2 top_scope scope_list ascope funn lval e e' scope_list'' g_scope1' g_scope2' scope_list'.
is_v e' ==>
e_multi_exec' (ctx:'a ctx) [g_scope1; g_scope2] (top_scope::scope_list) e n = SOME e' ==>
stmt_exec_ass lval e' ((top_scope::scope_list)++[g_scope1; g_scope2]) = SOME scope_list'' ==>
separate scope_list'' = (SOME [g_scope1'; g_scope2'], SOME scope_list') ==>
stmt_multi_exec' (ctx:'a ctx)
 (ascope, [g_scope1; g_scope2],
  [(funn, [stmt_ass lval e], (top_scope::scope_list))], status_running) (SUC n) =
 SOME (ascope, [g_scope1'; g_scope2'],
       [(funn, [stmt_empty], scope_list')],
       status_running)
Proof
Induct_on ‘n’ >- (
 rpt strip_tac >>
 gs[stmt_multi_exec'_def, e_multi_exec'_def] >>
 Cases_on ‘e'’ >> (
  gvs[stmt_exec_def, is_v_def, stmt_multi_exec'_check_state_def]
 ) >>
 gs[stmt_exec_ass_def] >>
 imp_res_tac assign_LENGTH >>
 imp_res_tac separate_SOME_imp >>
 gs[]
) >>
rpt strip_tac >>
gs[e_multi_exec'_def, stmt_multi_exec'_def] >>
Cases_on ‘e_multi_exec' ctx [g_scope1; g_scope2] (top_scope::scope_list) e n’ >> (
 gs[]
) >>
Cases_on ‘e_exec ctx [g_scope1; g_scope2] (top_scope::scope_list) x’ >> (
 gs[]
) >>
PairCases_on ‘x'’ >>
gs[] >>
Cases_on ‘x'1’ >> (
 gs[]
) >>
subgoal ‘~is_v x’ >- (
 rpt strip_tac >>
 Cases_on ‘x’ >> (
  gs[is_v_def, e_exec_def]
 )
) >>
imp_res_tac bigstep_stmt_ass_exec_sound_n_not_v >>
gs[stmt_exec_def, stmt_multi_exec'_check_state_def] >>
Cases_on ‘e'’ >> (
 gs[is_v_def]
) >>
gs[stmt_exec_ass_def] >>
imp_res_tac assign_LENGTH >>
imp_res_tac separate_SOME_imp >>
gs[]
QED

Theorem scope_lists_separate:
!scope_lists top_scope scope_list scope_list' g_scope_list' g_scope_list''.
scope_lists = top_scope::(scope_list ++ g_scope_list') ==>
LENGTH g_scope_list' = 2 ==>
separate scope_lists = (SOME g_scope_list'',SOME scope_list') ==>
g_scope_list' = g_scope_list'' /\ top_scope::scope_list = scope_list'
Proof
rpt gen_tac >> rpt disch_tac >>
rpt strip_tac >> (
 rw[]
) >>
gs[separate_def] >>
gs[arithmeticTheory.ADD_SUC] >>
FULL_SIMP_TAC pure_ss [GSYM SUC_ADD_ONE] >>
gs[oDROP_def, oTAKE_def, oDROP_APPEND, oTAKE_APPEND]
QED

(*
Theorem bigstep_stmt_ass_exec_sound_n_call:
!top_scope scope_list g_scope1 g_scope2 funn funn' lval e_l e_l' n (ctx:'a ctx) ascope.
bigstep_f_arg_exec (NONE:(func_map # b_func_map # 'a ext_map) option) (top_scope::(scope_list ++ [g_scope1; g_scope2])) (funn',e_l) 0 = SOME (e_l', n) ==>
stmt_multi_exec' ctx
 (ascope, [g_scope1; g_scope2], [(funn,[stmt_ass lval (e_call funn' e_l)],top_scope::scope_list)],status_running) n =
  SOME (ascope, [g_scope1; g_scope2], [(funn,[stmt_ass lval (e_call funn' e_l')], top_scope::scope_list)], status_running)
Proof
Induct_on ‘n’ >> (
 rpt strip_tac >>
 gs[stmt_multi_exec'_def, bigstep_f_arg_exec_def, stmt_multi_exec'_check_state_def]
)
QED
*)

Theorem bigstep_stmt_cond_exec_sound_n:
!n ctx g_scope1 g_scope2 top_scope scope_list ascope funn stmt1 stmt2 e e'.
e_multi_exec' (ctx:'a ctx) [g_scope1; g_scope2] (top_scope::scope_list) e n = SOME e' ==>
stmt_multi_exec' (ctx:'a ctx)
 (ascope, [g_scope1; g_scope2],
  [(funn, [stmt_cond e stmt1 stmt2], (top_scope::scope_list))], status_running) n =
 SOME (ascope, [g_scope1; g_scope2],
       [(funn, [stmt_cond e' stmt1 stmt2], (top_scope::scope_list))],
       status_running)
Proof
Induct_on ‘n’ >- (
 rpt strip_tac >>
 gs[e_multi_exec'_def, stmt_multi_exec'_def, stmt_multi_exec'_check_state_def]
) >>
rpt strip_tac >>
gs[e_multi_exec'_def, stmt_multi_exec'_def] >>
Cases_on ‘e_multi_exec' ctx [g_scope1; g_scope2] (top_scope::scope_list) e n’ >> (
 gs[]
) >>
Cases_on ‘e_exec ctx [g_scope1; g_scope2] (top_scope::scope_list) x’ >> (
 gs[]
) >>
PairCases_on ‘x'’ >>
gs[] >>
Cases_on ‘x'1’ >> (
 gs[]
) >>
gvs[] >>
res_tac >>
fs[] >>
Cases_on ‘stmt_exec ctx
             (ascope,[g_scope1; g_scope2],
              [(funn,[stmt_cond x stmt1 stmt2],top_scope::scope_list)],
              status_running)’ >> (
 gs[]
) >- (
 gs[stmt_exec_def, stmt_multi_exec'_check_state_def] >>
 Cases_on ‘is_v_bool x’ >> (
  gs[]
 ) >>
 Cases_on ‘x’ >> (
  gs[is_v_bool_def]
 ) >>
 Cases_on ‘v’ >> (
  gs[is_v_bool_def]
 ) >>
 Cases_on ‘b’ >> (
  gs[stmt_exec_cond_def]
 )
) >>
subgoal ‘~is_v x’ >- (
 Cases_on ‘x’ >> (
  gs[is_v_def, e_exec_def]
 )
) >>
gs[stmt_exec_def] >>
subgoal ‘~is_v_bool x’ >- (
 Cases_on ‘x’ >> (
  gs[is_v_def, is_v_bool_def]
 )
) >>
gvs[stmt_multi_exec'_check_state_def]
QED

Theorem bigstep_stmt_ret_exec_sound_n:
!n ctx g_scope1 g_scope2 top_scope scope_list ascope funn e e'.
e_multi_exec' (ctx:'a ctx) [g_scope1; g_scope2] (top_scope::scope_list) e n = SOME e' ==>
stmt_multi_exec' (ctx:'a ctx)
 (ascope, [g_scope1; g_scope2],
  [(funn, [stmt_ret e], (top_scope::scope_list))], status_running) n =
 SOME (ascope, [g_scope1; g_scope2],
       [(funn, [stmt_ret e'], (top_scope::scope_list))],
       status_running)
Proof
Induct_on ‘n’ >- (
 rpt strip_tac >>
 gs[e_multi_exec'_def, stmt_multi_exec'_def, stmt_multi_exec'_check_state_def]
) >>
rpt strip_tac >>
gs[e_multi_exec'_def, stmt_multi_exec'_def] >>
Cases_on ‘e_multi_exec' ctx [g_scope1; g_scope2] (top_scope::scope_list) e n’ >> (
 gs[]
) >>
Cases_on ‘e_exec ctx [g_scope1; g_scope2] (top_scope::scope_list) x’ >> (
 gs[]
) >>
PairCases_on ‘x'’ >>
gs[] >>
Cases_on ‘x'1’ >> (
 gs[]
) >>
gvs[] >>
res_tac >>
fs[] >>
Cases_on ‘stmt_exec ctx
             (ascope,[g_scope1; g_scope2],
              [(funn,[stmt_ret x],top_scope::scope_list)],
              status_running)’ >> (
 gs[]
) >- (
 gs[stmt_exec_def, stmt_multi_exec'_check_state_def] >>
 Cases_on ‘get_v x’ >> (
  gs[]
 )
) >>
subgoal ‘~is_v x’ >- (
 Cases_on ‘x’ >> (
  gs[is_v_def, e_exec_def]
 )
) >>
gs[stmt_exec_def] >>
subgoal ‘get_v x = NONE’ >- (
 Cases_on ‘x’ >> (
  gs[is_v_def, get_v_def]
 )
) >>
gvs[stmt_multi_exec'_check_state_def]
QED

Theorem bigstep_stmt_seq_exec_sound_n_second:
!n ctx g_scope1 g_scope2 top_scope scope_list g_scope_list' scope_list' ascope funn stmt stmt' stmt''.
stmt_multi_exec' ctx
            (ascope,[g_scope1; g_scope2],
             [(funn,[stmt'],top_scope::scope_list)],status_running) n =
          SOME
            (ascope,g_scope_list',[(funn,[stmt''],scope_list')],status_running) ==>
is_empty stmt ==>
stmt_multi_exec' (ctx:'a ctx)
 (ascope, [g_scope1; g_scope2],
  [(funn, [stmt_seq stmt stmt'], (top_scope::scope_list))], status_running) (SUC n) =
 SOME (ascope, g_scope_list',
       [(funn, [stmt''], scope_list')],
       status_running)
Proof
Induct_on ‘n’ >> (
 rpt strip_tac >>
 gs[stmt_multi_exec'_def, stmt_multi_exec'_check_state_def] >>
 Cases_on ‘stmt’ >> (
  gvs[is_empty_def]
 ) >>
 gs[stmt_exec_def, is_empty_def, stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘stmt_multi_exec' ctx
            (ascope,[g_scope1; g_scope2],
             [(funn,[stmt'],top_scope::scope_list)],status_running) n’ >> (
 gs[]
) >>
Cases_on ‘stmt_exec ctx x’ >> (
 gs[]
) >>
imp_res_tac stmt_multi_exec'_check_state_second >>
gvs[stmt_multi_exec'_check_state_def] >>
PairCases_on ‘x’ >>
imp_res_tac stmt_multi_exec'_SOME_imp >>
gs[] >>
res_tac >>
qpat_x_assum ‘!stmt'4'. _’ (fn thm => ASSUME_TAC (Q.SPEC ‘stmt_empty’ thm)) >>
fs[is_empty_def, stmt_multi_exec'_check_state_def]
QED

Theorem stmt_multi_exec'_check_state_SOME:
!state1 state2 state3.
stmt_multi_exec'_check_state state1 state2 = SOME state3 ==>
state3 = state2
Proof
rpt strip_tac >>
(* Cases of state1 *)
PairCases_on ‘state1’ >>
Cases_on ‘state11’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘t’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘t'’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘state12’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘t’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
PairCases_on ‘h''’ >>
Cases_on ‘state13’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘h''1’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
(* Cases of state2 *)
PairCases_on ‘state2’ >>
Cases_on ‘state21’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘t'’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘t''’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘state22’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘t'’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
PairCases_on ‘h'5'’ >>
Cases_on ‘state23’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘h'''''1’ >> (
 gs[stmt_multi_exec'_check_state_def]
)
QED

Theorem stmt_multi_exec'_check_state_id:
!state1 state2 state3.
stmt_multi_exec'_check_state state1 state2 = SOME state3 ==>
stmt_multi_exec'_check_state state3 state3 = SOME state3
Proof
rpt strip_tac >>
(* Cases of state1 *)
PairCases_on ‘state1’ >>
Cases_on ‘state11’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘t’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘t'’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘state12’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘t’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
PairCases_on ‘h''’ >>
Cases_on ‘state13’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘h''1’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
(* Cases of state2 *)
PairCases_on ‘state2’ >>
Cases_on ‘state21’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘t'’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘t''’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘state22’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘t'’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
PairCases_on ‘h'5'’ >>
Cases_on ‘state23’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘h'''''1’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
gvs[stmt_multi_exec'_check_state_def]
QED

(* TODO: Merge with stmt_multi_exec'_check_state_SOME? *)
Theorem stmt_multi_exec'_check_state_imp:
!st1 st2 st3 st4 st'1 st'2 st'3 st'4.
stmt_multi_exec'_check_state (st1, st2, st3, st4) (st'1, st'2, st'3, st'4) = SOME (st'1, st'2, st'3, st'4) ==>
st1 = st'1 /\ st4 = status_running /\ st'4 = status_running /\
LENGTH st2 = 2 /\ LENGTH st'2 = 2 /\
?funn stmt stmt' stmts scope_list scope_list'.
 st3 = [(funn,stmt::stmts,scope_list)] /\
 st'3 = [(funn,stmt'::stmts,scope_list')] /\ LENGTH scope_list = LENGTH scope_list'
Proof
rpt strip_tac >> (
 (* Cases of st1 *)
 Cases_on ‘st2’ >> (
  gs[stmt_multi_exec'_check_state_def]
 ) >>
 Cases_on ‘t’ >> (
  gs[stmt_multi_exec'_check_state_def]
 ) >>
 Cases_on ‘t'’ >> (
  gs[stmt_multi_exec'_check_state_def]
 ) >>
 Cases_on ‘st3’ >> (
  gs[stmt_multi_exec'_check_state_def]
 ) >>
 Cases_on ‘t’ >> (
  gs[stmt_multi_exec'_check_state_def]
 ) >>
 PairCases_on ‘h''’ >>
 Cases_on ‘st4’ >> (
  gs[stmt_multi_exec'_check_state_def]
 ) >>
 Cases_on ‘h''1’ >> (
  gs[stmt_multi_exec'_check_state_def]
 ) >>
 (* Cases of st2 *)
 Cases_on ‘st'2’ >> (
  gs[stmt_multi_exec'_check_state_def]
 ) >>
 Cases_on ‘t'’ >> (
  gs[stmt_multi_exec'_check_state_def]
 ) >>
 Cases_on ‘t''’ >> (
  gs[stmt_multi_exec'_check_state_def]
 ) >>
 Cases_on ‘st'3’ >> (
  gs[stmt_multi_exec'_check_state_def]
 ) >>
 Cases_on ‘t'’ >> (
  gs[stmt_multi_exec'_check_state_def]
 ) >>
 PairCases_on ‘h'5'’ >>
 Cases_on ‘st'4’ >> (
  gs[stmt_multi_exec'_check_state_def]
 ) >>
 Cases_on ‘h'''''1’ >> (
  gs[stmt_multi_exec'_check_state_def]
 )
)
QED

Theorem stmt_multi_exec'_hd_tl:
!m ctx x0 x1 x2 x3.
(case stmt_multi_exec' ctx (x0,x1,x2,x3) m of
   NONE => NONE
 | SOME state' =>
   case stmt_exec ctx state' of
     NONE => NONE
   | SOME state'' =>
     stmt_multi_exec'_check_state (x0,x1,x2,x3) state'') =
case
  case stmt_multi_exec'_check_state (x0,x1,x2,x3) (x0,x1,x2,x3) of
    NONE => NONE
  | SOME state' =>
    case stmt_exec ctx state' of
      NONE => NONE
    | SOME state'' =>
      stmt_multi_exec'_check_state (x0,x1,x2,x3) state''
of
  NONE => NONE
| SOME (ascope',g_scope_list',frame_list',status') =>
  stmt_multi_exec' ctx (ascope',g_scope_list',frame_list',status') m
Proof
Induct_on ‘m’ >- (
 rpt strip_tac >>
 gs [stmt_multi_exec'_def, stmt_multi_exec'_check_state_def] >>
 Cases_on ‘stmt_multi_exec'_check_state (x0,x1,x2,x3) (x0,x1,x2,x3)’ >> (
  gs[]
 ) >>
 Cases_on ‘stmt_exec ctx x’ >> (
  gs[]
 ) >>
 Cases_on ‘stmt_multi_exec'_check_state (x0,x1,x2,x3) x'’ >> (
  gs[]
 ) >>
 PairCases_on ‘x''’ >>
 gs[] >>
 imp_res_tac stmt_multi_exec'_check_state_id >>
 gs[]
) >>
rpt strip_tac >>
gs[stmt_multi_exec'_def, stmt_multi_exec'_check_state_def] >>
Cases_on ‘stmt_multi_exec'_check_state (x0,x1,x2,x3) (x0,x1,x2,x3)’ >> (
 gs[]
) >>
Cases_on ‘stmt_exec ctx x’ >> (
 gs[]
) >>
Cases_on ‘stmt_multi_exec'_check_state (x0,x1,x2,x3) x'’ >> (
 gs[]
) >>
PairCases_on ‘x''’ >>
gs[] >>
qpat_x_assum ‘!ctx. _’ (fn thm => ASSUME_TAC (GSYM thm)) >>
gs[] >>
Cases_on ‘stmt_multi_exec' ctx (x''0,x''1,x''2,x''3) m’ >> (
 gs[]
) >>
Cases_on ‘stmt_exec ctx x''’ >> (
 gs[]
) >>
PairCases_on ‘x'3'’ >>
subgoal ‘x0 = x''0 /\ x3 = status_running /\ x''3 = status_running /\
         LENGTH x1 = 2 /\ LENGTH x''1 = 2 /\
         ?funn stmt stmt' stmts scope_list scope_list'.
         x2 = [(funn,stmt::stmts,scope_list)] /\
         x''2 = [(funn,stmt'::stmts,scope_list')] /\ LENGTH scope_list = LENGTH scope_list'’ >- (
 imp_res_tac stmt_multi_exec'_check_state_SOME >>
 gvs[] >>
 imp_res_tac stmt_multi_exec'_check_state_imp >>
 gvs[]
) >>
gs[] >>
Cases_on ‘x1’ >> (
 gs[]
) >>
Cases_on ‘t’ >> (
 gs[]
) >>
Cases_on ‘x''1’ >> (
 gs[]
) >>
Cases_on ‘t’ >> (
 gs[]
) >>
(* TODO: Split out into lemma... *)
gvs [stmt_multi_exec'_check_state_def] >>
Cases_on ‘x'''1’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘t’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘t'’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘x'''2’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘t’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
PairCases_on ‘h'6'’ >>
Cases_on ‘x'''3’ >> (
 gs[stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘h''''''1’ >> (
 gs[stmt_multi_exec'_check_state_def]
)
QED

Triviality stmt_multi_exec'_NONE_status:
!ctx n ascope g_scope_list frame_list status.
status <> status_running ==>
stmt_multi_exec' ctx (ascope,g_scope_list,frame_list,status) n = NONE
Proof
metis_tac[stmt_multi_exec'_imp_NONE]
QED

Triviality stmt_multi_exec'_NONE_g_scope_list:
!ctx n ascope g_scope_list frame_list status.
LENGTH g_scope_list <> 2 ==>
stmt_multi_exec' ctx (ascope,g_scope_list,frame_list,status) n = NONE
Proof
metis_tac[stmt_multi_exec'_imp_NONE]
QED

Triviality stmt_multi_exec'_NONE_frame_list:
!ctx n ascope g_scope_list frame_list status.
~(?funn stmt stmts scope_list.
  frame_list = [(funn,stmt::stmts,scope_list)]) ==>
stmt_multi_exec' ctx (ascope,g_scope_list,frame_list,status) n = NONE
Proof
metis_tac[stmt_multi_exec'_imp_NONE]
QED

Theorem stmt_multi_exec'_add:
!ctx ascope g_scope_list frame_list status m n.
stmt_multi_exec' ctx (ascope, g_scope_list, frame_list, status) (m+n) =
 case stmt_multi_exec' ctx (ascope, g_scope_list, frame_list, status) n of
 | SOME (ascope', g_scope_list', frame_list', status') =>
  stmt_multi_exec' ctx (ascope', g_scope_list', frame_list', status') m
 | NONE => NONE
Proof
Induct_on ‘n’ >- (
 rpt strip_tac >>
 gs [stmt_multi_exec'_def, stmt_multi_exec'_check_state_def] >>
 Cases_on ‘stmt_multi_exec'_check_state (ascope,g_scope_list,frame_list,status)
            (ascope,g_scope_list,frame_list,status)’ >> (
  gs[]
 ) >- (
  imp_res_tac stmt_multi_exec'_check_state_eq_NONE >- (
   gs[stmt_multi_exec'_NONE_status]
  ) >- (
   gs[stmt_multi_exec'_NONE_g_scope_list]
  ) >>
  gs[stmt_multi_exec'_NONE_frame_list]
 ) >>
 PairCases_on ‘x’ >>
 gs[] >>
 metis_tac[stmt_multi_exec'_check_state_SOME]
) >>
rpt strip_tac >>
Q.SUBGOAL_THEN ‘m + SUC n = SUC m + n’ (fn thm => REWRITE_TAC [thm]) >- (
 decide_tac
) >>
gs[] >>
Q.SUBGOAL_THEN ‘SUC n = 1 + n’ (fn thm => REWRITE_TAC [thm]) >- (
 decide_tac
) >>
gs[] >>
REWRITE_TAC [Once arithmeticTheory.ONE] >>
gs [stmt_multi_exec'_def, stmt_multi_exec'_check_state_def, arithmeticTheory.ADD_CLAUSES] >>
Cases_on ‘stmt_multi_exec' ctx (ascope,g_scope_list,frame_list,status) n’ >> (
 gs[]
) >>
PairCases_on ‘x’ >>
(* Boils down to proving order m,1 and 1,m equivalence *)
gs[stmt_multi_exec'_hd_tl]
QED

Theorem bigstep_stmt_seq_exec_sound_n_first:
!n ctx g_scope1 g_scope2 top_scope scope_list g_scope_list' scope_list' ascope funn stmt stmt' stmt''.
stmt_multi_exec' ctx
            (ascope,[g_scope1; g_scope2],
             [(funn,[stmt],top_scope::scope_list)],status_running) n =
          SOME
            (ascope,g_scope_list',[(funn,[stmt''],scope_list')],status_running) ==>
stmt_multi_exec' (ctx:'a ctx)
 (ascope, [g_scope1; g_scope2],
  [(funn, [stmt_seq stmt stmt'], (top_scope::scope_list))], status_running) n =
 SOME (ascope, g_scope_list',
       [(funn, [stmt_seq stmt'' stmt'], scope_list')],
       status_running)
Proof
Induct_on ‘n’ >> (
 rpt strip_tac >>
 gs[stmt_multi_exec'_def, stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘stmt_multi_exec' ctx
            (ascope,[g_scope1; g_scope2],
             [(funn,[stmt],top_scope::scope_list)],status_running) n’ >> (
 gs[]
) >>
Cases_on ‘stmt_exec ctx x’ >> (
 gs[]
) >>
imp_res_tac stmt_multi_exec'_check_state_second >>
gvs[stmt_multi_exec'_check_state_def] >>
PairCases_on ‘x’ >>
imp_res_tac stmt_multi_exec'_SOME_imp >>
gs[] >>
res_tac >>
qpat_x_assum ‘!stmt'. _’ (fn thm => ASSUME_TAC (Q.SPEC ‘stmt'’ thm)) >>
fs[] >>
Cases_on ‘scope_list''’ >> (
 gs[stmt_exec_def]
) >>
Cases_on ‘stmt'3'’ >> (
 gvs[is_empty_def, stmt_exec_def, stmt_multi_exec'_check_state_def]
)
QED

Theorem stmt_multi_exec'_comp_n_tl:
!ctx ascope g_scope_list frame_list status n m ascope' g_scope_list' frame_list' status' ascope'' g_scope_list'' frame_list'' status''.
stmt_multi_exec' ctx (ascope, g_scope_list, frame_list, status) n =
  SOME (ascope', g_scope_list', frame_list', status') ==>
stmt_multi_exec' ctx (ascope', g_scope_list', frame_list', status') m =
  SOME (ascope'', g_scope_list'', frame_list'', status'') ==>
stmt_multi_exec' ctx (ascope, g_scope_list, frame_list, status) (n+m) =
  SOME (ascope'', g_scope_list'', frame_list'', status'')
Proof
rpt strip_tac >>
FULL_SIMP_TAC pure_ss [Once arithmeticTheory.ADD_COMM] >>
gs[stmt_multi_exec'_add]
QED

Theorem bigstep_stmt_seq_exec_sound_n_both:
!n n' n'' ctx g_scope1 g_scope2 top_scope scope_list g_scope_list' g_scope_list'' scope_list' scope_list'' ascope funn stmt stmt' stmt'' stmt'''.
stmt_multi_exec' ctx
            (ascope,[g_scope1; g_scope2],
             [(funn,[stmt],top_scope::scope_list)],status_running) n =
          SOME
            (ascope,g_scope_list',[(funn,[stmt''],scope_list')],status_running) ==>
stmt_multi_exec' ctx
            (ascope,g_scope_list',
             [(funn,[stmt'],scope_list')],status_running) n' =
          SOME
            (ascope,g_scope_list'',[(funn,[stmt'''],scope_list'')],status_running) ==>
is_empty stmt'' ==>
n'' = n+n' ==>
stmt_multi_exec' (ctx:'a ctx)
 (ascope, [g_scope1; g_scope2],
  [(funn, [stmt_seq stmt stmt'], (top_scope::scope_list))], status_running) (SUC n'') =
 SOME (ascope, g_scope_list'',
       [(funn, [stmt'''], scope_list'')],
       status_running)
Proof
rpt strip_tac >>
Cases_on ‘scope_list'’ >- (
 imp_res_tac stmt_multi_exec'_SOME_imp >>
 gvs[]
) >>
subgoal ‘?g_scope1' g_scope2'. g_scope_list' = [g_scope1'; g_scope2']’ >- (
 imp_res_tac stmt_multi_exec'_SOME_imp >>
 gvs[]
) >>
gvs[] >>
subgoal ‘stmt_multi_exec' ctx
          (ascope,[g_scope1'; g_scope2'],
           [(funn,[stmt_seq stmt'' stmt'],h::t)],status_running) (SUC n') =
        SOME
          (ascope,g_scope_list'',[(funn,[stmt'³'],scope_list'')],
           status_running)’ >- (
 imp_res_tac bigstep_stmt_seq_exec_sound_n_second
) >>
subgoal ‘stmt_multi_exec' ctx
          (ascope,[g_scope1; g_scope2],
           [(funn,[stmt_seq stmt stmt'],top_scope::scope_list)],
           status_running) n =
        SOME
          (ascope,[g_scope1'; g_scope2'],[(funn,[stmt_seq stmt'' stmt'],h::t)],
           status_running)’ >- (
 irule bigstep_stmt_seq_exec_sound_n_first >>
 gs[]
) >>
Q.SUBGOAL_THEN ‘SUC (n + n') = n + SUC n'’ (fn thm => REWRITE_TAC [thm]) >- (
 decide_tac
) >>
irule stmt_multi_exec'_comp_n_tl >>
qexistsl_tac [‘ascope’, ‘[(funn,[stmt_seq stmt'' stmt'],h::t)]’, ‘[g_scope1'; g_scope2']’, ‘status_running’] >>
gs[]
QED

Theorem bigstep_stmt_trans_exec_sound_n:
!n ctx g_scope1 g_scope2 top_scope scope_list ascope funn e e'.
e_multi_exec' (ctx:'a ctx) [g_scope1; g_scope2] (top_scope::scope_list) e n = SOME e' ==>
stmt_multi_exec' (ctx:'a ctx)
 (ascope, [g_scope1; g_scope2],
  [(funn, [stmt_trans e], (top_scope::scope_list))], status_running) n =
 SOME (ascope, [g_scope1; g_scope2],
       [(funn, [stmt_trans e'], (top_scope::scope_list))],
       status_running)
Proof
Induct_on ‘n’ >- (
 rpt strip_tac >>
 gs[e_multi_exec'_def, stmt_multi_exec'_def, stmt_multi_exec'_check_state_def]
) >>
rpt strip_tac >>
gs[e_multi_exec'_def, stmt_multi_exec'_def] >>
Cases_on ‘e_multi_exec' ctx [g_scope1; g_scope2] (top_scope::scope_list) e n’ >> (
 gs[]
) >>
Cases_on ‘e_exec ctx [g_scope1; g_scope2] (top_scope::scope_list) x’ >> (
 gs[]
) >>
PairCases_on ‘x'’ >>
gs[] >>
Cases_on ‘x'1’ >> (
 gs[]
) >>
gvs[] >>
res_tac >>
fs[] >>
subgoal ‘~is_v x’ >- (
 Cases_on ‘x’ >> (
  gs[is_v_def, e_exec_def]
 )
) >>
Cases_on ‘stmt_exec ctx
             (ascope,[g_scope1; g_scope2],
              [(funn,[stmt_trans x],top_scope::scope_list)],
              status_running)’ >> (
 gs[]
) >> (
 gvs[stmt_exec_def, stmt_multi_exec'_check_state_def]
)
QED

Theorem bigstep_stmt_app_exec_sound_n:
!n ctx g_scope1 g_scope2 top_scope scope_list ascope funn s e_l e_l'.
e_multi_exec'_list' (ctx:'a ctx) [g_scope1; g_scope2] (top_scope::scope_list) e_l n = SOME e_l' ==>
stmt_multi_exec' (ctx:'a ctx)
 (ascope, [g_scope1; g_scope2],
  [(funn, [stmt_app s e_l], (top_scope::scope_list))], status_running) n =
 SOME (ascope, [g_scope1; g_scope2],
       [(funn, [stmt_app s e_l'], (top_scope::scope_list))],
       status_running)
Proof
Induct_on ‘n’ >- (
 rpt strip_tac >>
 gs[e_multi_exec'_list'_def, stmt_multi_exec'_def, stmt_multi_exec'_check_state_def]
) >>
rpt strip_tac >>
gs[e_multi_exec'_list'_def, stmt_multi_exec'_def, stmt_multi_exec'_check_state_def] >>
Cases_on ‘e_l’ >- (
 (* ??? Disallow empty list? Check proof state where this is used...
  * Maybe write a wrapper for e_multi_exec'_list' that returns NONE for empty list... *)
 Cases_on ‘e_multi_exec'_list' ctx [g_scope1; g_scope2]
                (top_scope::scope_list) [] n’ >- (
  gs[]
 ) >>
 imp_res_tac e_multi_exec'_list'_LENGTH >>
 gs[unred_mem_index_def, unred_mem_def, INDEX_FIND_def]
) >>
gs[e_multi_exec'_list'_def] >>
Cases_on ‘e_multi_exec'_list' ctx [g_scope1; g_scope2]
             (top_scope::scope_list) (h::t) n’ >> (
 gs[]
) >>
Cases_on ‘unred_mem_index x’ >- (
 gs[]
) >>
gs[] >>
Cases_on ‘e_exec ctx [g_scope1; g_scope2] (top_scope::scope_list) (EL x' x)’ >> (
 gs[]
) >>
PairCases_on ‘x''’ >>
gs[] >>
Cases_on ‘x''1’ >> (
 gs[]
) >>
gvs[] >>
res_tac >>
PairCases_on ‘ctx’ >>
fs[stmt_exec_def] >>
(* Done, modulo some fiddling? *)
subgoal ‘index_not_const x = SOME x'’ >- (
 gs[index_not_const_def, unred_mem_index_def, unred_mem_def]
) >>
gs[e_multi_exec'_list'_def, stmt_multi_exec'_def, stmt_multi_exec'_check_state_def]
QED

Theorem stmt_exec_ass_LENGTH:
!lval e scope_lists scope_lists'.
stmt_exec_ass lval e scope_lists = SOME scope_lists' ==>
LENGTH scope_lists' = LENGTH scope_lists
Proof
rpt strip_tac >>
Cases_on ‘e’ >> (
 gs[stmt_exec_ass_def]
) >>
imp_res_tac assign_LENGTH
QED

Theorem bigstep_stmt_exec_imp:
!stmt stmt' scope_lists scope_lists' n m.
bigstep_stmt_exec (NONE:(func_map # b_func_map # 'a ext_map) option) scope_lists stmt n = SOME (stmt', scope_lists', m) ==>
((n <= m) /\
(n = m ==> (stmt = stmt' /\ scope_lists = scope_lists'))) /\ LENGTH scope_lists' = LENGTH scope_lists
Proof
Induct_on ‘stmt’ >> (
 rpt gen_tac >>
 rpt disch_tac
) >| [
 (* empty *)
 gs[bigstep_stmt_exec_def],

 (* assign *)
 gs[bigstep_stmt_exec_def] >>
 Cases_on ‘is_v e’ >> (
  gs[]
 ) >- (
  Cases_on ‘e’ >> (
   gs[is_v_def]
  ) >>
  gs[bigstep_e_exec_def, is_v_def] >>
  Cases_on ‘stmt_exec_ass l (e_v v) scope_lists’ >> (
   gs[]
  ) >>
  imp_res_tac stmt_exec_ass_LENGTH >>
  gs[]
 ) >>
 Cases_on ‘?funn' e_l. e = e_call funn e_l’ >> (
  gs[bigstep_f_arg_exec_def]
 ) >>
 Cases_on ‘bigstep_e_exec scope_lists (INL e) n’ >> (
  gs[]
 ) >- (
  Cases_on ‘e’ >> (
   gs[]
  )
 ) >>
 PairCases_on ‘x’ >>
 gs[] >>
 Cases_on ‘x0’ >> (
  gs[]
 ) >> (
  Cases_on ‘is_v x’ >> (
   gs[]
  ) >- (
   Cases_on ‘stmt_exec_ass l x scope_lists’ >> (
    gs[]
   ) >> (
    Cases_on ‘e’ >> (
     gs[]
    )
   ) >> (
    gvs[is_v_def] >>
    imp_res_tac bigstep_e_exec_incr >>
    imp_res_tac stmt_exec_ass_LENGTH >>
    decide_tac
   )
  ) >> (
   Cases_on ‘e’ >> (
    gs[]
   )
  ) >> (
   gvs[is_v_def] >>
   imp_res_tac bigstep_e_exec_incr >>
   imp_res_tac stmt_exec_ass_LENGTH >>
   gs[] >>
   Cases_on ‘n = m’ >> (
    gvs[]
   ) >>
   imp_res_tac bigstep_e_exec_unchanged >>
   gs[]
  )
 ) >>
 Cases_on ‘e’ >> (
  gs[]
 ),

 (* Conditional *)
 gs[bigstep_stmt_exec_def] >>
 Cases_on ‘is_v e’ >> (
  gs[]
 ) >- (
  Cases_on ‘e’ >> (
   gs[is_v_def]
  ) >>
  gs[bigstep_e_exec_def, is_v_def]
 ) >>
 Cases_on ‘?funn' e_l. e = e_call funn e_l’ >> (
  gs[bigstep_f_arg_exec_def]
 ) >>
 Cases_on ‘bigstep_e_exec scope_lists (INL e) n’ >> (
  gs[]
 ) >- (
  Cases_on ‘e’ >> (
   gs[]
  )
 ) >>
 PairCases_on ‘x’ >>
 gs[] >>
 Cases_on ‘x0’ >> (
  gs[]
 ) >- (
  Cases_on ‘e’ >> (
   gs[]
  ) >> (
   gvs[is_v_def] >>
   imp_res_tac bigstep_e_exec_incr
  ) >> (
   gs[] >>
   Cases_on ‘n = m’ >> (
    gvs[]
   ) >>
   imp_res_tac bigstep_e_exec_unchanged >>
   gs[]
  )
 ) >>
 Cases_on ‘e’ >> (
  gs[]
 ),
 
 (* block *)
 gs[bigstep_stmt_exec_def],

 (* return *)
 gs[bigstep_stmt_exec_def] >>
 Cases_on ‘get_v e <> NONE’ >> (
  gs[]
 ) >- (
  subgoal ‘?x. get_v e = SOME x’ >- (
   gs[GSYM quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE, optionTheory.IS_SOME_EXISTS]
  ) >>
  Cases_on ‘e’ >> (
   gs[get_v_def]
  ) >>
  gs[bigstep_stmt_exec_def, bigstep_e_exec_def]
 ) >>
 (* e reduction *)
 Cases_on ‘bigstep_e_exec scope_lists (INL e) n’ >> (
  gs[]
 ) >>
 PairCases_on ‘x’ >>
 gs[] >>
 Cases_on ‘x0’ >> (
  gs[]
 ) >>
 gvs[] >>
 imp_res_tac bigstep_e_exec_incr >>
 gs[] >>
 Cases_on ‘n = m’ >> (
  gvs[]
 ) >>
 imp_res_tac bigstep_e_exec_unchanged >>
 gs[],

 (* seq - sole recursive case *)
 gs[bigstep_stmt_exec_def] >>
 Cases_on ‘is_empty stmt’ >> (
  gs[] >>
  res_tac >>
  Cases_on ‘n +1 = m’ >> (
   gvs[]
  )
 ) >> (
  Cases_on ‘bigstep_stmt_exec (NONE:(func_map # b_func_map # 'a ext_map) option) scope_lists stmt n’ >> (
   gs[]
  ) >>
  PairCases_on ‘x’ >>
  gs[] >>
  Cases_on ‘is_empty x0’ >> (
   gs[]
  ) >- (
   res_tac >>
   fs[]
  ) >>
  res_tac >>
  fs[]
 ),

 (* transition *)
 gs[bigstep_stmt_exec_def] >>
 Cases_on ‘bigstep_e_exec scope_lists (INL e) n’ >> (
  gs[]
 ) >>
 PairCases_on ‘x’ >>
 gs[] >>
 Cases_on ‘x0’ >> (
  gs[]
 ) >>
 gvs[] >>
 imp_res_tac bigstep_e_exec_incr >>
 gs[] >>
 Cases_on ‘n = m’ >> (
  gvs[]
 ) >>
 imp_res_tac bigstep_e_exec_unchanged >>
 gs[],

 (* apply *)
 gs[bigstep_stmt_exec_def] >>
 Cases_on ‘bigstep_e_exec scope_lists (INR l) n’ >> (
  gs[]
 ) >>
 PairCases_on ‘x’ >>
 gs[] >>
 Cases_on ‘x0’ >> (
  gs[]
 ) >>
 imp_res_tac bigstep_e_exec_incr >>
 gs[] >>
 Cases_on ‘n = m’ >> (
  gvs[]
 ) >>
 imp_res_tac bigstep_e_exec_unchanged >>
 gs[],

 (* ext *)
 gs[bigstep_stmt_exec_def]
]
QED


Theorem bigstep_f_arg_exec_l_imp:
!d_e_l e_l' scope_lists n m.
bigstep_f_arg_exec_l scope_lists d_e_l n = SOME (e_l', m) ==>
((n <= m) /\ LENGTH d_e_l = LENGTH e_l' /\
(n = m ==> (MAP SND d_e_l = e_l')))
Proof
Induct_on ‘d_e_l’ >- (
 gs[bigstep_f_arg_exec_l_def]
) >>
rpt gen_tac >>
rpt disch_tac >>
gs[bigstep_f_arg_exec_l_def, AllCaseEqs()] >>
PairCases_on ‘h’ >>
gs[bigstep_f_arg_exec'_def, AllCaseEqs()] >- (
 res_tac >>
 gvs[] >>
 imp_res_tac bigstep_e_exec_incr >>
 gs[] >>
 disch_tac >>
 subgoal ‘n = n'’ >- (
  gs[]
 ) >>
 rw[] >>
 imp_res_tac bigstep_e_exec_unchanged >>
 fs[]
) >- (
 res_tac >>
 gvs[]
) >>
res_tac >>
gvs[]
QED


Theorem oZIP_lemma:
!l1 l2 l3.
oZIP (l1,l2) = SOME l3 ==>
MAP SND l3 = l2
Proof
Induct_on ‘l2’ >- (
 gs[oZIP_def] >>
 Cases_on ‘l1’ >> (
  gvs[oZIP_def, AllCaseEqs()]
 )
) >>
rpt strip_tac >>
Cases_on ‘l1’ >> (
 gvs[oZIP_def, AllCaseEqs()]
) >>
res_tac
QED

Theorem oZIP_lemma2:
!l1 l2.
oZIP (l1,l2) = SOME [] ==>
l1 = [] ∧ l2 = []
Proof
Induct_on ‘l2’ >- (
 gs[oZIP_def] >>
 Cases_on ‘l1’ >> (
  gvs[oZIP_def, AllCaseEqs()]
 )
) >>
rpt strip_tac >>
Cases_on ‘l1’ >> (
 gvs[oZIP_def, AllCaseEqs()]
)
QED

(* TODO: Merge with the above? *)
Theorem bigstep_stmt_exec_SOME_imp:
!func_map_b_func_map_ext_map_option stmt stmt' scope_lists scope_lists' n m.
bigstep_stmt_exec func_map_b_func_map_ext_map_option scope_lists stmt n = SOME (stmt', scope_lists', m) ==>
((n <= m) /\
(n = m ==> (stmt = stmt' /\ scope_lists = scope_lists'))) /\ LENGTH scope_lists' = LENGTH scope_lists
Proof
Induct_on ‘stmt’ >> (
 rpt gen_tac >>
 rpt disch_tac
) >| [
 (* empty *)
 gs[bigstep_stmt_exec_def],

 (* assign *)
 gs[bigstep_stmt_exec_def] >>
 Cases_on ‘is_v e’ >> (
  gs[]
 ) >- (
  Cases_on ‘e’ >> (
   gs[is_v_def]
  ) >>
  gs[bigstep_e_exec_def, is_v_def] >>
  Cases_on ‘stmt_exec_ass l (e_v v) scope_lists’ >> (
   gs[]
  ) >>
  imp_res_tac stmt_exec_ass_LENGTH >>
  gs[]
 ) >>
 Cases_on ‘?funn' e_l. e = e_call funn e_l’ >> (
  gs[bigstep_f_arg_exec_def] >>
  imp_res_tac bigstep_f_arg_exec_l_imp >>
  gvs[]
 ) >- (
  gs[AllCaseEqs()] >>
  imp_res_tac bigstep_f_arg_exec_l_imp >>
  gvs[] >>
  metis_tac[oZIP_lemma]
 ) >>
 Cases_on ‘bigstep_e_exec scope_lists (INL e) n’ >> (
  gs[]
 ) >- (
  Cases_on ‘e’ >> (
   gs[AllCaseEqs()]
  ) >>
  imp_res_tac bigstep_f_arg_exec_l_imp >>
  gvs[] >>
  metis_tac[oZIP_lemma]
 ) >>
 PairCases_on ‘x’ >>
 gs[] >>
 Cases_on ‘x0’ >> (
  gs[]
 ) >> (
  Cases_on ‘is_v x’ >> (
   gs[]
  ) >- (
   Cases_on ‘stmt_exec_ass l x scope_lists’ >> (
    gs[]
   ) >> (
    Cases_on ‘e’ >> (
     gs[AllCaseEqs()]
    )
   ) >> (
    gvs[is_v_def] >>
    imp_res_tac bigstep_e_exec_incr >>
    imp_res_tac stmt_exec_ass_LENGTH >>
    imp_res_tac bigstep_f_arg_exec_l_imp >>
    gs[] >>
    metis_tac[oZIP_lemma]
   )
  ) >> (
   Cases_on ‘e’ >> (
    gs[is_v_def] >>
    imp_res_tac bigstep_e_exec_incr >>
    imp_res_tac stmt_exec_ass_LENGTH >>
    gs[]
   )
  ) >> (
   gvs[is_v_def, AllCaseEqs()] >>
   imp_res_tac bigstep_e_exec_incr >>
   imp_res_tac stmt_exec_ass_LENGTH >>
   gs[] >>
   Cases_on ‘n = m’ >> (
    gvs[]
   ) >>
   imp_res_tac bigstep_e_exec_unchanged >>
   gs[]
  ) >- (
   imp_res_tac oZIP_lemma >>
   gvs[] >>
   imp_res_tac bigstep_f_arg_exec_l_imp >>
   metis_tac[]
  ) >>
  imp_res_tac oZIP_lemma >>
  gvs[] >>
  imp_res_tac bigstep_f_arg_exec_l_imp >>
  metis_tac[]
 ) >>
 Cases_on ‘e’ >> (
  gs[is_v_def] >>
  gvs[is_v_def, AllCaseEqs()] >>
  imp_res_tac bigstep_e_exec_incr >>
  imp_res_tac stmt_exec_ass_LENGTH >>
  gs[] >>
  Cases_on ‘n = m’ >> (
   gvs[]
  ) >>
  imp_res_tac bigstep_e_exec_unchanged >>
  gs[]
 ) >> (
  (* Fixed with oZIP lemma *)
  imp_res_tac oZIP_lemma >>
  gvs[] >>
  imp_res_tac bigstep_f_arg_exec_l_imp >>
  metis_tac[]
 ),

 (* Conditional *)
 gs[bigstep_stmt_exec_def] >>
 Cases_on ‘is_v e’ >> (
  gs[]
 ) >- (
  Cases_on ‘e’ >> (
   gs[is_v_def]
  ) >>
  gs[bigstep_e_exec_def, is_v_def]
 ) >>
 Cases_on ‘?funn' e_l. e = e_call funn e_l’ >> (
  gs[bigstep_f_arg_exec_def]
 ) >- (
  gvs[AllCaseEqs()] >>
  imp_res_tac oZIP_lemma >>
  imp_res_tac bigstep_f_arg_exec_l_imp >>
  metis_tac[]
 ) >>
 Cases_on ‘bigstep_e_exec scope_lists (INL e) n’ >> (
  gs[]
 ) >- (
  Cases_on ‘e’ >> (
   gs[AllCaseEqs()]
  ) >>
  imp_res_tac oZIP_lemma >>
  imp_res_tac bigstep_f_arg_exec_l_imp >>
  metis_tac[]
 ) >>
 PairCases_on ‘x’ >>
 gs[] >>
 Cases_on ‘x0’ >> (
  gs[]
 ) >- (
  Cases_on ‘e’ >> (
   gs[]
  ) >> (
   gvs[is_v_def] >>
   imp_res_tac bigstep_e_exec_incr
  ) >> (
   gs[AllCaseEqs()] >>
   Cases_on ‘n = m’ >> (
    gvs[]
   ) >>
   imp_res_tac bigstep_e_exec_unchanged >>
   gs[] >> (
    imp_res_tac oZIP_lemma >>
    imp_res_tac bigstep_f_arg_exec_l_imp >>
    metis_tac[]
   )
  )
 ) >>
 Cases_on ‘e’ >> (
  gs[AllCaseEqs()]
 ) >>
 imp_res_tac bigstep_f_arg_exec_l_imp >>
 gs[] >>
 imp_res_tac oZIP_lemma >>
 metis_tac[],
 
 (* block *)
 gs[bigstep_stmt_exec_def],

 (* return *)
 gs[bigstep_stmt_exec_def] >>
 Cases_on ‘get_v e <> NONE’ >> (
  gs[]
 ) >- (
  subgoal ‘?x. get_v e = SOME x’ >- (
   gs[GSYM quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE, optionTheory.IS_SOME_EXISTS]
  ) >>
  Cases_on ‘e’ >> (
   gs[get_v_def]
  ) >>
  gs[bigstep_stmt_exec_def, bigstep_e_exec_def]
 ) >>
 (* e reduction *)
 Cases_on ‘bigstep_e_exec scope_lists (INL e) n’ >> (
  gs[]
 ) >>
 PairCases_on ‘x’ >>
 gs[] >>
 Cases_on ‘x0’ >> (
  gs[]
 ) >>
 gvs[] >>
 imp_res_tac bigstep_e_exec_incr >>
 gs[] >>
 Cases_on ‘n = m’ >> (
  gvs[]
 ) >>
 imp_res_tac bigstep_e_exec_unchanged >>
 gs[],

 (* seq - sole recursive case *)
 gs[bigstep_stmt_exec_def] >>
 Cases_on ‘is_empty stmt’ >> (
  gs[] >>
  res_tac >>
  Cases_on ‘n +1 = m’ >> (
   gvs[]
  )
 ) >> (
  Cases_on ‘bigstep_stmt_exec func_map_b_func_map_ext_map_option scope_lists stmt n’ >> (
   gs[]
  ) >>
  PairCases_on ‘x’ >>
  gs[] >>
  Cases_on ‘is_empty x0’ >> (
   gs[]
  ) >- (
   res_tac >>
   fs[]
  ) >>
  res_tac >>
  fs[]
 ),

 (* transition *)
 gs[bigstep_stmt_exec_def] >>
 Cases_on ‘bigstep_e_exec scope_lists (INL e) n’ >> (
  gs[]
 ) >>
 PairCases_on ‘x’ >>
 gs[] >>
 Cases_on ‘x0’ >> (
  gs[]
 ) >>
 gvs[] >>
 imp_res_tac bigstep_e_exec_incr >>
 gs[] >>
 Cases_on ‘n = m’ >> (
  gvs[]
 ) >>
 imp_res_tac bigstep_e_exec_unchanged >>
 gs[],

 (* apply *)
 gs[bigstep_stmt_exec_def] >>
 Cases_on ‘bigstep_e_exec scope_lists (INR l) n’ >> (
  gs[]
 ) >>
 PairCases_on ‘x’ >>
 gs[] >>
 Cases_on ‘x0’ >> (
  gs[]
 ) >>
 imp_res_tac bigstep_e_exec_incr >>
 gs[] >>
 Cases_on ‘n = m’ >> (
  gvs[]
 ) >>
 imp_res_tac bigstep_e_exec_unchanged >>
 gs[],

 (* ext *)
 gs[bigstep_stmt_exec_def]
]
QED

Theorem oDROP_oTAKE:
!n l l1 l2.
oDROP n l = SOME l2 ==>
oTAKE n l = SOME l1 ==>
l = l1 ++ l2
Proof
Induct_on ‘l’ >> (
 rpt strip_tac >>
 Cases_on ‘n’ >> (
  gs[oDROP_def, oTAKE_def]
 )
) >>
Cases_on ‘oTAKE n' l’ >> (
 gs[]
) >>
res_tac >>
gs[]
QED


(**************************************)
(* Approach: add indices to arguments *)
(**************************************)

Definition augment_b_func_map_def:
 (augment_b_func_map [] = []) /\
 (augment_b_func_map (((fname, (body, params))::t):b_func_map) =
  (fname, (body,
   ZIP (COUNT_LIST (LENGTH params), params)))::augment_b_func_map t)
End

Definition augment_func_map_def:
 (augment_func_map [] = []) /\
 (augment_func_map (((fname, (body, params))::t):func_map) =
  (fname, (body,
   ZIP (COUNT_LIST (LENGTH params), params)))::augment_func_map t)
End

Definition augment_ext_fun_map_def:
 (augment_ext_fun_map [] = []) /\
 (augment_ext_fun_map (((fname, (params, impl))::t):'a ext_fun_map) =
  (fname, (ZIP (COUNT_LIST (LENGTH params), params), impl))::augment_ext_fun_map t)
End

Definition augment_ext_map_def:
 (augment_ext_map [] = []) /\
 (augment_ext_map (((fname, (SOME (params, constructor), implementations))::t):'a ext_map) =
  (fname, (SOME (ZIP (COUNT_LIST (LENGTH params), params), constructor), implementations))::augment_ext_map t)
End

Definition augment_ctx_def:
 augment_ctx ((apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map):'a ctx) = (apply_table_f,augment_ext_map ext_map,augment_func_map func_map,augment_b_func_map b_func_map,pars_map,tbl_map)
End

(* TODO: Alternative definition for e_multi_exec that uses an
 * augmented ctx, allowing to structurally split execution of
 * argument reduction *)
(* TODO: Equivalence theorem between e_multi_exec and e_multi_exec aux. *)

(* bigstep_stmt_ass_exec_sound_n_call can no longer be used *)

(*
    0.  separate (top_scope::(scope_list ++ [g_scope1; g_scope2])) =
        (SOME [g_scope1; g_scope2],SOME (top_scope::scope_list))
    1.  lookup_funn_sig funn' func_map b_func_map ext_map = SOME x_d_l
    2.  oZIP (MAP SND x_d_l,e_l) = SOME d_e_l
    3.  bigstep_f_arg_exec_l
          (top_scope::(scope_list ++ [g_scope1; g_scope2])) d_e_l n' =
        SOME (h::t,n + n')
   ------------------------------------
        stmt_multi_exec'
          (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)
          (ascope,[g_scope1; g_scope2],
           [(funn,[stmt_ass l (e_call funn' e_l)],top_scope::scope_list)],
           status_running) n =
        SOME
          (ascope,[g_scope1; g_scope2],
           [(funn,[stmt_ass l (e_call funn' (h::t))],top_scope::scope_list)],
           status_running)
*)

(* Idea: use a number signifying the (1-)index of argument after which to stop
 * reducing. Use two auxiliary definitions using this, then use them for the proof. *)
(* 1-indexing is used for ease of terminating at zero *)
(* TODO: REwrite to not consume arguments as they are reduced - use "current index" or similar.
 * unred_arg_index? *)
 (*
Definition bigstep_f_arg_exec_l_aux'_def:
 (bigstep_f_arg_exec_l_aux' scope_lists [] n _ _ = SOME ([],n)) /\
 (bigstep_f_arg_exec_l_aux' scope_lists l n 0 _ = SOME (MAP SND l,n)) /\
 (bigstep_f_arg_exec_l_aux' scope_lists (h::t) n (SUC m) (SUC k) =
(* 
  case bigstep_f_arg_exec_l_aux' scope_lists t n m k of
    NONE => NONE
  | SOME (t',n') =>
   (case bigstep_f_arg_exec' scope_lists h n' of
      NONE => NONE
    | SOME (INL h',n'') => SOME (h'::t',n''))
*)
  case bigstep_f_arg_exec' scope_lists h n of
    NONE => NONE
  | SOME (INL h',n') =>
    (case bigstep_f_arg_exec_l_aux' scope_lists t n' m of
       NONE => NONE
     | SOME (t',n'') => SOME (h'::t',n''))
  | _ => NONE
 )
End
(* The above, but with zero-indexing *)
Definition bigstep_f_arg_exec_l_aux_def:
 (bigstep_f_arg_exec_l_aux scope_lists l n m = bigstep_f_arg_exec_l_aux' scope_lists l n (SUC m) (LENGTH l))
End
*)

Definition bigstep_f_arg_exec_l_aux'_def:
 (bigstep_f_arg_exec_l_aux' scope_lists e_l n 0 = SOME (MAP SND e_l,n)) /\
 (bigstep_f_arg_exec_l_aux' scope_lists e_l n (SUC m) =
  let (d, e) = (EL m e_l) in
  case bigstep_f_arg_exec_l_aux' scope_lists e_l n m of
    NONE => NONE
  | SOME (e_l',n') =>
   (case bigstep_f_arg_exec' scope_lists (d,e) n' of
      SOME (INL e',n'') => SOME ((LUPDATE e' m e_l'),n'')
    |  _ => NONE)
(*
  (case bigstep_f_arg_exec' scope_lists (d,e) n of
     NONE => NONE
   | SOME (INL e',n') =>
     (case bigstep_f_arg_exec_l_aux' scope_lists (LUPDATE (d,e') m e_l) n' m of
        NONE => NONE
      | SOME (e_l',n'') => SOME (e_l',n''))
   | _ => NONE)
*)
 )
End
Definition bigstep_f_arg_exec_l_aux_def:
 (bigstep_f_arg_exec_l_aux scope_lists l n = bigstep_f_arg_exec_l_aux' scope_lists l n (LENGTH l))
End

Theorem bigstep_f_arg_exec_l_aux_equiv:
!scopes_list d_e_l e_l' n n'.
bigstep_f_arg_exec_l scopes_list d_e_l n = SOME (e_l', n + n') <=>
bigstep_f_arg_exec_l_aux scopes_list d_e_l n = SOME (e_l', n + n')
Proof
gs[bigstep_f_arg_exec_l_aux_def] >>
cheat
QED

(* NOTE: This does not treat nested function calls *)
Definition e_multi_exec'_aux_def:
 (e_multi_exec'_aux (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map) g_scope_list scope_list e 0 n_args = SOME e) /\
 (e_multi_exec'_aux (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map) g_scope_list scope_list e (SUC fuel) n_args =
  case e of
  | e_call funn e_l =>
   (case lookup_funn_sig funn func_map b_func_map ext_map of
    | SOME x_d_l =>
     (* TODO: Instead, limit the length of d_l and e_l by some max, and increment it when expression is
      * fully reduced. *)
     (case unred_arg_index (MAP SND x_d_l) e_l of
      | SOME i =>
       if i < n_args then
       (case e_exec (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map) g_scope_list scope_list e of
        | SOME (e', []) =>
         e_multi_exec'_aux (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map) g_scope_list scope_list e' fuel n_args
        | _ => NONE)
       else e_multi_exec'_aux (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map) g_scope_list scope_list e (SUC fuel) n_args
      | NONE => SOME e
      )
    | NONE => NONE)
  | _ => e_multi_exec' (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map) g_scope_list scope_list e (SUC fuel)
 )
Termination
cheat
End

Theorem e_multi_exec'_aux_equiv:
!ctx g_scope_list scope_list funn e_l e_l' n.
e_multi_exec' ctx g_scope_list scope_list
 (e_call funn e_l) n = SOME (e_call funn e_l') <=>
e_multi_exec'_aux ctx g_scope_list scope_list (e_call funn e_l) n (LENGTH e_l) = SOME (e_call funn e_l')
Proof
cheat
QED

(*
Theorem e_multi_exec'_aux_split:
!ctx g_scope_list scope_list funn h h' e_l e_l' n n'.
e_multi_exec'_aux ctx g_scope_list scope_list (e_call funn (h::e_l)) n 1 = SOME (e_call funn (h'::e_l)) ==>
e_multi_exec'_aux ctx g_scope_list scope_list (e_call funn (h'::e_l)) n' (LENGTH e_l) = SOME (e_call funn (h'::e_l')) ==>
e_multi_exec'_aux ctx g_scope_list scope_list (e_call funn (h::e_l)) (n+n') (LENGTH e_l) = SOME (e_call funn (h'::e_l'))
Proof
cheat
QED
*)

Theorem e_multi_exec'_aux_split:
!ctx g_scope_list scope_list funn e_l e_l' n n' e' m.
e_multi_exec'_aux ctx g_scope_list scope_list (e_call funn e_l) n m = SOME (e_call funn e_l') ==>
e_multi_exec'_aux ctx g_scope_list scope_list (e_call funn e_l') n' (SUC m) = SOME (e_call funn (LUPDATE e' m e_l')) ==>
e_multi_exec'_aux ctx g_scope_list scope_list (e_call funn e_l) (n+n') (SUC m) = SOME (e_call funn (LUPDATE e' m e_l'))
Proof
cheat
QED

(* TODO: Use this in the below? *)        
Theorem bigstep_f_arg_exec_l_aux_sound_n:
!funn func_map b_func_map ext_map (x_d_l:(string # d) list).
lookup_funn_sig funn func_map b_func_map ext_map = SOME x_d_l ==>
!m top_scope scope_list g_scope1 g_scope2 d_e_l e_l' n n'  e_l apply_table_f pars_map tbl_map.
oZIP (MAP SND x_d_l,e_l) = SOME d_e_l ==>
bigstep_f_arg_exec_l_aux' (top_scope::(scope_list ++ [g_scope1; g_scope2])) d_e_l n m =
 SOME (e_l',n + n') ==>
e_multi_exec'_aux ((apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map):'a ctx) [g_scope1; g_scope2] (top_scope::scope_list) (e_call funn (MAP SND d_e_l)) n' m = SOME (e_call funn e_l')
Proof
rpt gen_tac >>
rpt disch_tac >>
Induct_on ‘m’ >- (
 rpt strip_tac >>
 gvs[oZIP_def, AllCaseEqs(), bigstep_f_arg_exec_l_aux'_def] >>
 Cases_on ‘n'’ >> (
  gvs[e_multi_exec'_aux_def]
 )
) >>
rpt strip_tac >>
res_tac >>
Cases_on ‘e_l’ >> Cases_on ‘x_d_l’ >>  (
 gs[oZIP_def, AllCaseEqs(), bigstep_f_arg_exec_l_aux_def, bigstep_f_arg_exec_l_aux'_def]
) >- (
 Cases_on ‘EL m ([]:(d # e) list)’ >>
 gvs[AllCaseEqs()] >>
 (* Contradiction: element of empty list *)
 cheat
) >>
gvs[oZIP_def, AllCaseEqs(), bigstep_f_arg_exec_l_aux'_def] >>
Cases_on ‘EL m ((SND h',h)::t'')’ >>
gvs[oZIP_def, AllCaseEqs(), bigstep_f_arg_exec_l_aux'_def] >>
subgoal ‘?n_incr. n'' = n_incr + n’ >- (
 cheat
) >>
gvs[] >>
qpat_x_assum ‘bigstep_f_arg_exec_l_aux'
          (top_scope::(scope_list ++ [g_scope1; g_scope2])) ((SND h',h)::t'')
          n m =
        SOME (e_l'',n + n_incr)’ (fn thm => assume_tac (REWRITE_RULE [Once arithmeticTheory.ADD_SYM] thm)) >>
res_tac >>
subgoal ‘?n_incr'. n' = n_incr + n_incr'’ >- (
 cheat
) >>
gs[] >>
irule e_multi_exec'_aux_split >>
gvs[] >>
(* Only the single final step left... *)
(* Have in assums: All args up until 0-index m-1 have been fully reduced (from ind.hyp.concl.).
 * In e_l'', the arg at 0-index m has not been reduced (from ind.hyp.concl.)
 *   Therefore, it is identical to its predecessor in h::MAP SND t'', the element at 0-index m.
 * Element m of (SND h', h)::t'' is reduced in n_incr' small-steps to e'. *)
cheat
QED

(*
Theorem bigstep_f_arg_exec_l_sound_n:
!funn func_map b_func_map ext_map (x_d_l:(string # d) list).
lookup_funn_sig funn func_map b_func_map ext_map = SOME x_d_l ==>
!top_scope scope_list g_scope1 g_scope2 d_e_l e_l' n n'  e_l apply_table_f pars_map tbl_map.
oZIP (MAP SND x_d_l,e_l) = SOME d_e_l ==>
bigstep_f_arg_exec_l (top_scope::(scope_list ++ [g_scope1; g_scope2])) d_e_l n =
 SOME (e_l',n + n') ==>
e_multi_exec' ((apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map):'a ctx) [g_scope1; g_scope2] (top_scope::scope_list) (e_call funn (MAP SND d_e_l)) n' = SOME (e_call funn e_l')
Proof
(*
rpt gen_tac >>
rpt disch_tac >>
Induct_on ‘e_l’ >- (
 cheat
) >>
rpt strip_tac >>
Cases_on ‘x_d_l’ >> (
 gvs[oZIP_def, AllCaseEqs(), bigstep_f_arg_exec_l_def]
) >>
*)
rpt strip_tac >>
fs[e_multi_exec'_aux_equiv, bigstep_f_arg_exec_l_aux_equiv] >>
cheat
QED
*)

(* TODO: Can this use the soundness proof for bigstep_e? *)
Theorem bigstep_f_arg_exec_l_sound_n:
!top_scope scope_list g_scope1 g_scope2 x_d_e_l d_e_l e_l' n n' (x_d_l:(string # d) list) e_l funn apply_table_f ext_map func_map b_func_map pars_map tbl_map.
(* All lists as one:
oZIP (x_d_l, e_l) = SOME x_d_e_l ==>
oZIP (MAP SND x_d_l,e_l) = SOME d_e_l ==>
lookup_funn_sig funn func_map b_func_map ext_map = SOME (ZIP (MAP FST $ MAP FST x_d_e_l, MAP SND $ MAP FST x_d_e_l)) ==>
*)
bigstep_f_arg_exec_l (top_scope::(scope_list ++ [g_scope1; g_scope2])) d_e_l n =
 SOME (e_l',n + n') ==>

e_multi_exec' ((apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map):'a ctx) [g_scope1; g_scope2] (top_scope::scope_list) (e_call funn (MAP SND d_e_l)) n' = SOME (e_call funn e_l')
Proof
Induct_on ‘n'’ >- (
 cheat
) >>
rpt strip_tac >>
gs[e_multi_exec'_def, AllCaseEqs()] >>
Cases_on ‘d_e_l’ >- (
 cheat
) >>  
gvs[bigstep_f_arg_exec_l_def, bigstep_f_arg_exec'_def, AllCaseEqs()] >>
‘?h''.
  e_multi_exec'
   ((apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map):'a ctx)
   [g_scope1; g_scope2] (top_scope::scope_list)
   (e_call funn (h''::MAP SND (t:(d#e) list))) n' = SOME (e_call funn (h'::MAP SND t)) /\
    e_exec ((apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map):'a ctx)
   [g_scope1; g_scope2] (top_scope::scope_list) (e_call funn (SND (h:(d#e))::MAP SND t)) =
 SOME (e_call funn (h''::MAP SND t),[])’ suffices_by cheat >>
SUBGOAL_THEN “(n:num) + SUC n' = n' + SUC n” (fn thm => FULL_SIMP_TAC empty_ss [Once thm]) >- (
 cheat
) >>
res_tac >>
rpt strip_tac >>
gs[AllCaseEqs()] >>
PairCases_on ‘h’ >>
gs[bigstep_f_arg_exec_l_def, bigstep_f_arg_exec'_def, AllCaseEqs()] >- (
 (* Case further reduction of head *)
 (* TODO: Seems to work out only when a single step is taken... *)
 (* Add bigstep_e_exec and bigstep_f_arg_exec_l *)
 gs[] >>
 cheat
) >- (
(* Case no further reduction of head *)
res_tac >>
gvs[e_multi_exec'_def, AllCaseEqs()] >>
cheat
) >>
(* Case no further reduction of head *)
res_tac >>
cheat
QED

(* TODO: Instead of the above, make version similar to bigstep_stmt_ass_exec_sound_n_not_v... *)
Theorem bigstep_stmt_ass_call_exec_sound_n:
!top_scope ascope lval scope_list g_scope1 g_scope2 x_d_e_l d_e_l e_l' n n' (x_d_l:(string # d) list) e_l funn apply_table_f ext_map func_map b_func_map pars_map tbl_map.
oZIP (MAP SND x_d_l,e_l) = SOME d_e_l ==>
lookup_funn_sig funn func_map b_func_map ext_map = SOME x_d_l ==>
bigstep_f_arg_exec_l (top_scope::(scope_list ++ [g_scope1; g_scope2])) d_e_l n =
 SOME (e_l',n + n') ==>
stmt_multi_exec'
          (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)
          (ascope,[g_scope1; g_scope2],
           [(funn,[stmt_ass lval (e_call funn e_l)],top_scope::scope_list)],
           status_running) n' =
        SOME
          (ascope,[g_scope1; g_scope2],
           [(funn,[stmt_ass lval (e_call funn e_l')],top_scope::scope_list)],
           status_running)
Proof
Induct_on ‘n'’ >- (
 rpt strip_tac >>
 gs[e_multi_exec'_def, stmt_multi_exec'_def, stmt_multi_exec'_check_state_def] >>
 cheat
) >>
rpt strip_tac >>
gs[e_multi_exec'_def, stmt_multi_exec'_def] >>
cheat
(*
Cases_on ‘e_multi_exec' (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map) [g_scope1; g_scope2] (top_scope::scope_list) e n’ >> (
 gs[]
) >>
Cases_on ‘e_exec ctx [g_scope1; g_scope2] (top_scope::scope_list) x’ >> (
 gs[]
) >>
PairCases_on ‘x'’ >>
gs[] >>
Cases_on ‘x'1’ >> (
 gs[]
) >>
gvs[] >>
subgoal ‘~is_v x’ >- (
 imp_res_tac e_exec_not_v
) >>
res_tac >>
fs[stmt_exec_def, stmt_multi_exec'_check_state_def]
*)
QED

Theorem bigstep_stmt_exec_sound_n:
!n n' scope_list scope_lists' scope_list' funn ascope stmt stmt' top_scope g_scope1 g_scope2 g_scope_list' ctx.
bigstep_stmt_exec (NONE:(func_map # b_func_map # 'a ext_map) option) ((top_scope::scope_list)++[g_scope1; g_scope2]) stmt n' = SOME (stmt', scope_lists', n' + n) ==>
separate scope_lists' = (SOME g_scope_list',SOME scope_list') ==>
stmt_multi_exec' (ctx:'a ctx) (ascope:'a, [g_scope1; g_scope2]:g_scope_list, [(funn, [stmt], (top_scope::scope_list))], status_running) n = SOME (ascope, g_scope_list', [(funn, [stmt'], scope_list')], status_running)
Proof
Induct_on ‘stmt’ >- (
 (* empty *)
 gs[stmt_multi_exec'_def, bigstep_stmt_exec_def, stmt_multi_exec'_check_state_def] >>
 rpt strip_tac >> (
  subgoal ‘n = 0’ >- (
   decide_tac
  ) >>
  fs[separate_def, SUC_ADD_ONE, stmt_multi_exec'_def, stmt_multi_exec'_check_state_def] >>
  fs[GSYM SUC_ADD_ONE, oDROP_def, oTAKE_def, oDROP_APPEND, oTAKE_APPEND]
 )
) >- (
 (* assignment *)
 gs[bigstep_stmt_exec_def] >>
 rpt strip_tac >>
 (* Rule this out first... *)
 Cases_on ‘?funn e_l. e = e_call funn e_l’ >- (
  gs[] >>
  Cases_on ‘bigstep_f_arg_exec NONE (top_scope::(scope_list ++ [g_scope1; g_scope2]))
              (funn',e_l) n'’ >> (
   gs[]
  ) >>
  PairCases_on ‘x’ >>
  gs[] >>
  Cases_on ‘x0’ >> (
   gs[]
  ) >> (
   gvs[] >>
   subgoal ‘[g_scope1; g_scope2] = g_scope_list'’ >- (
    subgoal ‘LENGTH [g_scope1; g_scope2] = 2’ >- (
     gs[]
    ) >>
    metis_tac[scope_lists_separate]
   ) >>
   subgoal ‘top_scope::scope_list = scope_list'’ >- (
    subgoal ‘LENGTH [g_scope1; g_scope2] = 2’ >- (
     gs[]
    ) >>
    metis_tac[scope_lists_separate]
   ) >>
   gvs[stmt_multi_exec'_def, bigstep_f_arg_exec_def, stmt_multi_exec'_check_state_def] >>
   subgoal ‘n = 0’ >- (
    decide_tac
   ) >>
   fs[separate_def, SUC_ADD_ONE, stmt_multi_exec'_def, stmt_multi_exec'_check_state_def]
  )
 ) >>
 Cases_on ‘bigstep_e_exec (top_scope::(scope_list ++ [g_scope1; g_scope2])) (INL e) n'’ >> (
  gs[]
 ) >- (
  Cases_on ‘e’ >> (
   gs[]
  )
 ) >>
 PairCases_on ‘x’ >>
 gs[] >>
 Cases_on ‘x0’ >> (
  gs[]
 ) >- (
  Cases_on ‘is_v x’ >> (
   gs[]
  ) >- (
   Cases_on ‘stmt_exec_ass l x (top_scope::(scope_list ++ [g_scope1; g_scope2]))’ >> (
    gs[]
   ) >> (
    Cases_on ‘e’ >> (
     gvs[]
    )
   ) >> (
    subgoal ‘x1 = n' + (n - 1)’ >- (
     imp_res_tac bigstep_e_exec_incr >>
     decide_tac
    ) >>
    fs[] >>
    FULL_SIMP_TAC pure_ss [GSYM APPEND] >>
    imp_res_tac bigstep_e_exec_sound_n_INL_zero >>
    qpat_x_assum ‘!ctx. _’ (fn thm => ASSUME_TAC (Q.SPEC ‘ctx’ thm)) >>
    subgoal ‘LENGTH scope_lists' > 2’ >- (
     Cases_on ‘x’ >> (
      gs[is_v_def]
     ) >>
     gs[stmt_exec_ass_def] >>
     imp_res_tac assign_LENGTH >>
     gs[]
    ) >>
    imp_res_tac separate_SOME_imp >>
    imp_res_tac bigstep_stmt_ass_exec_sound_n_v >>
    Cases_on ‘n’ >> (
     gs[SUC_ADD_ONE]
    )
   )
  ) >>
  Cases_on ‘e’ >> (
   gvs[]
  ) >> (
   FULL_SIMP_TAC pure_ss [GSYM APPEND, Once arithmeticTheory.ADD_SYM] >>
   imp_res_tac bigstep_e_exec_sound_n_INL_zero >>
   qpat_x_assum ‘!ctx. _’ (fn thm => ASSUME_TAC (Q.SPEC ‘ctx’ thm)) >>
   imp_res_tac bigstep_stmt_ass_exec_sound_n_not_v >>
   gs[] >>
   irule scope_lists_separate >>
   gs[]
  )
 ) >>
 Cases_on ‘e’ >> (
  gvs[]
 )
) >- (
 (* conditional *)
 gs[bigstep_stmt_exec_def] >>
 rpt strip_tac >>
 (* Rule this out first... *)
 Cases_on ‘?funn e_l. e = e_call funn e_l’ >- (
  gs[] >>
  Cases_on ‘bigstep_f_arg_exec NONE (top_scope::(scope_list ++ [g_scope1; g_scope2]))
              (funn',e_l) n'’ >> (
   gs[]
  ) >>
  PairCases_on ‘x’ >>
  gs[] >>
  Cases_on ‘x0’ >> (
   gs[]
  ) >> (
   gvs[] >>
   subgoal ‘[g_scope1; g_scope2] = g_scope_list'’ >- (
    subgoal ‘LENGTH [g_scope1; g_scope2] = 2’ >- (
     gs[]
    ) >>
    metis_tac[scope_lists_separate]
   ) >>
   subgoal ‘top_scope::scope_list = scope_list'’ >- (
    subgoal ‘LENGTH [g_scope1; g_scope2] = 2’ >- (
     gs[]
    ) >>
    metis_tac[scope_lists_separate]
   ) >>
   gvs[stmt_multi_exec'_def, bigstep_f_arg_exec_def, stmt_multi_exec'_check_state_def] >>
   subgoal ‘n = 0’ >- (
    decide_tac
   ) >>
   fs[stmt_multi_exec'_def, stmt_multi_exec'_check_state_def]
  )
 ) >>
 Cases_on ‘bigstep_e_exec (top_scope::(scope_list ++ [g_scope1; g_scope2])) (INL e) n'’ >> (
  gs[]
 ) >- (
  Cases_on ‘e’ >> (
   gs[]
  )
 ) >>
 PairCases_on ‘x’ >>
 gs[] >>
 Cases_on ‘x0’ >> (
  gs[]
 ) >> (
  Cases_on ‘e’ >> (
   gvs[]
  )
 ) >> (
  FULL_SIMP_TAC pure_ss [GSYM APPEND, Once arithmeticTheory.ADD_SYM] >>
  imp_res_tac bigstep_e_exec_sound_n_INL_zero >>
  qpat_x_assum ‘!ctx. _’ (fn thm => ASSUME_TAC (Q.SPEC ‘ctx’ thm)) >>
  imp_res_tac bigstep_stmt_cond_exec_sound_n >>
  gs[] >>
  irule scope_lists_separate >>
  gs[]
 )
) >- (
 (* block *)
 gs[stmt_multi_exec'_def, bigstep_stmt_exec_def, stmt_multi_exec'_check_state_def] >>
 rpt strip_tac >> (
  subgoal ‘n = 0’ >- (
   decide_tac
  ) >>
  fs[separate_def, SUC_ADD_ONE, stmt_multi_exec'_def, stmt_multi_exec'_check_state_def] >>
  fs[GSYM SUC_ADD_ONE, oDROP_def, oTAKE_def, oDROP_APPEND, oTAKE_APPEND]
 )
) >- (
 (* return *)
 gs[bigstep_stmt_exec_def] >>
 rpt strip_tac >>
 Cases_on ‘bigstep_e_exec (top_scope::(scope_list ++ [g_scope1; g_scope2])) (INL e) n'’ >> (
  gs[]
 ) >>
 PairCases_on ‘x’ >>
 gs[] >>
 Cases_on ‘x0’ >> (
  gs[]
 ) >>
 gvs[] >>
 FULL_SIMP_TAC pure_ss [GSYM APPEND, Once arithmeticTheory.ADD_SYM] >>
 imp_res_tac bigstep_e_exec_sound_n_INL_zero >>
 qpat_x_assum ‘!ctx. _’ (fn thm => ASSUME_TAC (Q.SPEC ‘ctx’ thm)) >>
 imp_res_tac bigstep_stmt_ret_exec_sound_n >>
 gvs[] >>
 irule scope_lists_separate >>
 gs[]
) >- (

 (* seq *)
 gs[bigstep_stmt_exec_def] >>
 rpt strip_tac >>
 Cases_on ‘n’ >- (
  Cases_on ‘is_empty stmt’ >> (
   gs[]
  ) >- (
   imp_res_tac bigstep_stmt_exec_imp >>
   gs[]
  ) >>
  Cases_on ‘bigstep_stmt_exec (NONE:(func_map # b_func_map # 'a ext_map) option)
             (top_scope::(scope_list ++ [g_scope1; g_scope2])) stmt n'’ >> (
   gs[]
  ) >>
  PairCases_on ‘x’ >>
  gs[] >>
  Cases_on ‘is_empty x0’ >> (
   gs[]
  ) >> (
   imp_res_tac bigstep_stmt_exec_imp >>
   gs[stmt_multi_exec'_def, stmt_multi_exec'_check_state_def] >>
   irule scope_lists_separate >>
   gs[]
  )
 ) >>
 Cases_on ‘is_empty stmt’ >> (
  gs[]
 ) >- (
  (* Case stmt empty *)
  (* Firstly, stmt' reduced to stmt'' in n'' steps. (use ind.hyp.)
   * Finally, stmt + seq reduced in 1 step. (Expand definition in goal, or use lemma?) *)
  irule bigstep_stmt_seq_exec_sound_n_second >>
  gs[] >>
  qpat_x_assum ‘!n n' scope_list scope_lists' scope_list' funn ascope stmt''
          top_scope g_scope1 g_scope2 g_scope_list' ctx.
        bigstep_stmt_exec (NONE:(func_map # b_func_map # 'a ext_map) option)
          (top_scope::(scope_list ++ [g_scope1; g_scope2])) stmt' n' =
        SOME (stmt'',scope_lists',n + n') ==>
        separate scope_lists' = (SOME g_scope_list',SOME scope_list') ==>
        stmt_multi_exec' ctx
          (ascope,[g_scope1; g_scope2],
           [(funn,[stmt'],top_scope::scope_list)],status_running) n =
        SOME
          (ascope,g_scope_list',[(funn,[stmt''],scope_list')],
           status_running)’ (fn thm => irule thm) >>
  qexistsl_tac [‘n' + 1’, ‘scope_lists'’] >>
  gs[]
 ) >>
 Cases_on ‘bigstep_stmt_exec (NONE:(func_map # b_func_map # 'a ext_map) option)
             (top_scope::(scope_list ++ [g_scope1; g_scope2])) stmt n'’ >> (
  gs[]
 ) >>
 PairCases_on ‘x’ >>
 gs[] >>
 Cases_on ‘is_empty x0’ >> (
  gs[]
 ) >- (
  (* Case 1st statement reduced to empty *)
  (* Firstly, stmt reduced to stmt_empty in (x2-n') steps. (use ind.hyp.)
   * Then, stmt' reduced to stmt'' in (n' + SUC n'' - (x2+1)) steps. (use ind.hyp.)
   * Finally, use seq-case lemma composing stmt_multi_exec (similar to e case) *)
  irule bigstep_stmt_seq_exec_sound_n_both >>
  gvs[] >>
  imp_res_tac bigstep_stmt_exec_imp >>
  subgoal ‘?g_scope1' g_scope2' top_scope scope_list'.
           separate x1 = (SOME [g_scope1'; g_scope2'],SOME (top_scope::scope_list'))’ >- (
   (* Need something along the lines of that bigstep_stmt_exec preserves scope list length,
    * then a lemma that says that separate has a result so long as the scope list has length
    * at least 2 *)
   gs[separate_LENGTH_SOME]
  ) >>
  qexistsl_tac [‘[g_scope1'; g_scope2']’, ‘x2-n'’, ‘(n' + n'' + 1)-(x2+1)’, ‘(top_scope'::scope_list'')’, ‘x0’] >>
  gs[] >>
  rpt strip_tac >- (
   qpat_x_assum ‘!n n' scope_list scope_lists' scope_list' funn ascope stmt''
             top_scope g_scope1 g_scope2 g_scope_list' ctx.
           bigstep_stmt_exec (NONE:(func_map # b_func_map # 'a ext_map) option)
             (top_scope::(scope_list ++ [g_scope1; g_scope2])) stmt' n' =
           SOME (stmt'',scope_lists',n + n') ==>
           separate scope_lists' = (SOME g_scope_list',SOME scope_list') ==>
           stmt_multi_exec' ctx
             (ascope,[g_scope1; g_scope2],
              [(funn,[stmt'],top_scope::scope_list)],status_running) n =
           SOME
             (ascope,g_scope_list',[(funn,[stmt''],scope_list')],
              status_running)’ (fn thm => irule thm) >>
   qexistsl_tac [‘x2 + 1’, ‘scope_lists'’] >>
   gs[] >>
   subgoal ‘x1 = (top_scope'::(scope_list'' ++ [g_scope1'; g_scope2']))’ >- (
    (* Requires a theorem stating the reverse effect of separate *)
    gs[separate_def] >>
    gvs[SUC_ADD_ONE] >>
    Cases_on ‘x1’ >> (
     gs[GSYM SUC_ADD_ONE]
    ) >>
    gs[oDROP_def, oTAKE_def] >>
    Cases_on ‘oTAKE (LENGTH scope_list) t’ >> (
     gs[]
    ) >>
    gvs[] >>
    imp_res_tac bigstep_stmt_exec_imp >>
    irule oDROP_oTAKE >>
    qexists_tac ‘LENGTH scope_list’ >>
    gs[]
   ) >>
   subgoal ‘n' + n'' - x2 + (x2 + 1) = n' + SUC n''’ >- (
    imp_res_tac bigstep_stmt_exec_imp >>
    decide_tac
   ) >>
   gs[SUC_ADD_ONE]
  ) >>
  qpat_x_assum ‘!n n' scope_list scope_lists' scope_list' funn ascope stmt''
           top_scope g_scope1 g_scope2 g_scope_list' ctx.
         bigstep_stmt_exec (NONE:(func_map # b_func_map # 'a ext_map) option)
           (top_scope::(scope_list ++ [g_scope1; g_scope2])) stmt n' =
         SOME (stmt'',scope_lists',n + n') ==>
         separate scope_lists' = (SOME g_scope_list',SOME scope_list') ==>
         stmt_multi_exec' ctx
           (ascope,[g_scope1; g_scope2],
            [(funn,[stmt],top_scope::scope_list)],status_running) n =
         SOME
           (ascope,g_scope_list',[(funn,[stmt''],scope_list')],
            status_running)’ (fn thm => irule thm) >>
  qexistsl_tac [‘n'’, ‘x1’] >>
  gs[] >>
  imp_res_tac bigstep_stmt_exec_imp >>
  decide_tac
 ) >>
 (* Reduction of 1st statement only *)
 (* Firstly, stmt reduced to x0 in SUC n'' steps. (use ind.hyp.)
  * Finally, use seq-case lemma composing stmt_multi_exec (similar to e case) *)
 gvs[] >>
 Q.SUBGOAL_THEN ‘n' + SUC n'' = (SUC n'') + n'’ (fn thm => FULL_SIMP_TAC pure_ss [thm]) >- (
  decide_tac
 ) >>
 res_tac >>
 irule bigstep_stmt_seq_exec_sound_n_first >>
 gs[]
) >- (

 (* trans *)
 gs[bigstep_stmt_exec_def] >>
 rpt strip_tac >>
 Cases_on ‘bigstep_e_exec (top_scope::(scope_list ++ [g_scope1; g_scope2])) (INL e) n'’ >> (
  gs[]
 ) >>
 PairCases_on ‘x’ >>
 gs[] >>
 Cases_on ‘x0’ >> (
  gs[]
 ) >>
 gvs[] >>
 FULL_SIMP_TAC pure_ss [GSYM APPEND, Once arithmeticTheory.ADD_SYM] >>
 imp_res_tac bigstep_e_exec_sound_n_INL_zero >>
 qpat_x_assum ‘!ctx. _’ (fn thm => ASSUME_TAC (Q.SPEC ‘ctx’ thm)) >>
 imp_res_tac bigstep_stmt_trans_exec_sound_n >>
 gvs[] >>
 irule scope_lists_separate >>
 gs[]
) >- (

 (* apply *)
 gs[bigstep_stmt_exec_def] >>
 rpt strip_tac >>
 Cases_on ‘bigstep_e_exec (top_scope::(scope_list ++ [g_scope1; g_scope2])) (INR l) n'’ >> (
  gs[]
 ) >>
 PairCases_on ‘x’ >>
 gs[] >>
 Cases_on ‘x0’ >> (
  gs[]
 ) >>
 gvs[] >>
 FULL_SIMP_TAC pure_ss [GSYM APPEND, Once arithmeticTheory.ADD_SYM] >>
 (* Need INR version of bigstep_e_exec_sound_n_INL_zero *)
 imp_res_tac bigstep_e_exec_sound_n_INR_zero >>
 qpat_x_assum ‘!ctx. _’ (fn thm => ASSUME_TAC (Q.SPEC ‘ctx’ thm)) >>
 imp_res_tac bigstep_stmt_app_exec_sound_n >>
 gvs[] >>
 irule scope_lists_separate >>
 gs[]
) >- (

 (* extern *)
 gs[stmt_multi_exec'_def, bigstep_stmt_exec_def, stmt_multi_exec'_check_state_def] >>
 rpt strip_tac >> (
  subgoal ‘n = 0’ >- (
   decide_tac
  ) >>
  fs[separate_def, SUC_ADD_ONE, stmt_multi_exec'_def, stmt_multi_exec'_check_state_def] >>
  fs[GSYM SUC_ADD_ONE, oDROP_def, oTAKE_def, oDROP_APPEND, oTAKE_APPEND]
 )
)
QED

(* TODO: Unify and state the above using an option variable instead? *)
Theorem bigstep_stmt_exec_SOME_sound_n:
!n n' scope_list scope_lists' scope_list' funn ascope stmt stmt' top_scope g_scope1 g_scope2 g_scope_list' apply_table_f ext_map func_map b_func_map pars_map tbl_map.
bigstep_stmt_exec (SOME (func_map, b_func_map, ext_map)) ((top_scope::scope_list)++[g_scope1; g_scope2]) stmt n' = SOME (stmt', scope_lists', n' + n) ==>
separate scope_lists' = (SOME g_scope_list',SOME scope_list') ==>
stmt_multi_exec' ((apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map):'a ctx) (ascope:'a, [g_scope1; g_scope2]:g_scope_list, [(funn, [stmt], (top_scope::scope_list))], status_running) n = SOME (ascope, g_scope_list', [(funn, [stmt'], scope_list')], status_running)
Proof
(* Proof based on copy-paste of the above *)
Induct_on ‘stmt’ >- (
 (* empty *)
 gs[stmt_multi_exec'_def, bigstep_stmt_exec_def, stmt_multi_exec'_check_state_def] >>
 rpt strip_tac >> (
  subgoal ‘n = 0’ >- (
   decide_tac
  ) >>
  fs[separate_def, SUC_ADD_ONE, stmt_multi_exec'_def, stmt_multi_exec'_check_state_def] >>
  fs[GSYM SUC_ADD_ONE, oDROP_def, oTAKE_def, oDROP_APPEND, oTAKE_APPEND]
 )
) >- (

 (* assignment *)
 gs[bigstep_stmt_exec_def] >>
 rpt strip_tac >>
 (* Rule this out first... *)
 Cases_on ‘?funn e_l. e = e_call funn e_l’ >- (
  gs[] >>
  Cases_on ‘bigstep_f_arg_exec (SOME (func_map,b_func_map,ext_map)) (top_scope::(scope_list ++ [g_scope1; g_scope2]))
              (funn',e_l) n'’ >> (
   gs[]
  ) >>
  PairCases_on ‘x’ >>
  gs[] >>
  Cases_on ‘x0’ >> (
   gs[]
  ) >> (
   gvs[] >>
   subgoal ‘[g_scope1; g_scope2] = g_scope_list'’ >- (
    subgoal ‘LENGTH [g_scope1; g_scope2] = 2’ >- (
     gs[]
    ) >>
    metis_tac[scope_lists_separate]
   ) >>
   subgoal ‘top_scope::scope_list = scope_list'’ >- (
    subgoal ‘LENGTH [g_scope1; g_scope2] = 2’ >- (
     gs[]
    ) >>
    metis_tac[scope_lists_separate]
   ) >>
   gvs[stmt_multi_exec'_def, bigstep_f_arg_exec_def, stmt_multi_exec'_check_state_def] >>
   gs[AllCaseEqs()]
  ) >- (
   subgoal ‘e_l = [] /\ x_d_l = []’ >- (
    imp_res_tac bigstep_f_arg_exec_l_imp >>
    Cases_on ‘d_e_l’ >> (
     gs[]
    ) >>
    imp_res_tac oZIP_lemma2 >>
    gs[]
   ) >>
   gvs[stmt_multi_exec'_def, bigstep_f_arg_exec_l_def, bigstep_f_arg_exec_def, stmt_multi_exec'_check_state_def, oZIP_def] >>
   subgoal ‘n = 0’ >- (
    decide_tac
   ) >>
   fs[separate_def, SUC_ADD_ONE, stmt_multi_exec'_def, stmt_multi_exec'_check_state_def]
  ) >>
  FULL_SIMP_TAC pure_ss [Once arithmeticTheory.ADD_SYM] >>
  imp_res_tac bigstep_f_arg_exec_l_sound_n >>
  irule bigstep_stmt_ass_exec_sound_n_not_v >>
  gs[is_v_def] >>
  cheat
 ) >>
 Cases_on ‘bigstep_e_exec (top_scope::(scope_list ++ [g_scope1; g_scope2])) (INL e) n'’ >> (
  gs[]
 ) >- (
  Cases_on ‘e’ >> (
   gs[bigstep_e_exec_def, AllCaseEqs()]
  )
 ) >>
 PairCases_on ‘x’ >>
 gs[] >>
 Cases_on ‘x0’ >> (
  gs[]
 ) >- (
  Cases_on ‘is_v x’ >> (
   gs[]
  ) >- (
   Cases_on ‘stmt_exec_ass l x (top_scope::(scope_list ++ [g_scope1; g_scope2]))’ >> (
    gs[]
   ) >> (
    Cases_on ‘e’ >> (
     gvs[]
    )
   ) >> (
    subgoal ‘x1 = n' + (n - 1)’ >- (
     imp_res_tac bigstep_e_exec_incr >>
     decide_tac
    ) >>
    fs[] >>
    FULL_SIMP_TAC pure_ss [GSYM APPEND] >>
    imp_res_tac bigstep_e_exec_sound_n_INL_zero >>
    qpat_x_assum ‘!ctx. _’ (fn thm => ASSUME_TAC (Q.SPEC ‘(apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)’ thm)) >>
    subgoal ‘LENGTH scope_lists' > 2’ >- (
     Cases_on ‘x’ >> (
      gs[is_v_def]
     ) >>
     gs[stmt_exec_ass_def] >>
     imp_res_tac assign_LENGTH >>
     gs[]
    ) >>
    imp_res_tac separate_SOME_imp >>
    imp_res_tac bigstep_stmt_ass_exec_sound_n_v >>
    Cases_on ‘n’ >> (
     gs[SUC_ADD_ONE]
    )
   )
  ) >>
  Cases_on ‘e’ >> (
   gvs[]
  ) >> (
   FULL_SIMP_TAC pure_ss [GSYM APPEND, Once arithmeticTheory.ADD_SYM] >>
   imp_res_tac bigstep_e_exec_sound_n_INL_zero >>
   qpat_x_assum ‘!ctx. _’ (fn thm => ASSUME_TAC (Q.SPEC ‘(apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)’ thm)) >>
   imp_res_tac bigstep_stmt_ass_exec_sound_n_not_v >>
   gs[] >>
   irule scope_lists_separate >>
   gs[]
  )
 ) >>
 Cases_on ‘e’ >> (
  gvs[]
 )
) >- (

 (* conditional *)
 gs[bigstep_stmt_exec_def] >>
 rpt strip_tac >>
 (* Rule this out first... *)
 Cases_on ‘?funn e_l. e = e_call funn e_l’ >- (
  gs[] >>
  Cases_on ‘bigstep_f_arg_exec (SOME (func_map,b_func_map,ext_map)) (top_scope::(scope_list ++ [g_scope1; g_scope2]))
              (funn',e_l) n'’ >> (
   gs[]
  ) >>
  PairCases_on ‘x’ >>
  gs[] >>
  Cases_on ‘x0’ >> (
   gs[]
  ) >> (
   gvs[] >>
   subgoal ‘[g_scope1; g_scope2] = g_scope_list'’ >- (
    subgoal ‘LENGTH [g_scope1; g_scope2] = 2’ >- (
     gs[]
    ) >>
    metis_tac[scope_lists_separate]
   ) >>
   subgoal ‘top_scope::scope_list = scope_list'’ >- (
    subgoal ‘LENGTH [g_scope1; g_scope2] = 2’ >- (
     gs[]
    ) >>
    metis_tac[scope_lists_separate]
   ) >>
   gvs[stmt_multi_exec'_def, bigstep_f_arg_exec_def, stmt_multi_exec'_check_state_def] >>
   gs[AllCaseEqs()]
  ) >- (
   subgoal ‘e_l = [] /\ x_d_l = []’ >- (
    imp_res_tac bigstep_f_arg_exec_l_imp >>
    Cases_on ‘d_e_l’ >> (
     gs[]
    ) >>
    imp_res_tac oZIP_lemma2 >>
    gs[]
   ) >>
   gvs[stmt_multi_exec'_def, bigstep_f_arg_exec_l_def, bigstep_f_arg_exec_def, stmt_multi_exec'_check_state_def, oZIP_def] >>
   subgoal ‘n = 0’ >- (
    decide_tac
   ) >>
   fs[separate_def, SUC_ADD_ONE, stmt_multi_exec'_def, stmt_multi_exec'_check_state_def]
  ) >>
  FULL_SIMP_TAC pure_ss [Once arithmeticTheory.ADD_SYM] >>
  imp_res_tac bigstep_f_arg_exec_l_sound_n >>
  irule bigstep_stmt_cond_exec_sound_n >>
  gs[is_v_def] >>
  cheat
 ) >>
 Cases_on ‘bigstep_e_exec (top_scope::(scope_list ++ [g_scope1; g_scope2])) (INL e) n'’ >> (
  gs[]
 ) >- (
  Cases_on ‘e’ >> (
   gs[]
  )
 ) >>
 PairCases_on ‘x’ >>
 gs[] >>
 Cases_on ‘x0’ >> (
  gs[]
 ) >> (
  Cases_on ‘e’ >> (
   gvs[]
  )
 ) >> (
  FULL_SIMP_TAC pure_ss [GSYM APPEND, Once arithmeticTheory.ADD_SYM] >>
  imp_res_tac bigstep_e_exec_sound_n_INL_zero >>
  qpat_x_assum ‘!ctx. _’ (fn thm => ASSUME_TAC (Q.SPEC ‘(apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)’ thm)) >>
  imp_res_tac bigstep_stmt_cond_exec_sound_n >>
  gs[] >>
  irule scope_lists_separate >>
  gs[]
 )
) >- (

 (* block *)
 gs[stmt_multi_exec'_def, bigstep_stmt_exec_def, stmt_multi_exec'_check_state_def] >>
 rpt strip_tac >> (
  subgoal ‘n = 0’ >- (
   decide_tac
  ) >>
  fs[separate_def, SUC_ADD_ONE, stmt_multi_exec'_def, stmt_multi_exec'_check_state_def] >>
  fs[GSYM SUC_ADD_ONE, oDROP_def, oTAKE_def, oDROP_APPEND, oTAKE_APPEND]
 )
) >- (

 (* return *)
 gs[bigstep_stmt_exec_def] >>
 rpt strip_tac >>
 Cases_on ‘bigstep_e_exec (top_scope::(scope_list ++ [g_scope1; g_scope2])) (INL e) n'’ >> (
  gs[]
 ) >>
 PairCases_on ‘x’ >>
 gs[] >>
 Cases_on ‘x0’ >> (
  gs[]
 ) >>
 gvs[] >>
 FULL_SIMP_TAC pure_ss [GSYM APPEND, Once arithmeticTheory.ADD_SYM] >>
 imp_res_tac bigstep_e_exec_sound_n_INL_zero >>
 qpat_x_assum ‘!ctx. _’ (fn thm => ASSUME_TAC (Q.SPEC ‘(apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)’ thm)) >>
 imp_res_tac bigstep_stmt_ret_exec_sound_n >>
 gvs[] >>
 irule scope_lists_separate >>
 gs[]
) >- (

 (* seq *)
 gs[bigstep_stmt_exec_def] >>
 rpt strip_tac >>
 Cases_on ‘n’ >- (
  Cases_on ‘is_empty stmt’ >> (
   gs[]
  ) >- (
   imp_res_tac bigstep_stmt_exec_SOME_imp >>
   gs[]
  ) >>
  Cases_on ‘bigstep_stmt_exec (SOME (func_map,b_func_map,ext_map))
             (top_scope::(scope_list ++ [g_scope1; g_scope2])) stmt n'’ >> (
   gs[]
  ) >>
  PairCases_on ‘x’ >>
  gs[] >>
  Cases_on ‘is_empty x0’ >> (
   gs[]
  ) >> (
   imp_res_tac bigstep_stmt_exec_SOME_imp >>
   gs[stmt_multi_exec'_def, stmt_multi_exec'_check_state_def] >>
   irule scope_lists_separate >>
   gs[]
  )
 ) >>
 Cases_on ‘is_empty stmt’ >> (
  gs[]
 ) >- (
  (* Case stmt empty *)
  (* Firstly, stmt' reduced to stmt'' in n'' steps. (use ind.hyp.)
   * Finally, stmt + seq reduced in 1 step. (Expand definition in goal, or use lemma?) *)
  irule bigstep_stmt_seq_exec_sound_n_second >>
  gs[] >>
  qpat_x_assum ‘!n n' scope_list scope_lists'
                scope_list' funn ascope stmt''
          top_scope g_scope1 g_scope2 g_scope_list' apply_table_f ext_map
            func_map b_func_map pars_map tbl_map.
        bigstep_stmt_exec (SOME (func_map,b_func_map,ext_map))
          (top_scope::(scope_list ++ [g_scope1; g_scope2])) stmt' n' =
        SOME (stmt'',scope_lists',n + n') ==>
        separate scope_lists' = (SOME g_scope_list',SOME scope_list') ==>
        stmt_multi_exec' (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)
          (ascope,[g_scope1; g_scope2],
           [(funn,[stmt'],top_scope::scope_list)],status_running) n =
        SOME
          (ascope,g_scope_list',[(funn,[stmt''],scope_list')],
           status_running)’ (fn thm => irule thm) >>
  qexistsl_tac [‘n' + 1’, ‘scope_lists'’] >>
  gs[]
 ) >>
 Cases_on ‘bigstep_stmt_exec (SOME (func_map,b_func_map,ext_map))
             (top_scope::(scope_list ++ [g_scope1; g_scope2])) stmt n'’ >> (
  gs[]
 ) >>
 PairCases_on ‘x’ >>
 gs[] >>
 Cases_on ‘is_empty x0’ >> (
  gs[]
 ) >- (
  (* Case 1st statement reduced to empty *)
  (* Firstly, stmt reduced to stmt_empty in (x2-n') steps. (use ind.hyp.)
   * Then, stmt' reduced to stmt'' in (n' + SUC n'' - (x2+1)) steps. (use ind.hyp.)
   * Finally, use seq-case lemma composing stmt_multi_exec (similar to e case) *)
  irule bigstep_stmt_seq_exec_sound_n_both >>
  gvs[] >>
  imp_res_tac bigstep_stmt_exec_SOME_imp >>
  subgoal ‘?g_scope1' g_scope2' top_scope scope_list'.
           separate x1 = (SOME [g_scope1'; g_scope2'],SOME (top_scope::scope_list'))’ >- (
   (* Need something along the lines of that bigstep_stmt_exec preserves scope list length,
    * then a lemma that says that separate has a result so long as the scope list has length
    * at least 2 *)
   gs[separate_LENGTH_SOME]
  ) >>
  qexistsl_tac [‘[g_scope1'; g_scope2']’, ‘x2-n'’, ‘(n' + n'' + 1)-(x2+1)’, ‘(top_scope'::scope_list'')’, ‘x0’] >>
  gs[] >>
  rpt strip_tac >- (
   qpat_x_assum ‘!n n' scope_list scope_lists'
                 scope_list' funn ascope stmt''
             top_scope g_scope1 g_scope2 g_scope_list' apply_table_f ext_map
            func_map b_func_map pars_map tbl_map.
           bigstep_stmt_exec (SOME (func_map,b_func_map,ext_map))
             (top_scope::(scope_list ++ [g_scope1; g_scope2])) stmt' n' =
           SOME (stmt'',scope_lists',n + n') ==>
           separate scope_lists' = (SOME g_scope_list',SOME scope_list') ==>
           stmt_multi_exec' (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)
             (ascope,[g_scope1; g_scope2],
              [(funn,[stmt'],top_scope::scope_list)],status_running) n =
           SOME
             (ascope,g_scope_list',[(funn,[stmt''],scope_list')],
              status_running)’ (fn thm => irule thm) >>
   qexistsl_tac [‘x2 + 1’, ‘scope_lists'’] >>
   gs[] >>
   subgoal ‘x1 = (top_scope'::(scope_list'' ++ [g_scope1'; g_scope2']))’ >- (
    (* Requires a theorem stating the reverse effect of separate *)
    gs[separate_def] >>
    gvs[SUC_ADD_ONE] >>
    Cases_on ‘x1’ >> (
     gs[GSYM SUC_ADD_ONE]
    ) >>
    gs[oDROP_def, oTAKE_def] >>
    Cases_on ‘oTAKE (LENGTH scope_list) t’ >> (
     gs[]
    ) >>
    gvs[] >>
    imp_res_tac bigstep_stmt_exec_imp >>
    irule oDROP_oTAKE >>
    qexists_tac ‘LENGTH scope_list’ >>
    gs[]
   ) >>
   subgoal ‘n' + n'' - x2 + (x2 + 1) = n' + SUC n''’ >- (
    imp_res_tac bigstep_stmt_exec_SOME_imp >>
    decide_tac
   ) >>
   gs[SUC_ADD_ONE]
  ) >>
  qpat_x_assum ‘!n n' scope_list scope_lists'
                scope_list' funn ascope stmt''
           top_scope g_scope1 g_scope2 g_scope_list' apply_table_f ext_map
            func_map b_func_map pars_map tbl_map.
         bigstep_stmt_exec func_map_b_func_map_ext_map_opt
           (top_scope::(scope_list ++ [g_scope1; g_scope2])) stmt n' =
         SOME (stmt'',scope_lists',n + n') ==>
         separate scope_lists' = (SOME g_scope_list',SOME scope_list') ==>
         stmt_multi_exec' (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)
           (ascope,[g_scope1; g_scope2],
            [(funn,[stmt],top_scope::scope_list)],status_running) n =
         SOME
           (ascope,g_scope_list',[(funn,[stmt''],scope_list')],
            status_running)’ (fn thm => irule thm) >>
  qexistsl_tac [‘n'’, ‘x1’] >>
  gs[] >>
  imp_res_tac bigstep_stmt_exec_SOME_imp >>
  decide_tac
 ) >>
 (* Reduction of 1st statement only *)
 (* Firstly, stmt reduced to x0 in SUC n'' steps. (use ind.hyp.)
  * Finally, use seq-case lemma composing stmt_multi_exec (similar to e case) *)
 gvs[] >>
 Q.SUBGOAL_THEN ‘n' + SUC n'' = (SUC n'') + n'’ (fn thm => FULL_SIMP_TAC pure_ss [thm]) >- (
  decide_tac
 ) >>
 res_tac >>
 irule bigstep_stmt_seq_exec_sound_n_first >>
 gs[]
) >- (

 (* trans *)
 gs[bigstep_stmt_exec_def] >>
 rpt strip_tac >>
 Cases_on ‘bigstep_e_exec (top_scope::(scope_list ++ [g_scope1; g_scope2])) (INL e) n'’ >> (
  gs[]
 ) >>
 PairCases_on ‘x’ >>
 gs[] >>
 Cases_on ‘x0’ >> (
  gs[]
 ) >>
 gvs[] >>
 FULL_SIMP_TAC pure_ss [GSYM APPEND, Once arithmeticTheory.ADD_SYM] >>
 imp_res_tac bigstep_e_exec_sound_n_INL_zero >>
 qpat_x_assum ‘!ctx. _’ (fn thm => ASSUME_TAC (Q.SPEC ‘(apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)’ thm)) >>
 imp_res_tac bigstep_stmt_trans_exec_sound_n >>
 gvs[] >>
 irule scope_lists_separate >>
 gs[]
) >- (

 (* apply *)
 gs[bigstep_stmt_exec_def] >>
 rpt strip_tac >>
 Cases_on ‘bigstep_e_exec (top_scope::(scope_list ++ [g_scope1; g_scope2])) (INR l) n'’ >> (
  gs[]
 ) >>
 PairCases_on ‘x’ >>
 gs[] >>
 Cases_on ‘x0’ >> (
  gs[]
 ) >>
 gvs[] >>
 FULL_SIMP_TAC pure_ss [GSYM APPEND, Once arithmeticTheory.ADD_SYM] >>
 (* Need INR version of bigstep_e_exec_sound_n_INL_zero *)
 imp_res_tac bigstep_e_exec_sound_n_INR_zero >>
 qpat_x_assum ‘!ctx. _’ (fn thm => ASSUME_TAC (Q.SPEC ‘(apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)’ thm)) >>
 imp_res_tac bigstep_stmt_app_exec_sound_n >>
 gvs[] >>
 irule scope_lists_separate >>
 gs[]
) >- (

 (* extern *)
 gs[stmt_multi_exec'_def, bigstep_stmt_exec_def, stmt_multi_exec'_check_state_def] >>
 rpt strip_tac >> (
  subgoal ‘n = 0’ >- (
   decide_tac
  ) >>
  fs[separate_def, SUC_ADD_ONE, stmt_multi_exec'_def, stmt_multi_exec'_check_state_def] >>
  fs[GSYM SUC_ADD_ONE, oDROP_def, oTAKE_def, oDROP_APPEND, oTAKE_APPEND]
 )
)
QED

Theorem stmt_multi_exec'_stmt_stack:
!n scope_list scope_list' funn ascope stmt stmt' stmts top_scope g_scope1 g_scope2 g_scope_list' ctx.
 stmt_multi_exec' (ctx:'a ctx) (ascope:'a, [g_scope1; g_scope2]:g_scope_list, [(funn, [stmt], (top_scope::scope_list))], status_running) n = SOME (ascope, g_scope_list', [(funn, [stmt'], scope_list')], status_running) ==>
 stmt_multi_exec' (ctx:'a ctx) (ascope:'a, [g_scope1; g_scope2]:g_scope_list, [(funn, stmt::stmts, (top_scope::scope_list))], status_running) n = SOME (ascope, g_scope_list', [(funn, stmt'::stmts, scope_list')], status_running)
Proof
Induct_on ‘n’ >- (
 gs[stmt_multi_exec'_def, stmt_multi_exec'_check_state_def]
) >>
rpt strip_tac >>
gs[stmt_multi_exec'_def] >>
Cases_on ‘stmt_multi_exec' ctx
             (ascope,[g_scope1; g_scope2],
              [(funn,[stmt],top_scope::scope_list)],status_running) n’ >> (
 gs[]
) >>
PairCases_on ‘x’ >>
Cases_on ‘stmt_exec ctx (x0,x1,x2,x3)’ >> (
 gs[]
) >>
PairCases_on ‘x’ >>
imp_res_tac stmt_multi_exec'_check_state_second >>
subgoal ‘x0 = ascope /\ ?g_scope1'' g_scope2''. x1 = [g_scope1''; g_scope2''] /\ ?stmt' scope_list'. x2 = [(funn, [stmt'], scope_list')] /\ x3 = status_running’ >- (
 imp_res_tac stmt_multi_exec'_SOME_imp >>
 gs[]
) >>
gvs[] >>
res_tac >>
fs[] >>
imp_res_tac stmt_exec_lemma >>
gs[stmt_multi_exec'_check_state_def]
QED

Definition funn_is_local_or_global_def:
 (funn_is_local_or_global (func_map:func_map) (b_func_map:b_func_map) funn =
  case funn of
  | funn_name x =>
   (case ALOOKUP func_map x of
    | NONE => IS_SOME $ ALOOKUP b_func_map x
    | _ => T)
  | _ => F
)
End

Definition in_local_fun_def:
 (in_local_fun (func_map:func_map) (b_func_map:b_func_map) (arch_frame_list_regular [(funn_name fname, stmt_stack, scope_list)]) =
  ((scope_list <> []) /\
   (ALOOKUP func_map fname = NONE) /\ (IS_SOME $ ALOOKUP b_func_map fname))) /\
 (in_local_fun func_map b_func_map (arch_frame_list_regular ((funn_name fname, stmt_stack, scope_list)::frame_list)) =
  ((scope_list <> []) /\
   (ALOOKUP func_map fname = NONE) /\ (IS_SOME $ ALOOKUP b_func_map fname))) /\
 (in_local_fun _ _ _ = F)
End

(* Since stmt_exec yields NONE for execution starting in scope_list that is empty,
 * and since the big-step semantics does not check the length of scope_list, a
 * non-emptiness requirement on scope_list has been added here *)
Definition in_local_fun'_def:
 (in_local_fun' ((ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map):'a actx) i (arch_frame_list_regular [(funn_name fname, stmt_stack, scope_list)]) n =
  ((scope_list <> []) /\
   (ALOOKUP func_map fname = NONE) /\
   (case EL i ab_list of
    | arch_block_pbl x el =>
     (case ALOOKUP pblock_map x of
      | SOME (pbl_type,x_d_list,b_func_map,decl_list,pars_map,tbl_map) =>
       IS_SOME $ ALOOKUP b_func_map fname
      | NONE => F)
    | _ => F) /\
   n <> 0)) /\
 (in_local_fun' ((ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map):'a actx) i (arch_frame_list_regular ((funn_name fname, stmt_stack, scope_list)::frame_list)) n =
  ((scope_list <> []) /\
   (ALOOKUP func_map fname = NONE) /\
   (case EL i ab_list of
    | arch_block_pbl x el =>
     (case ALOOKUP pblock_map x of
      | SOME (pbl_type,x_d_list,b_func_map,decl_list,pars_map,tbl_map) =>
       IS_SOME $ ALOOKUP b_func_map fname
      | NONE => F)
    | _ => F) /\
   n <> 0)) /\
 (in_local_fun' ctx _ _ _ = F)
End

Theorem in_local_fun'_imp:
!(ctx:'a actx) i arch_frame_list n.
in_local_fun' ctx i arch_frame_list n ==> n <> 0
Proof
rpt strip_tac >>
PairCases_on ‘ctx’ >>
Cases_on ‘arch_frame_list’ >> (
 gs[in_local_fun'_def]
) >>
Cases_on ‘l’ >> (
 gs[in_local_fun'_def]
) >>
PairCases_on ‘h’ >>
Cases_on ‘h0’ >> (
 gs[in_local_fun'_def]
) >>
Cases_on ‘t’ >> (
 gs[in_local_fun'_def]
)
QED

Theorem bigstep_arch_exec_zero:
!g_scope_list arch_frame_list g_scope_list' arch_frame_list'.
bigstep_arch_exec (NONE:('a actx # b_func_map) option) g_scope_list arch_frame_list =
 SOME (g_scope_list',arch_frame_list',0) ==>
g_scope_list = g_scope_list' /\ arch_frame_list = arch_frame_list'
Proof
rpt gen_tac >>
rpt disch_tac >>
Cases_on ‘g_scope_list’ >> (
 gs[bigstep_arch_exec_def]
) >>
Cases_on ‘t’ >> (
 gs[bigstep_arch_exec_def]
) >>
Cases_on ‘t'’ >> Cases_on ‘arch_frame_list’ >> (
 gs[bigstep_arch_exec_def]
) >>
Cases_on ‘l’ >> (
 gs[bigstep_arch_exec_def]
) >>
PairCases_on ‘h''’ >>
gs[] >>
Cases_on ‘h''1’ >> (
 gs[]
) >>
gs[bigstep_exec_def] >>
rpt strip_tac >> (
 Cases_on ‘bigstep_stmt_exec NONE (h''2 ++ [h; h']) h'' 0’ >> (
  gs[]
 ) >>
 PairCases_on ‘x’ >> (
  gs[]
 ) >>
 Cases_on ‘separate x1’ >> (
  gs[]
 ) >>
 Cases_on ‘q’ >> (
  gs[]
 ) >>
 Cases_on ‘r’ >> (
  gs[]
 ) >>
 rw[] >>
 imp_res_tac bigstep_stmt_exec_imp >>
 gvs[separate_def, oDROP_APPEND, oTAKE_APPEND]
)
QED

Definition arch_exec_init_sane_def:
 arch_exec_init_sane
  ((ab_list,pblock_map,ffblock_map,input_f,output_f,copyin_pbl,copyout_pbl,
    apply_table_f,ext_map,func_map):'a actx)
  ((i,in_out_list,in_out_list',scope):'a aenv) g_scope_list (frame_list:frame_list) status =
?funn stmt_stack scope_list frame_list'.
 frame_list = ((funn,stmt_stack,scope_list)::frame_list') /\
 ?x el.
  EL i ab_list = arch_block_pbl x el /\
  ?pbl_type x_d_list b_func_map decl_list pars_map tbl_map.
   ALOOKUP pblock_map x =
    SOME (pbl_type,x_d_list,b_func_map,decl_list,pars_map,tbl_map) /\
   ~state_fin_exec status ((funn,stmt_stack,scope_list)::frame_list') /\
   (map_to_pass funn b_func_map <> NONE) /\
   (tbl_to_pass funn b_func_map tbl_map <> NONE) /\
   (?g_scope_list''.
    scopes_to_pass funn func_map b_func_map g_scope_list =
     SOME g_scope_list'')
End

(* The properties of the result that follow from bigstep_arch_exec yielding a
 * SOME result. *)
Theorem bigstep_arch_exec_SOME_imp:
!ctx_b_func_map_opt g_scope_list g_scope_list' arch_frame_list arch_frame_list' n.
bigstep_arch_exec ctx_b_func_map_opt g_scope_list arch_frame_list = SOME (g_scope_list', arch_frame_list', n) ==>
(?g_scope1 g_scope2.
 g_scope_list = [g_scope1; g_scope2]) /\
(?frame_list. arch_frame_list = arch_frame_list_regular frame_list) /\
(* TODO: Holds, but not needed for now... 
(?g_scope1' g_scope2'.
 g_scope_list' = [g_scope1'; g_scope2']) /\
*)
(?frame_list'. arch_frame_list' = arch_frame_list_regular frame_list')
Proof
rpt gen_tac >>
rpt disch_tac >>
Cases_on ‘g_scope_list’ >- (
 gs[bigstep_arch_exec_def]
) >>
Cases_on ‘t’ >- (
 gs[bigstep_arch_exec_def]
) >>
gs[] >>
Cases_on ‘arch_frame_list’ >> (
 gs[bigstep_arch_exec_def]
) >>
Cases_on ‘t'’ >> (
 gs[bigstep_arch_exec_def]
) >>
Cases_on ‘l’ >> (
 gs[]
) >>
PairCases_on ‘h''’ >>
gs[] >>
Cases_on ‘h''1’ >> (
 gs[]
) >>
Cases_on ‘bigstep_exec
             (case ctx_b_func_map_opt of
                NONE => NONE
              | SOME
                ((ab_list,pblock_map,ffblock_map,input_f,output_f,copyin_pbl,
                  copyout_pbl,apply_table_f,ext_map,func_map),b_func_map) =>
                SOME (func_map,b_func_map,ext_map)) ([h; h'],h''2)
             h''’ >> (
 gs[]
) >>
PairCases_on ‘x’ >>
gs[] >>
metis_tac[]
QED

Theorem bigstep_arch_exec'_SOME_imp:
!ctx_b_func_map_opt g_scope_list g_scope_list' arch_frame_list arch_frame_list' n.
bigstep_arch_exec' ctx_b_func_map_opt g_scope_list arch_frame_list = SOME (g_scope_list', arch_frame_list', n) ==>
(?g_scope1 g_scope2.
 g_scope_list = [g_scope1; g_scope2]) /\
(?frame_list. arch_frame_list = arch_frame_list_regular frame_list) /\
(* TODO: Holds, but not needed for now... 
(?g_scope1' g_scope2'.
 g_scope_list' = [g_scope1'; g_scope2']) /\
*)
(?frame_list'. arch_frame_list' = arch_frame_list_regular frame_list')
Proof
rpt gen_tac >>
rpt disch_tac >>
Cases_on ‘g_scope_list’ >> (
 gs[bigstep_arch_exec'_def]
) >>
Cases_on ‘t’ >> (
 gs[bigstep_arch_exec'_def]
) >>
Cases_on ‘arch_frame_list’ >> (
 gs[bigstep_arch_exec'_def]
) >>
Cases_on ‘t'’ >> (
 gvs[bigstep_arch_exec'_def, AllCaseEqs()]
) >> (
 metis_tac[bigstep_arch_exec_SOME_imp]
)
QED

Definition arch_multi_exec'_def:
 (arch_multi_exec' _ astate 0 = SOME astate)
 /\
 (arch_multi_exec' (actx:'a actx) astate (SUC fuel) =
  case arch_multi_exec' actx astate fuel of
  | SOME astate' =>
   arch_exec actx astate'
  | _ => NONE)
End

Theorem bigstep_arch_exec_sound_n_stmt:
!n h g_scope1 g_scope2 x0 g_scope_list' x2 ab_list pblock_map ffblock_map input_f output_f copyin_pbl copyout_pbl apply_table_f ext_map func_map b_func_map pars_map tbl_map i in_out_list in_out_list' ascope funn h' t t' t'' x' el pbl_type x_d_list decl_list.

EL i ab_list = arch_block_pbl x' el ==>
ALOOKUP pblock_map x' = SOME (pbl_type,x_d_list,b_func_map,decl_list,pars_map,tbl_map) ==>
in_local_fun func_map b_func_map (arch_frame_list_regular [(funn,x0::t',x2)]) ==>

 stmt_multi_exec' ((apply_table_f, ext_map, func_map, b_func_map, pars_map, tbl_map):'a ctx) (ascope, [g_scope1; g_scope2]:g_scope_list, [(funn,h::t',h'::t'')], status_running) n =
 SOME (ascope,g_scope_list',[(funn, x0::t', x2)],status_running) ==>
 arch_multi_exec' ((ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map):'a actx)
  ((i,in_out_list,in_out_list',ascope),[g_scope1; g_scope2],
   arch_frame_list_regular ((funn,h::t',h'::t'')::t),status_running) n =
   SOME
    ((i,in_out_list,in_out_list',ascope),g_scope_list',arch_frame_list_regular ((funn,x0::t',x2)::t),
     status_running)
Proof
Induct_on ‘n’ >> (
 rpt strip_tac >>
 gs[arch_multi_exec'_def, stmt_multi_exec'_def, stmt_multi_exec'_check_state_def]
) >>
Cases_on ‘stmt_multi_exec' (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)
            (ascope,[g_scope1; g_scope2],[(funn,h::t',h'::t'')],status_running)
            n’ >> (
 gs[]
) >>
PairCases_on ‘x’ >>
gs[] >>
subgoal ‘x0' = ascope /\
         ?g_scope1' g_scope2'. x1 = [g_scope1'; g_scope2'] /\
         ?stmt' scope_list'. x2' = [(funn,stmt'::t',scope_list')] /\
         x3 = status_running ’ >- (
 imp_res_tac stmt_multi_exec'_SOME_imp >>
 gs[]
) >>
gs[] >>
Cases_on ‘stmt_exec (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)
            (ascope,[g_scope1'; g_scope2'],[(funn,stmt'::t',scope_list')],
             status_running)’ >> (
 gs[]
) >>
imp_res_tac stmt_multi_exec'_check_state_second >>
gvs[] >>
subgoal ‘in_local_fun
         func_map b_func_map
         (arch_frame_list_regular [(funn,stmt'::t',scope_list')])’ >- (
 Cases_on ‘funn’ >> (
  gs[in_local_fun_def]
 ) >>
 imp_res_tac stmt_multi_exec'_SOME_imp >>
 Cases_on ‘scope_list''’ >> (
  gs[]
 )
) >>
res_tac >>
fs[arch_exec_def] >>
Cases_on ‘t’ >> (
 gs[]
) >- (
 gs[frames_exec_def] >>
 (* From top-level soundness theorem/ composition theorem *)
 subgoal ‘~state_fin_exec status_running [(funn,stmt'::t',scope_list')]’ >- (
  gs[state_fin_exec_def] >>
  Cases_on ‘stmt'’ >> (
   gs[]
  ) >>
  Cases_on ‘t'’ >> (
   gs[]
  ) >>
  Cases_on ‘scope_list'’ >> (
   gs[stmt_exec_def]
  )
 ) >>
 gs[] >>
 (* Needs all the to-pass information + identification of components of stmt_exec
  * possibly that scope_list' is non-empty *)
 (* Since we're in a local function - get this premise from above *)
 subgoal ‘scopes_to_pass funn func_map b_func_map [g_scope1'; g_scope2'] = SOME [g_scope1'; g_scope2'] /\
          (map_to_pass funn b_func_map = SOME b_func_map /\
           tbl_to_pass funn b_func_map tbl_map = SOME tbl_map)
            ’ >- (
  Cases_on ‘funn’ >> (
   gs[in_local_fun_def, scopes_to_pass_def, map_to_pass_def, tbl_to_pass_def]
  ) >>
  Cases_on ‘ALOOKUP b_func_map s’ >> (
   gs[]
  )
 ) >>
 gs[] >>
 gvs[] >>
 subgoal ‘scopes_to_retrieve funn func_map b_func_map [g_scope1'; g_scope2']
               [g_scope1''; g_scope2''] = SOME [g_scope1''; g_scope2'']’ >- (
  Cases_on ‘funn’ >> (
   gs[in_local_fun_def, scopes_to_retrieve_def]
  ) >>
  CASE_TAC
 ) >>
 gs[]
) >>
PairCases_on ‘h''’ >>
gs[frames_exec_def, state_fin_exec_def] >>
(* Needs all the to-pass information + identification of components of stmt_exec
 * possibly that scope_list' is non-empty *)
gvs[] >>
subgoal ‘scopes_to_pass funn func_map b_func_map [g_scope1'; g_scope2'] = SOME [g_scope1'; g_scope2'] /\
          map_to_pass funn b_func_map = SOME b_func_map /\
          tbl_to_pass funn b_func_map tbl_map = SOME tbl_map’ >- (
 Cases_on ‘funn’ >> (
  gs[in_local_fun_def, scopes_to_pass_def, map_to_pass_def, tbl_to_pass_def]
 ) >>
 Cases_on ‘ALOOKUP b_func_map s’ >> (
  gs[]
 )
) >>
subgoal ‘scopes_to_retrieve funn func_map b_func_map [g_scope1'; g_scope2']
              [g_scope1''; g_scope2''] = SOME [g_scope1''; g_scope2'']’ >- (
 Cases_on ‘funn’ >> (
  gs[in_local_fun_def, scopes_to_retrieve_def]
 ) >>
 CASE_TAC
) >>
gs[]
QED

Theorem bigstep_arch_exec_sound_n:
!n func_map g_scope_list g_scope_list' frame_list frame_list' x el pbl_type x_d_list b_func_map decl_list pars_map tbl_map ab_list pblock_map ffblock_map input_f output_f copyin_pbl
           copyout_pbl apply_table_f ext_map i in_out_list in_out_list' ascope.

EL i ab_list = arch_block_pbl x el ==>
ALOOKUP pblock_map x = SOME (pbl_type,x_d_list,b_func_map,decl_list,pars_map,tbl_map) ==>
in_local_fun func_map b_func_map (arch_frame_list_regular frame_list) ==>

bigstep_arch_exec (NONE:('a actx # b_func_map) option) g_scope_list (arch_frame_list_regular frame_list) = SOME (g_scope_list', (arch_frame_list_regular frame_list'), n) ==>
arch_multi_exec' ((ab_list,pblock_map,ffblock_map,input_f,output_f,copyin_pbl,
           copyout_pbl,apply_table_f,ext_map,func_map):'a actx) (((i,in_out_list,in_out_list',ascope):'a aenv), g_scope_list, arch_frame_list_regular frame_list, status_running) n = SOME ((i,in_out_list,in_out_list',ascope), g_scope_list', arch_frame_list_regular frame_list', status_running)
Proof
Cases_on ‘frame_list’ >- (
 rpt strip_tac >>
 imp_res_tac bigstep_arch_exec_SOME_imp >>
 gs[bigstep_arch_exec_def]
) >>
rpt strip_tac >>
imp_res_tac bigstep_arch_exec_SOME_imp >>
gs[arch_multi_exec'_def, bigstep_arch_exec_def] >>
Cases_on ‘frame_list’ >> (
 gs[]
) >>
PairCases_on ‘h'’ >>
gs[] >>
Cases_on ‘h'1’ >> (
 gs[]
) >>
Cases_on ‘bigstep_exec NONE ([g_scope1; g_scope2],h'2) h'’ >> (
 gs[]
) >>
PairCases_on ‘x'’ >>
gs[] >>
gvs[] >>
gs[bigstep_exec_def] >>
Cases_on ‘bigstep_stmt_exec NONE (h'2 ++ [g_scope1; g_scope2]) h' 0’ >> (
 gs[]
) >>
PairCases_on ‘x'’ >>
gs[] >>
Cases_on ‘separate x'1’ >> (
 gs[]
) >>
Cases_on ‘q’ >> (
 gs[]
) >>
Cases_on ‘r’ >> (
 gs[]
) >>
gvs[] >>
(* Scope list non-empty should probably be added to in_local_fun' assumption, which can then be passed along to this theorem *)
Cases_on ‘h'2’ >- (
 Cases_on ‘h'0’ >> (
  gs[in_local_fun_def]
 ) >>
 Cases_on ‘t’ >> (
  gs[in_local_fun_def]
 )
) >>
imp_res_tac (SIMP_RULE std_ss [] $ Q.SPECL [‘n’, ‘0’] bigstep_stmt_exec_sound_n) >>
gs[] >>
res_tac >>
irule bigstep_arch_exec_sound_n_stmt >>
Cases_on ‘h'0’ >> (
 gs[in_local_fun_def]
) >>
strip_tac >- (
 metis_tac[stmt_multi_exec'_stmt_stack]
) >>
Cases_on ‘t’ >> (
 gs[in_local_fun_def] >>
 qpat_x_assum ‘!funn. _’ (fn thm => ASSUME_TAC (Q.SPECL [‘funn’, ‘ctx’, ‘ascope’] thm)) >>
 imp_res_tac stmt_multi_exec'_SOME_imp >>
 Cases_on ‘scope_list'’ >> (
  gs[]
 )
)
QED

Theorem bigstep_arch_exec'_sound_n:
!n func_map g_scope_list g_scope_list' frame_list frame_list' x el pbl_type x_d_list b_func_map decl_list pars_map tbl_map ab_list pblock_map ffblock_map input_f output_f copyin_pbl
           copyout_pbl apply_table_f ext_map i in_out_list in_out_list' ascope.

EL i ab_list = arch_block_pbl x el ==>
ALOOKUP pblock_map x = SOME (pbl_type,x_d_list,b_func_map,decl_list,pars_map,tbl_map) ==>
in_local_fun func_map b_func_map (arch_frame_list_regular frame_list) ==>

bigstep_arch_exec' (SOME ((i,in_out_list,in_out_list',ascope),(ab_list,pblock_map,ffblock_map,input_f,output_f,copyin_pbl,copyout_pbl,apply_table_f,ext_map,func_map))) g_scope_list (arch_frame_list_regular frame_list) = SOME (g_scope_list', (arch_frame_list_regular frame_list'), n) ==>
arch_multi_exec' ((ab_list,pblock_map,ffblock_map,input_f,output_f,copyin_pbl,
           copyout_pbl,apply_table_f,ext_map,func_map):'a actx) (((i,in_out_list,in_out_list',ascope):'a aenv), g_scope_list, arch_frame_list_regular frame_list, status_running) n = SOME ((i,in_out_list,in_out_list',ascope), g_scope_list', arch_frame_list_regular frame_list', status_running)
Proof
Cases_on ‘frame_list’ >- (
 rpt strip_tac >>
 imp_res_tac bigstep_arch_exec'_SOME_imp >>
 gs[bigstep_arch_exec'_def, bigstep_arch_exec_def]
) >>
rpt strip_tac >>
imp_res_tac bigstep_arch_exec'_SOME_imp >>
gs[arch_multi_exec'_def, bigstep_arch_exec'_def, bigstep_arch_exec_def] >>
Cases_on ‘frame_list’ >> (
 gs[]
) >>
PairCases_on ‘h'’ >>
gs[] >>
Cases_on ‘h'1’ >> (
 gs[]
) >>
Cases_on ‘bigstep_exec (SOME (func_map,b_func_map,ext_map)) ([g_scope1; g_scope2],h'2) h'’ >> (
 gs[]
) >>
PairCases_on ‘x'’ >>
gs[] >>
gvs[] >>
gs[bigstep_exec_def] >>
Cases_on ‘bigstep_stmt_exec (SOME (func_map,b_func_map,ext_map)) (h'2 ++ [g_scope1; g_scope2]) h' 0’ >> (
 gs[]
) >>
PairCases_on ‘x'’ >>
gs[] >>
Cases_on ‘separate x'1’ >> (
 gs[]
) >>
Cases_on ‘q’ >> (
 gs[]
) >>
Cases_on ‘r’ >> (
 gs[]
) >>
gvs[] >>
(* Scope list non-empty should probably be added to in_local_fun' assumption, which can then be passed along to this theorem *)
Cases_on ‘h'2’ >- (
 Cases_on ‘h'0’ >> (
  gs[in_local_fun_def]
 ) >>
 Cases_on ‘t’ >> (
  gs[in_local_fun_def]
 )
) >>
imp_res_tac (SIMP_RULE std_ss [] $ Q.SPECL [‘n’, ‘0’] bigstep_stmt_exec_SOME_sound_n) >>
gs[] >>
res_tac >>
irule bigstep_arch_exec_sound_n_stmt >>
Cases_on ‘h'0’ >> (
 gs[in_local_fun_def]
) >>
strip_tac >- (
 metis_tac[stmt_multi_exec'_stmt_stack]
) >>
Cases_on ‘t’ >> (
 gs[in_local_fun_def] >>
 qpat_x_assum ‘!tbl_map. _’ (fn thm => ASSUME_TAC (Q.SPECL [‘tbl_map’, ‘pars_map’, ‘funn’, ‘ascope’, ‘apply_table_f’] thm)) >>
 imp_res_tac stmt_multi_exec'_SOME_imp >>
 Cases_on ‘scope_list'’ >> (
  gs[]
 )
)
QED

Theorem arch_multi_exec'_sound:
!n g_scope_list g_scope_list' frame_list arch_frame_list' aenv aenv' actx status'.
arch_multi_exec' (actx:'a actx) ((aenv:'a aenv), g_scope_list, arch_frame_list_regular frame_list, status_running) n = SOME (aenv', g_scope_list', arch_frame_list', status') ==>
arch_multi_exec (actx:'a actx) (aenv, g_scope_list, arch_frame_list_regular frame_list, status_running) n = SOME (aenv', g_scope_list', arch_frame_list', status')
Proof
Induct_on ‘n’ >- (
 rpt strip_tac >>
 gs[arch_multi_exec'_def, arch_multi_exec_def]
) >>
rpt strip_tac >>
gs[arch_multi_exec'_def] >>
Cases_on ‘arch_multi_exec' actx
             (aenv,g_scope_list,arch_frame_list_regular frame_list,
              status_running) n’ >> (
 gs[]
) >>
PairCases_on ‘x’ >>
res_tac >>
(* Use theorem to split execution of arch_multi_exec into 1+n *)
FULL_SIMP_TAC pure_ss [SUC_ADD_ONE, Once arithmeticTheory.ADD_SYM] >>
FULL_SIMP_TAC pure_ss [arch_multi_exec_add, Once arithmeticTheory.ONE] >>
gs[arch_multi_exec_def]
QED

Theorem arch_multi_exec_sound:
!n g_scope_list g_scope_list' frame_list arch_frame_list' aenv aenv' actx status' .
arch_multi_exec (actx:'a actx) ((aenv:'a aenv), g_scope_list, arch_frame_list_regular frame_list, status_running) n = SOME (aenv', g_scope_list', arch_frame_list', status') ==>
arch_multi_exec' (actx:'a actx) (aenv, g_scope_list, arch_frame_list_regular frame_list, status_running) n = SOME (aenv', g_scope_list', arch_frame_list', status')
Proof
Induct_on ‘n’ >- (
 rpt strip_tac >>
 gs[arch_multi_exec'_def, arch_multi_exec_def]
) >>
rpt strip_tac >>
FULL_SIMP_TAC pure_ss [SUC_ADD_ONE, Once arithmeticTheory.ADD_SYM] >>
FULL_SIMP_TAC pure_ss [arch_multi_exec_add, Once arithmeticTheory.ONE] >>
Cases_on ‘arch_multi_exec actx
             (aenv,g_scope_list,arch_frame_list_regular frame_list,
              status_running) n’ >> (
 gs[]
) >>
PairCases_on ‘x’ >>
res_tac >>
fs[arch_multi_exec'_def, GSYM SUC_ADD_ONE] >>
FULL_SIMP_TAC pure_ss [Once arithmeticTheory.ONE] >>
gs[arch_multi_exec_def] >>
Cases_on ‘arch_exec actx ((x0,x1,x2,x3),x4,x5,x6)’ >> (
 gs[]
) >>
PairCases_on ‘x’ >>
gs[]
QED

Theorem bigstep_arch_exec_comp'_NONE:
!n' n assl ctx g_scope_list arch_frame_list i in_out_list in_out_list' ascope g_scope_list' g_scope_list'' arch_frame_list' arch_frame_list'' aenv.
(assl ==> arch_multi_exec ctx (aenv, g_scope_list, arch_frame_list, status_running) n = SOME ((i,in_out_list,in_out_list',ascope), g_scope_list', arch_frame_list', status_running)) ==>
in_local_fun' (ctx:'a actx) i arch_frame_list' n ==>
bigstep_arch_exec (NONE:('a actx # b_func_map) option) (g_scope_list':g_scope_list) arch_frame_list' = SOME (g_scope_list'', arch_frame_list'', n') ==>
(assl ==> arch_multi_exec ctx (aenv, g_scope_list, arch_frame_list, status_running) (n+n') = SOME ((i,in_out_list,in_out_list',ascope), g_scope_list'', arch_frame_list'', status_running))
Proof
rpt strip_tac >>
irule arch_multi_exec_comp_n_tl >>
imp_res_tac bigstep_arch_exec_SOME_imp >>
gvs[] >>
PairCases_on ‘ctx’ >>
subgoal ‘?x el. EL i ctx0 = arch_block_pbl x el /\
         ?pbl_type x_d_list b_func_map decl_list pars_map tbl_map.
          ALOOKUP ctx1 x =
           SOME (pbl_type,x_d_list,b_func_map,decl_list,pars_map,tbl_map)’ >- (
 imp_res_tac in_local_fun'_imp >>
 Cases_on ‘n’ >> (
  gs[]
 ) >>
 imp_res_tac arch_multi_exec_arch_frame_list_regular >>
 metis_tac[]
) >>
subgoal ‘in_local_fun ctx9 b_func_map (arch_frame_list_regular frame_list)’ >- (
 Cases_on ‘frame_list’ >> (
  gs[in_local_fun'_def, in_local_fun_def]
 ) >>
 PairCases_on ‘h’ >>
 Cases_on ‘h0’ >> (
  gs[in_local_fun'_def, in_local_fun_def]
 ) >>
 Cases_on ‘t’ >> (
  gs[in_local_fun'_def, in_local_fun_def]
 )
) >>
imp_res_tac bigstep_arch_exec_sound_n >>
metis_tac[arch_multi_exec'_sound]
QED

Theorem bigstep_arch_exec_comp'_NONE_conj:
!n' n assl ctx g_scope_list arch_frame_list i in_out_list in_out_list' ascope g_scope_list' g_scope_list'' arch_frame_list' arch_frame_list'' aenv.
((assl ==> arch_multi_exec ctx (aenv, g_scope_list, arch_frame_list, status_running) n = SOME ((i,in_out_list,in_out_list',ascope), g_scope_list', arch_frame_list', status_running)) /\
in_local_fun' (ctx:'a actx) i arch_frame_list' n /\
bigstep_arch_exec (NONE:('a actx # b_func_map) option) (g_scope_list':g_scope_list) arch_frame_list' = SOME (g_scope_list'', arch_frame_list'', n')) ==>
(assl ==> arch_multi_exec ctx (aenv, g_scope_list, arch_frame_list, status_running) (n+n') = SOME ((i,in_out_list,in_out_list',ascope), g_scope_list'', arch_frame_list'', status_running))
Proof
metis_tac[bigstep_arch_exec_comp'_NONE]
QED

Theorem bigstep_arch_exec_comp'_SOME:
!assl ctx g_scope_list arch_frame_list i in_out_list in_out_list' ascope g_scope_list' g_scope_list'' n' arch_frame_list' arch_frame_list'' n aenv.
(assl ==> arch_multi_exec ctx (aenv, g_scope_list, arch_frame_list, status_running) n = SOME ((i,in_out_list,in_out_list',ascope), g_scope_list', arch_frame_list', status_running)) ==>
in_local_fun' ctx i arch_frame_list' n ==>
bigstep_arch_exec' (SOME ((i,in_out_list,in_out_list',ascope), ctx)) (g_scope_list':g_scope_list) arch_frame_list' = SOME (g_scope_list'', arch_frame_list'', n') ==>
(assl ==> arch_multi_exec ctx (aenv, g_scope_list, arch_frame_list, status_running) (n+n') = SOME ((i,in_out_list,in_out_list',ascope), g_scope_list'', arch_frame_list'', status_running))
Proof
rpt strip_tac >>
irule arch_multi_exec_comp_n_tl >>
imp_res_tac bigstep_arch_exec'_SOME_imp >>
gvs[] >>
PairCases_on ‘ctx’ >>
subgoal ‘?x el. EL i ctx0 = arch_block_pbl x el /\
         ?pbl_type x_d_list b_func_map decl_list pars_map tbl_map.
          ALOOKUP ctx1 x =
           SOME (pbl_type,x_d_list,b_func_map,decl_list,pars_map,tbl_map)’ >- (
 imp_res_tac in_local_fun'_imp >>
 Cases_on ‘n’ >> (
  gs[]
 ) >>
 imp_res_tac arch_multi_exec_arch_frame_list_regular >>
 metis_tac[]
) >>
subgoal ‘in_local_fun ctx9 b_func_map (arch_frame_list_regular frame_list)’ >- (
 Cases_on ‘frame_list’ >> (
  gs[in_local_fun'_def, in_local_fun_def]
 ) >>
 PairCases_on ‘h’ >>
 Cases_on ‘h0’ >> (
  gs[in_local_fun'_def, in_local_fun_def]
 ) >>
 Cases_on ‘t’ >> (
  gs[in_local_fun'_def, in_local_fun_def]
 )
) >>
imp_res_tac bigstep_arch_exec'_sound_n >>
metis_tac[arch_multi_exec'_sound]
QED

Theorem bigstep_arch_exec_comp'_SOME_conj:
!assl ctx g_scope_list arch_frame_list status i in_out_list in_out_list' ascope g_scope_list' g_scope_list'' n' arch_frame_list' arch_frame_list'' n aenv.
((assl ==> arch_multi_exec ctx (aenv, g_scope_list, arch_frame_list, status_running) n = SOME ((i,in_out_list,in_out_list',ascope), g_scope_list', arch_frame_list', status_running)) /\
in_local_fun' ctx i arch_frame_list' n /\
bigstep_arch_exec' (SOME ((i,in_out_list,in_out_list',ascope), ctx)) (g_scope_list':g_scope_list) arch_frame_list' = SOME (g_scope_list'', arch_frame_list'', n')) ==>
(assl ==> arch_multi_exec ctx (aenv, g_scope_list, arch_frame_list, status_running) (n+n') = SOME ((i,in_out_list,in_out_list',ascope), g_scope_list'', arch_frame_list'', status_running))
Proof
metis_tac[bigstep_arch_exec_comp'_SOME]
QED

val _ = export_theory ();
