open HolKernel boolLib liteLib simpLib Parse bossLib;
open p4Theory p4_auxTheory p4_exec_semTheory;

val _ = new_theory "p4_bigstep";

(* This file contains a big-step semantics for a fragment of P4 that
 * contains mostly local instructions *)

(* The symbolic execution should attempt to use this when
 * then next statement to be reduced is stmt_empty, (stmt_seq stmt_ass _)
 * or (stmt_seq stmt_empty _) *)


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
fs[e_size_def] >>
Induct_on ‘x_e_l’ >> (
 fs[e_size_def]
) >>
rpt strip_tac >>
PairCases_on ‘h’ >>
fs[e_size_def]
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

(* NOTE: This can return no reductions in case the next item to be reduced in
 * e_l is a function call *)
Definition bigstep_f_arg_exec_def:
 (bigstep_f_arg_exec func_maps_opt scope_lists (funn, e_l) n =
  (case func_maps_opt of
   | SOME (func_map, b_func_map, ext_fun_map) =>
    (case lookup_funn_sig funn func_map b_func_map ext_fun_map of
     | SOME x_d_l =>
      bigstep_f_arg_exec_l scope_lists (ZIP (MAP SND x_d_l, e_l)) n
     | NONE => NONE)
   | NONE => SOME (e_l, n))
 )
End

Definition bigstep_stmt_exec_def:
 (bigstep_stmt_exec func_maps_opt scope_lists (stmt_ass lval e) n =
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
     | _ => NONE)))
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
     | _ => NONE)))
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

(* TODO: The result of this should be sound with respect to n steps of
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
(* TODO: Take whole ctx or just function maps? Whole ctx leads to faster composition,
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
(* Takes entire ctx, but no b_func_map. Hands over to bigstep_arch_exec when this has been sorted *)
(* TODO: Is an option type really necessary for the aenv, actx tuple? *)
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
 fs[e_size_def]
) >>
Induct_on ‘h’ >>
gen_tac >>
Induct_on ‘p_2’ >> (
 fs[e_size_def]
)
QED

Theorem bigstep_e_exec_var_REWR:
!scope_lists var n t' m v.
bigstep_e_exec scope_lists (INL (e_var var)) n = SOME (t',m) <=>
(m = n + 1 /\ ?v. SOME v =  lookup_vexp scope_lists var /\ t' = (INL $ e_v v))
Proof
rpt strip_tac >>
eq_tac >> (
 rpt strip_tac >>
 fs[bigstep_e_exec_def] >>
 Cases_on ‘lookup_vexp scope_lists var’ >> (
  fs[]
 )
)
QED

Theorem bigstep_e_exec_var_REWR:
!scope_lists var n t' m v.
bigstep_e_exec scope_lists (INL (e_var var)) n = SOME (t',m) <=>
 (m = n + 1 /\ ?v. SOME v =  lookup_vexp scope_lists var /\ t' = (INL $ e_v v))
Proof
rpt strip_tac >>
eq_tac >> (
 rpt strip_tac >>
 fs[bigstep_e_exec_def] >>
 Cases_on ‘lookup_vexp scope_lists var’ >> (
  fs[]
 )
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
 fs[bigstep_e_exec_def]
) >- (
 Cases_on ‘bigstep_e_exec scope_lists (INL x) n’ >> (
  fs[]
 ) >>
 PairCases_on ‘x'’ >>
 fs[] >>
 Cases_on ‘x'0’ >>
 fs[] >>
 Cases_on ‘is_v x'’ >> (
  fs[]
 ) >>
 Cases_on ‘e_exec_acc (e_acc x' s)’ >> (
  fs[]
 )
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
 fs[bigstep_e_exec_def]
) >>
Cases_on ‘bigstep_e_exec scope_lists (INL e) n’ >> (
 fs[]
) >>
PairCases_on ‘x’ >>
fs[] >>
Cases_on ‘x0’ >>
fs[] >>
Cases_on ‘is_v x’ >> (
 fs[]
) >>
Cases_on ‘e_exec_unop unop x’ >> (
 fs[]
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
 fs[bigstep_e_exec_def]
) >- (
 Cases_on ‘bigstep_e_exec scope_lists (INL x) n’ >> (
  fs[]
 ) >>
 PairCases_on ‘x'’ >>
 fs[] >>
 Cases_on ‘x'0’ >>
 fs[] >>
 Cases_on ‘is_v x'’ >> (
  fs[]
 ) >>
 Cases_on ‘e_exec_cast cast x'’ >> (
  fs[]
 )
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
 fs[bigstep_e_exec_def]
) >- (
 Cases_on ‘bigstep_e_exec scope_lists (INL e1) n’ >> (
  fs[]
 ) >>
 PairCases_on ‘x’ >>
 fs[] >>
 Cases_on ‘x0’ >>
 fs[] >>
 Cases_on ‘is_v x’ >> (
  fs[]
 ) >> (
  Cases_on ‘x’ >> (
   fs[is_v]
  )
 ) >>
 Cases_on ‘is_short_circuitable binop’ >> (
  fs[]
 ) >- (
  Cases_on ‘e_exec_short_circuit v binop e2’ >> (
   fs[]
  )
 ) >>
 Cases_on ‘bigstep_e_exec scope_lists (INL e2) x1’ >> (
  fs[]
 ) >>
 PairCases_on ‘x’ >>
 fs[] >>
 Cases_on ‘x0’ >>
 fs[] >>
 Cases_on ‘is_v x’ >> (
  fs[]
 ) >>
 Cases_on ‘e_exec_binop (e_v v) binop x’ >> (
  fs[]
 )
) >> (
 Cases_on ‘e1'’ >> (
  fs[is_v]
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
 fs[bigstep_e_exec_def]
) >>
Cases_on ‘bigstep_e_exec scope_lists (INL e1) n’ >> (
 fs[]
) >>
PairCases_on ‘x’ >>
fs[] >>
Cases_on ‘x0’ >>
fs[] >>
Cases_on ‘is_v_bit x’ >> (
 fs[]
) >>
Cases_on ‘bigstep_e_exec scope_lists (INL e2) x1’ >> (
 fs[]
) >>
PairCases_on ‘x'’ >>
fs[] >>
Cases_on ‘x'0’ >>
fs[] >>
Cases_on ‘is_v_bit x'’ >> (
 fs[]
) >>
Cases_on ‘e_exec_concat x x'’ >> (
 fs[]
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
 fs[bigstep_e_exec_def]
) >>
Cases_on ‘bigstep_e_exec scope_lists (INL e1) n’ >> (
 fs[]
) >>
PairCases_on ‘x’ >>
fs[] >>
Cases_on ‘x0’ >>
fs[] >>
Cases_on ‘is_v_bit x’ >> (
 fs[]
) >>
Cases_on ‘e_exec_slice x e2 e3’ >> (
 fs[]
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
 fs[bigstep_e_exec_def]
) >>
Cases_on ‘bigstep_e_exec scope_lists (INL e) n’ >> (
 fs[]
) >>
PairCases_on ‘x'’ >>
fs[] >>
Cases_on ‘x'0’ >>
fs[]
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
 fs [bigstep_e_exec_def]
) >- (
 Cases_on ‘bigstep_e_exec scope_lists (INR (MAP SND x_e_l)) n’ >> (
  fs[]
 ) >>
 PairCases_on ‘x’ >>
 fs[] >>
 Cases_on ‘x0’ >>
 fs[] >>
 Cases_on ‘EVERY is_v y’ >> (
  FULL_SIMP_TAC bool_ss []
 ) >> (
  fs[]
 )
) >>
subgoal ‘~EVERY is_v e_l'’ >- (
 fs[]
) >>
FULL_SIMP_TAC bool_ss []
QED

val bigstep_e_exec_ind_hyp_tac =
 PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
 fs[e_size_def] >>
 res_tac >>
 decide_tac
;

val bigstep_e_exec_2_ind_hyp_tac =
 PAT_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
 PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x')’] thm)) >>
 fs[e_size_def] >>
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
  fs[bigstep_e_exec_def],

  (* var *)
  fs[bigstep_e_exec_var_REWR],

  (* list *)
  fs[bigstep_e_exec_def],

  (* acc *)
  fs[bigstep_e_exec_acc_REWR] >>
  rpt strip_tac >> (
   bigstep_e_exec_ind_hyp_tac
  ),

  (* unop *)
  fs[bigstep_e_exec_unop_REWR] >>
  rpt strip_tac >> (
   bigstep_e_exec_ind_hyp_tac
  ),

  (* cast *)
  fs[bigstep_e_exec_cast_REWR] >>
  rpt strip_tac >> (
   bigstep_e_exec_ind_hyp_tac
  ),

  (* binop *)
  fs[bigstep_e_exec_binop_REWR] >>
  rpt strip_tac >- (
   bigstep_e_exec_ind_hyp_tac
  ) >- (
   bigstep_e_exec_2_ind_hyp_tac
  ) >- (
   bigstep_e_exec_2_ind_hyp_tac
  ) >>
  bigstep_e_exec_ind_hyp_tac,


  (* concat *)
  fs[bigstep_e_exec_concat_REWR] >>
  rpt strip_tac >- (
   bigstep_e_exec_2_ind_hyp_tac
  ) >- (
   bigstep_e_exec_2_ind_hyp_tac
  ) >>
  bigstep_e_exec_ind_hyp_tac,

  (* slice *)
  fs[bigstep_e_exec_slice_REWR] >>
  rpt strip_tac >> (
   bigstep_e_exec_ind_hyp_tac
  ),

  (* call *)
  fs[bigstep_e_exec_def],

  (* select *)
  fs[bigstep_e_exec_select_REWR] >>
  rpt strip_tac >>
  bigstep_e_exec_ind_hyp_tac,

  (* struct *)
  fs[bigstep_e_exec_struct_REWR] >>
  rpt strip_tac >> (
   PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INR (MAP SND (l:(string # e) list)))’] thm)) >>
   fs[e_size_def, e3_e1_size] >>
   res_tac >>
   decide_tac
  ),

  (* header *)
  fs[bigstep_e_exec_def]
 ]
(* INR *)
) >>
Induct_on ‘y’ >> (
 rpt strip_tac >>
 fs[bigstep_e_exec_def]
) >>
Cases_on ‘bigstep_e_exec scope_lists (INL h) n’ >> (
 fs[]
) >>
PairCases_on ‘x’ >>
fs[] >>
Cases_on ‘x0’ >>
fs[] >>
Cases_on ‘bigstep_e_exec scope_lists (INR y) x1’ >> (
 fs[]
) >- (
 PAT_ASSUM “!y'. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL h)’] thm)) >>
 fs[e_size_def] >>
 res_tac >>
 decide_tac
) >>
PairCases_on ‘x'’ >>
fs[] >>
Cases_on ‘x'0’ >>
fs[] >- (
 PAT_ASSUM “!y'. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL h)’] thm)) >>
 fs[e_size_def] >>
 res_tac >>
 decide_tac
) >>
PAT_ASSUM “!y'. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL h)’] thm)) >>
fs[e_size_def] >>
PAT_ASSUM “!y'. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INR y)’] thm)) >>
fs[e_size_def] >>
res_tac >>
Cases_on ‘is_v x’ >> (
 fs[]
)
QED

val bigstep_e_exec_unchanged_ind_hyp_tac =
 imp_res_tac bigstep_e_exec_incr >>
 PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
 fs[e_size_def] >>
 res_tac >>
 fs[]
;

val bigstep_e_exec_unchanged_2_ind_hyp_tac =
 imp_res_tac bigstep_e_exec_incr >>
 PAT_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
 PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x')’] thm)) >>
 fs[e_size_def] >>
 res_tac >>
 fs[]
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
  fs[bigstep_e_exec_def],

  (* var *)
  fs[bigstep_e_exec_var_REWR],

  (* list *)
  fs[bigstep_e_exec_def],

  (* acc *)
  fs[bigstep_e_exec_acc_REWR] >> (
   bigstep_e_exec_unchanged_ind_hyp_tac
  ),

  (* unop *)
  fs[bigstep_e_exec_unop_REWR] >> (
   bigstep_e_exec_unchanged_ind_hyp_tac
  ),

  (* cast *)
  fs[bigstep_e_exec_cast_REWR] >> (
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
   fs[]
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
   fs[]
  ) >>
  bigstep_e_exec_unchanged_ind_hyp_tac,

  (* slice *)
  fs[bigstep_e_exec_slice_REWR] >> (
   bigstep_e_exec_unchanged_ind_hyp_tac
  ),

  (* call *)
  fs[bigstep_e_exec_def],

  (* select *)
  fs[bigstep_e_exec_select_REWR] >>
  rpt strip_tac >>
  bigstep_e_exec_unchanged_ind_hyp_tac,

  (* struct *)
  fs[bigstep_e_exec_struct_REWR] >> (
   imp_res_tac bigstep_e_exec_incr >>
   PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INR (MAP SND (l:(string # e) list)))’] thm)) >>
   fs[e_size_def, e3_e1_size] >>
   res_tac >>
   gvs[GSYM ZIP_MAP_FST_SND]
  ),

  (* header *)
  fs[bigstep_e_exec_def]
 ]
(* INR *)
) >>
Induct_on ‘y’ >> (
 rpt strip_tac >>
 fs[bigstep_e_exec_def]
) >>
Cases_on ‘bigstep_e_exec scope_lists (INL h) n’ >> (
 fs[]
) >>
PairCases_on ‘x’ >>
fs[] >>
Cases_on ‘x0’ >>
fs[] >>
Cases_on ‘bigstep_e_exec scope_lists (INR y) x1’ >> (
 fs[]
) >- (
 PAT_ASSUM “!y'. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL h)’] thm)) >>
 gs[e_size_def] >>
 res_tac >>
 fs[]
) >>
PairCases_on ‘x'’ >>
fs[] >>
Cases_on ‘x'0’ >>
fs[] >- (
 PAT_ASSUM “!y'. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL h)’] thm)) >>
 gs[e_size_def] >>
 res_tac >>
 fs[]
) >>
imp_res_tac bigstep_e_exec_incr >>
PAT_ASSUM “!y'. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL h)’] thm)) >>
fs[e_size_def] >>
PAT_ASSUM “!y'.
          (case y' of INL e => e_size e | INR e_l => e3_size e_l) <
          e3_size y + (e_size h + 1) ==>
          !t' scope_lists n.
            bigstep_e_exec scope_lists y' n = SOME (t',n) ==> y' = t'” (fn thm => ASSUME_TAC (Q.SPECL [‘(INR y)’] thm)) >>

fs[e_size_def] >>
Cases_on ‘is_v x’ >> (
 fs[]
) >- (
 gvs[] >>
 subgoal ‘x1 = n’ >- (
  decide_tac
 ) >>
 fs[] >>
 res_tac >>
 fs[]
) >>
gvs[] >>
res_tac >>
fs[]
QED

fun bigstep_e_exec_not_eq_ind_hyp_tac tmq =
 PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
 fs[e_size_def] >>
 subgoal tmq >- (
  fs[]
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
  fs[bigstep_e_exec_def],

  (* var *)
  fs[bigstep_e_exec_var_REWR],

  (* list *)
  fs[bigstep_e_exec_def],

  (* acc *)
  fs[bigstep_e_exec_acc_REWR] >>
  bigstep_e_exec_not_eq_ind_hyp_tac ‘INL x <> ((INL e_v_struct):(e + e list))’,

  (* unop *)
  fs[bigstep_e_exec_unop_REWR] >>
  bigstep_e_exec_not_eq_ind_hyp_tac ‘INL x <> ((INL e'):(e + e list))’,

  (* cast *)
  fs[bigstep_e_exec_cast_REWR] >>
  bigstep_e_exec_not_eq_ind_hyp_tac ‘INL x <> ((INL e'):(e + e list))’,

  (* binop *)
  fs[bigstep_e_exec_binop_REWR] >- (
   imp_res_tac bigstep_e_exec_incr >>
   subgoal ‘n' = 0’ >- (
    fs[]
   ) >>
   fs[] >>
   imp_res_tac bigstep_e_exec_unchanged >>
   fs[]
  ) >>
  bigstep_e_exec_not_eq_ind_hyp_tac ‘INL x <> ((INL e1'):(e + e list))’,

  (* concat *)
  fs[bigstep_e_exec_concat_REWR] >- (
   imp_res_tac bigstep_e_exec_incr >>
   subgoal ‘n' = 0’ >- (
    fs[]
   ) >>
   fs[] >>
   imp_res_tac bigstep_e_exec_unchanged >>
   fs[]
  ) >>
  bigstep_e_exec_not_eq_ind_hyp_tac ‘INL x <> ((INL e1'):(e + e list))’,

  (* slice *)
  fs[bigstep_e_exec_slice_REWR] >>
  bigstep_e_exec_not_eq_ind_hyp_tac ‘INL x <> ((INL e1'):(e + e list))’,

  (* call *)
  fs[bigstep_e_exec_def],

  (* select *)
  fs[bigstep_e_exec_select_REWR] >>
  bigstep_e_exec_not_eq_ind_hyp_tac ‘INL x <> ((INL e'):(e + e list))’,

  (* struct *)
  fs[bigstep_e_exec_struct_REWR] >>
  PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INR (MAP SND (l:(string # e) list)))’] thm)) >>
  fs[e_size_def, e3_e1_size] >>
  imp_res_tac bigstep_e_exec_unchanged >>
  gvs[ZIP_MAP_FST_SND],

  (* header *)
  fs[bigstep_e_exec_def]
 ]
) >>
(* INR *)
Induct_on ‘y’ >> (
 rpt strip_tac >>
 fs[bigstep_e_exec_def]
) >>
Cases_on ‘bigstep_e_exec scope_lists (INL h) 0’ >> (
 fs[]
) >>
PairCases_on ‘x’ >>
fs[] >>
Cases_on ‘x0’ >>
fs[] >>
Cases_on ‘bigstep_e_exec scope_lists (INR y) x1’ >> (
 fs[]
) >- (
 gvs[] >>
 PAT_ASSUM “!y'. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL h)’] thm)) >>
 gs[e_size_def] >>
 res_tac
) >>
PairCases_on ‘x'’ >>
fs[] >>
Cases_on ‘x'0’ >>
fs[] >- (
 gvs[] >>
 PAT_ASSUM “!y'. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL h)’] thm)) >>
 gs[e_size_def] >>
 res_tac
) >>
imp_res_tac bigstep_e_exec_incr >>
PAT_ASSUM “!y'. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL h)’] thm)) >>
fs[e_size_def] >>
PAT_ASSUM “!y'.
          (case y' of INL e => e_size e | INR e_l => e3_size e_l) <
          e3_size y + (e_size h + 1) ==>
          !t'' scope_lists'.
            y' <> t'' ==> bigstep_e_exec scope_lists' y' 0 <> SOME (t'',0)” (fn thm => ASSUME_TAC (Q.SPECL [‘(INR y)’] thm)) >>
fs[e_size_def] >>
Cases_on ‘is_v x’ >> (
 fs[]
) >- (
 gvs[] >>
 imp_res_tac bigstep_e_exec_unchanged >>
 fs[]
) >>
gs[] >>
imp_res_tac bigstep_e_exec_unchanged >>
fs[]
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
Cases_on ‘e’ >> Cases_on ‘e'’ >> (
 fs[is_v_bit]
)
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
Cases_on ‘e’ >> Cases_on ‘e'’ >> (
 fs[is_v]
)
QED

Theorem bigstep_e_exec_v:
!v scope_list g_scope_list' n.
bigstep_e_exec (scope_list ++ g_scope_list') (INL (e_v v)) n = SOME (INL $ e_v v, n)
Proof
fs[bigstep_e_exec_def]
QED

(* OLD
Theorem bigstep_e_exec_all_red:
!e_l scope_lists n.
unred_mem_index e_l = NONE ==>
bigstep_e_exec scope_lists (INR e_l) n = SOME (INR e_l,n+1)
Proof
cheat
QED

Theorem bigstep_e_exec_single_unred:
!e_l e_l' e' x scope_lists n.
unred_mem_index e_l = SOME x ==>
bigstep_e_exec scope_lists (INR e_l) n = SOME (INR e_l',n+1) ==>
bigstep_e_exec scope_lists (INL (EL x e_l)) n = SOME (INL e', n+1) /\ e_l' = LUPDATE e' x e_l
Proof
cheat
QED
*)

Triviality unred_mem_index_NONE:
!e_l.
EVERY is_v e_l ==>
unred_mem_index e_l = NONE
Proof
Induct >- (
 fs[unred_mem_index_def, unred_mem_def, listTheory.INDEX_FIND_def]
) >>
rpt strip_tac >>
fs[unred_mem_index_def, unred_mem_def, listTheory.INDEX_FIND_def] >>
subgoal ‘is_const h’ >- (
 Cases_on ‘h’ >> (
  fs[is_v, is_const_def]
 )
) >>
fs[] >>
 Cases_on ‘INDEX_FIND 1 (\e. ~is_const e) e_l’ >> (
  fs[]
 ) >>
PairCases_on ‘x’ >>
fs[] >>
imp_res_tac index_find_first >>
Cases_on ‘INDEX_FIND 0 (\e. ~is_const e) e_l’ >- (
 fs[] >>
 fs[Q.SPECL [‘e_l’, ‘1:num’] (listTheory.INDEX_FIND_add)]
) >>
PairCases_on ‘x’ >>
fs[]
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
  fs[bigstep_e_exec_var_REWR] >>
  fs[e_exec, lookup_vexp_def, lookup_vexp2_def] >>
  Cases_on ‘lookup_map (scope_list ++ g_scope_list') v’ >> (
   fs[]
  ) >>
  PairCases_on ‘x’ >>
  fs[],

  (* list *)
  gvs[bigstep_e_exec_def],

  (* acc *)
  rw[] >>
  fs[bigstep_e_exec_acc_REWR] >> (
   rw[] >>
   fs[e_exec]
  ) >- (
   Cases_on ‘is_v x’ >> (
    fs[]
   ) >- (
    Cases_on ‘x’ >> (
     fs[is_v, bigstep_e_exec_def]
    )
   ) >>
   imp_res_tac bigstep_e_exec_unchanged >>
   fs[]
  ) >>
  fs[] >>
  PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
  fs[e_size_def] >>
  res_tac >>
  fs[] >>
  Cases_on ‘is_v x’ >> (
   fs[]
  ) >>
  Cases_on ‘x’ >> (
   fs[is_v, bigstep_e_exec_def]
  ),

  (* unop *)
  rw[] >>
  fs[bigstep_e_exec_unop_REWR] >> (
   rw[] >>
   fs[e_exec]
  ) >- (
   Cases_on ‘is_v x’ >> (
    fs[]
   ) >- (
    Cases_on ‘x’ >> (
     fs[is_v, bigstep_e_exec_def]
    )
   ) >>
   imp_res_tac bigstep_e_exec_unchanged >>
   fs[]
  ) >>
  fs[] >>
  PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
  fs[e_size_def] >>
  res_tac >>
  fs[] >>
  Cases_on ‘is_v x’ >> (
   fs[]
  ) >>
  Cases_on ‘x’ >> (
   fs[is_v, bigstep_e_exec_def]
  ),

  (* cast *)
  rw[] >>
  fs[bigstep_e_exec_cast_REWR] >> (
   rw[] >>
   fs[e_exec]
  ) >- (
   Cases_on ‘is_v x’ >> (
    fs[]
   ) >- (
    Cases_on ‘x’ >> (
     fs[is_v, bigstep_e_exec_def]
    )
   ) >>
   imp_res_tac bigstep_e_exec_unchanged >>
   fs[]
  ) >>
  fs[] >>
  PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
  fs[e_size_def] >>
  res_tac >>
  fs[] >>
  Cases_on ‘is_v x’ >> (
   fs[]
  ) >>
  Cases_on ‘x’ >> (
   fs[is_v, bigstep_e_exec_def]
  ),

  (* binop *)
  rw[] >>
  fs[bigstep_e_exec_binop_REWR] >> (
   rw[] >>
   fs[e_exec]
  ) >- (
   fs[] >>
   imp_res_tac bigstep_e_exec_unchanged >>
   fs[]
  ) >- (
   fs[] >>
   imp_res_tac bigstep_e_exec_incr >>
   fs[] >>
   imp_res_tac bigstep_e_exec_unchanged >>
   fs[] >>
   Cases_on ‘x’ >> (
    gvs[is_v]
   )
  ) >- (
   Cases_on ‘is_v x’ >> (
    fs[]
   ) >- (
    Cases_on ‘x’ >> (
     gvs[is_v]
    ) >- (
     Cases_on ‘is_v x'’ >> (
      fs[]
     ) >- (
      Cases_on ‘x'’ >> (
       gvs[is_v]
      ) >>
      fs[bigstep_e_exec_def]
     ) >>
     fs[bigstep_e_exec_def] >>
     gvs[] >>
     PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x')’] thm)) >>
     fs[e_size_def] >>
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
    fs[]
   ) >>
   fs[] >>
   PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
   Cases_on ‘x’ >> (
    gvs[is_v]
   ) >> (
    fs[e_size_def] >>
    res_tac >>
    fs[] >>
    imp_res_tac bigstep_e_exec_unchanged >>
    fs[]
   )
  ) >- (
   fs[] >>
   PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
   fs[e_size_def] >>
   res_tac >>
   fs[] >>
   Cases_on ‘x’ >> (
    fs[bigstep_e_exec_def]
   )
  ),

  (* concat *)
  rw[] >>
  fs[bigstep_e_exec_concat_REWR] >> (
   rw[] >>
   fs[e_exec]
  ) >- (
   fs[] >>
   imp_res_tac bigstep_e_exec_incr >>
   fs[] >>
   imp_res_tac bigstep_e_exec_unchanged >>
   fs[]
  ) >- (
   Cases_on ‘is_v_bit x’ >> (
    fs[]
   ) >- (
    Cases_on ‘x’ >> (
     gvs[is_v_bit]
    ) >>
    Cases_on ‘v’ >> (
     gvs[is_v_bit]
    ) >>
    Cases_on ‘is_v_bit x'’ >> (
     fs[]
    ) >- (
     Cases_on ‘x'’ >> (
      gvs[is_v_bit]
     ) >>
     fs[bigstep_e_exec_def]
    ) >>
    subgoal ‘n' = 0’ >- (
     fs[bigstep_e_exec_def]
    ) >>
    fs[] >>
    PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x')’] thm)) >>
    fs[e_size_def] >>
    res_tac >>
    fs[] >>
    imp_res_tac bigstep_e_exec_unchanged >>
    fs[]
   ) >>
   imp_res_tac bigstep_e_exec_incr >>
   subgoal ‘n' = 1’ >- (
    CCONTR_TAC >>
    subgoal ‘n' = 0’ >- (
     decide_tac
    ) >>
    fs[] >>
    imp_res_tac bigstep_e_exec_unchanged >>
    fs[]
   ) >>
   fs[] >>
   PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
   fs[e_size_def] >>
   res_tac >>
   fs[] >>
   imp_res_tac bigstep_e_exec_unchanged >>
   fs[]
  ) >- (
   fs[] >>
   PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
   fs[e_size_def] >>
   res_tac >>
   fs[] >>
   Cases_on ‘is_v_bit x’ >> (
    fs[]
   ) >>
   Cases_on ‘x’ >> (
    gvs[is_v_bit]
   ) >>
   fs[bigstep_e_exec_def]
  ),

  (* slice *)
  rw[] >>
  fs[bigstep_e_exec_slice_REWR] >> (
   rw[] >>
   fs[e_exec]
  ) >- (
   Cases_on ‘is_v_bit x’ >> (
    fs[]
   ) >- (
    Cases_on ‘x’ >> (
     fs[is_v_bit, bigstep_e_exec_def]
    )
   ) >>
   imp_res_tac bigstep_e_exec_unchanged >>
   fs[]
  ) >>
  fs[] >>
  PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
  fs[e_size_def] >>
  res_tac >>
  fs[] >>
  Cases_on ‘is_v_bit x’ >> (
   fs[]
  ) >>
  Cases_on ‘x’ >> (
   fs[is_v_bit, bigstep_e_exec_def]
  ),

  (* call *) 
  gvs[bigstep_e_exec_def],

  (* select *)
  rw[] >>
  fs[bigstep_e_exec_select_REWR] >> (
   rw[] >>
   fs[e_exec]
  ) >>
  Cases_on ‘is_v x’ >> (
   fs[]
  ) >- (
   Cases_on ‘x’ >> (
    fs[is_v, bigstep_e_exec_def]
   )
  ) >>
  PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
  fs[e_size_def] >>
  res_tac >>
  fs[],

  (* struct *)
  rw[] >>
  fs[bigstep_e_exec_struct_REWR] >> (
   rw[] >>
   fs[e_exec]
  ) >- (
   fs[] >>
   imp_res_tac bigstep_e_exec_unchanged >>
   fs[] >>
   Cases_on ‘unred_mem_index e_l'’ >> (
    fs[]
   ) >>
   (* Contradiction on unreduced element in e_l' *)
   imp_res_tac unred_mem_index_NONE >>
   fs[]
  ) >>
  fs[] >>
  PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INR (MAP SND (l:(string # e) list)))’] thm)) >>
  fs[e_size_def, e3_e1_size] >>
  res_tac >>
  Cases_on ‘l’ >- (
   fs[bigstep_e_exec_def, e_exec]
  ) >>
  fs[e_exec] >>
  Cases_on ‘unred_mem_index (SND h::MAP SND t)’ >> (
   fs[]
  ) >>
  PAT_X_ASSUM “!tbl_map pars_map func_map ext_map b_func_map apply_table_f. _” (fn thm => ASSUME_TAC (Q.SPECL [‘tbl_map’, ‘pars_map’, ‘func_map’, ‘ext_map’, ‘b_func_map’, ‘apply_table_f’] thm)) >>
  fs[],

  (* header *)
  gvs[bigstep_e_exec_def]
 ]
) >>
(* INR *)
Induct_on ‘y’ >> (
 rpt strip_tac >>
 fs[bigstep_e_exec_def]
) >>
Cases_on ‘bigstep_e_exec (scope_list ++ g_scope_list') (INL h) 0’ >> (
 fs[]
) >>
PairCases_on ‘x’ >>
fs[] >>
Cases_on ‘x0’ >>
fs[] >>
Cases_on ‘is_v x’ >> (
 fs[]
) >- (
 (* Same as with old definition *)
 Cases_on ‘bigstep_e_exec (scope_list ++ g_scope_list') (INR y) x1’ >> (
  fs[]
 ) >>
 PairCases_on ‘x'’ >>
 fs[] >>
 Cases_on ‘x'0’ >>
 fs[] >>
 subgoal ‘x1 = 0 \/ x1 = 1’ >- (
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
   fs[bigstep_e_exec_def]
  ) >>
  fs[] >>
  qexists_tac ‘i+1’ >>
  gvs[] >>
  rpt strip_tac >- (
   (* Not true? h could be any expression that is not reduced further.. *)
   subgoal ‘is_const h’ >- (
    Cases_on ‘h’ >> (
     fs[is_v, is_const_def]
    )
   ) >>
   fs[unred_mem_index_def, unred_mem_def, listTheory.INDEX_FIND_def] >>
   fs[Q.SPECL [‘y’, ‘1:num’] (listTheory.INDEX_FIND_add)] >>
   Cases_on ‘INDEX_FIND 0 (\e. ~is_const e) y’ >> (
    fs[]
   ) >>
   PairCases_on ‘x’ >>
   fs[]
  ) >>
  qexists_tac ‘e'’ >>
  subgoal ‘(EL (i + 1) (h::y)) = (EL i y)’ >- (
   fs[GSYM p4_auxTheory.SUC_ADD_ONE, listTheory.EL_restricted]
  ) >>
  fs[GSYM p4_auxTheory.SUC_ADD_ONE, listTheory.LUPDATE_def]
 ) >>
 (* x1 = 1: h reduction contributes the step *)
 gvs[] >>
 subgoal ‘~is_const h’ >- (
  CCONTR_TAC >>
  Cases_on ‘h’ >> (
   fs[is_const_def, bigstep_e_exec_def]
  )
 ) >>
 PAT_ASSUM “!y'. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL h)’] thm)) >>
 fs[e_size_def] >>
 res_tac >>
 fs[] >>
 qexists_tac ‘0’ >>
 fs[unred_mem_index_def, unred_mem_def, listTheory.INDEX_FIND_def, listTheory.LUPDATE_def] >>
 imp_res_tac bigstep_e_exec_unchanged >>
 fs[]
) >>
(* New case *)
gvs[] >>
qexists_tac ‘0’ >>
subgoal ‘~is_const h’ >- (
 CCONTR_TAC >>
 Cases_on ‘h’ >> (
  fs[is_const_def, bigstep_e_exec_def]
 )
) >>
fs[unred_mem_index_def, unred_mem_def, listTheory.INDEX_FIND_def, listTheory.LUPDATE_def] >>
PAT_ASSUM “!y'. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL h)’] thm)) >>
fs[e_size_def] >>
res_tac >>
fs[]
QED

(* TODO: This can probably just NONE the new frames *)
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

Theorem e_acc_v_not_red:
!e e' (ctx:'a ctx) g_scope_list scope_list.
~is_v e' ==>
e_exec ctx g_scope_list scope_list e = SOME (e',[]) ==>
~is_v e
Proof
rpt strip_tac >>
Cases_on ‘e’ >> (
 fs[is_v, e_exec]
)
QED

Theorem bigstep_e_acc_exec_sound_n_not_v:
!ctx g_scope_list' scope_list e e' n f.
~is_v e' ==>
e_multi_exec' (ctx:'a ctx) g_scope_list' scope_list e n = SOME e' ==>
e_multi_exec' (ctx:'a ctx) g_scope_list' scope_list (e_acc e f) n = SOME (e_acc e' f)
Proof
Induct_on ‘n’ >- (
 fs[e_multi_exec'_def]
) >>
rpt strip_tac >>
fs[e_multi_exec'_def] >>
Cases_on ‘e_multi_exec' ctx g_scope_list' scope_list e n’ >> (
 fs[]
) >>
Cases_on ‘e_exec ctx g_scope_list' scope_list x’ >> (
 fs[]
) >>
PairCases_on ‘x'’ >>
fs[] >>
Cases_on ‘x'1’ >> (
 fs[]
) >>
gvs[] >>
subgoal ‘~is_v x’ >- (
 imp_res_tac e_acc_v_not_red
) >>
res_tac >>
fs[] >>
gvs[] >>
Cases_on ‘e_exec ctx g_scope_list' scope_list (e_acc x f)’ >> (
 gs[e_exec]
) >>
PairCases_on ‘x'’ >>
fs[]
QED

Theorem bigstep_e_acc_exec_sound_n_v:
!ctx g_scope_list' scope_list e e' n f.
is_v e' ==>
e_multi_exec' (ctx:'a ctx) g_scope_list' scope_list e n = SOME e' ==>
e_multi_exec' (ctx:'a ctx) g_scope_list' scope_list (e_acc e f) (SUC n) = e_exec_acc (e_acc e' f)
Proof
Induct_on ‘n’ >- (
 rpt strip_tac >>
 fs[e_multi_exec'_def] >>
 Cases_on ‘e_exec ctx g_scope_list' scope_list (e_acc e' f)’ >> (
  fs[]
 ) >> (
  gs[e_exec] >>
  Cases_on ‘e_exec_acc (e_acc e' f)’ >> (
   fs[]
  )
 ) >>
 PairCases_on ‘x’ >>
 fs[]
) >>
rpt strip_tac >>
fs[e_multi_exec'_def] >>
Cases_on ‘e_multi_exec' ctx g_scope_list' scope_list e n’ >> (
 fs[]
) >>
subgoal ‘~is_v x’ >- (
 rpt strip_tac >>
 Cases_on ‘e_exec ctx g_scope_list' scope_list x’ >> (
  fs[]
 ) >>
 PairCases_on ‘x'’ >>
 fs[] >>
 Cases_on ‘x'1’ >> (
  fs[]
 ) >>
 Cases_on ‘x’ >> (
  fs[is_v, e_exec]
 )
) >>
imp_res_tac bigstep_e_acc_exec_sound_n_not_v >>
fs[] >>
Cases_on ‘e_exec ctx g_scope_list' scope_list x’ >> (
 fs[]
) >>
PairCases_on ‘x'’ >>
fs[] >>
Cases_on ‘x'1’ >> (
 fs[]
) >>
gvs[] >>
Cases_on ‘e_exec ctx g_scope_list' scope_list (e_acc x f)’ >> (
 gs[e_exec]
) >>
PairCases_on ‘x'’ >>
fs[] >>
Cases_on ‘x'1’ >> (
 fs[]
) >>
gvs[] >>
Cases_on ‘e_exec ctx g_scope_list' scope_list (e_acc e' f)’ >> (
 gs[e_exec]
) >> (
 Cases_on ‘e_exec_acc (e_acc e' f)’ >> (
  fs[]
 )
) >>
PairCases_on ‘x'’ >>
fs[]
QED

Theorem bigstep_e_exec_sound_n:
!e n scope_list g_scope_list' e' ctx.
bigstep_e_exec (scope_list ++ g_scope_list') (INL e) 0 = SOME (INL e', n) ==>
 e_multi_exec' (ctx:'a ctx)
        g_scope_list' scope_list e n = SOME e'
Proof
Induct_on ‘e’ >- (
 (* value *)
 Cases_on ‘n’ >> (
  fs[e_multi_exec'_def, bigstep_e_exec_def]
 )
) >- (
 (* variable *)
 cheat
) >- (
 (* list *)
 fs[e_multi_exec'_def, bigstep_e_exec_def]
) >- (
 (* access *)
 rpt strip_tac >>
 fs[bigstep_e_exec_def] >>
 Cases_on ‘bigstep_e_exec (scope_list ++ g_scope_list') (INL e) 0’ >> (
  fs[]
 ) >>
 PairCases_on ‘x’ >>
 fs[] >>
 Cases_on ‘x0’ >> (
  fs[]
 ) >>
 Cases_on ‘is_v x’ >> (
  fs[]
 ) >- (
  Cases_on ‘e_exec_acc (e_acc x s)’ >> (
   fs[]
  ) >>
  gvs[] >>
  PAT_X_ASSUM “e_exec_acc (e_acc x s) = SOME e'” (fn thm => REWRITE_TAC [GSYM thm]) >>
  fs[GSYM SUC_ADD_ONE] >>
  irule bigstep_e_acc_exec_sound_n_v >>
  fs[]
 ) >>
 gvs[] >>
 res_tac >>
 imp_res_tac bigstep_e_acc_exec_sound_n_not_v >>
 fs[]
) >- (
 (* unary arithmetic *)
 cheat
) >- (
 (* cast *)
 cheat
) >- (
 (* binary arithmetic *)
 cheat
) >- (
 (* concat *)
 cheat
) >- (
 (* slicing *)
 cheat
) >- (
 (* call *)
 fs[e_multi_exec'_def, bigstep_e_exec_def]
) >- (
 (* select *)
 cheat
) >- (
 (* struct *)
 cheat
) >> (
 (* header *)
 cheat
)
QED

Definition stmt_multi_exec'_check_state_def:
 (stmt_multi_exec'_check_state ((ascope, [g_scope1; g_scope2], [(funn, [stmt], scope_list)], status_running):'a state)
                               ((ascope', [g_scope1'; g_scope2'], [(funn', [stmt'], scope_list')], status_running):'a state) =
  if ascope = ascope' /\ funn = funn' /\ LENGTH scope_list = LENGTH scope_list'
  then SOME (ascope, [g_scope1; g_scope2], [(funn, [stmt], scope_list)], status_running)
  else NONE
)
 /\
 (stmt_multi_exec'_check_state _ _ = NONE)
End

Definition stmt_multi_exec'_def:
 (stmt_multi_exec' _ state 0 = SOME state)
 /\
 (stmt_multi_exec' (ctx:'a ctx) state (SUC fuel) =
  case stmt_multi_exec' ctx state fuel of
  | SOME state' =>
   stmt_exec ctx state'
  | _ => NONE)
End

Theorem bigstep_stmt_ass_exec_sound_n_not_v:
!n ctx g_scope_list top_scope scope_list ascope funn l e e'.
~is_v e' ==>
e_multi_exec' (ctx:'a ctx) g_scope_list (top_scope::scope_list) e n = SOME e' ==>
stmt_multi_exec' (ctx:'a ctx)
 (ascope, g_scope_list,
  [(funn, [stmt_ass l e], (top_scope::scope_list))], status_running) n =
 SOME (ascope, g_scope_list,
       [(funn, [stmt_ass l e'], (top_scope::scope_list))],
       status_running)
Proof
Induct_on ‘n’ >- (
 fs[e_multi_exec'_def, stmt_multi_exec'_def]
) >>
rpt strip_tac >>
fs[e_multi_exec'_def, stmt_multi_exec'_def] >>
Cases_on ‘e_multi_exec' ctx g_scope_list (top_scope::scope_list) e n’ >> (
 fs[]
) >>
Cases_on ‘e_exec ctx g_scope_list (top_scope::scope_list) x’ >> (
 fs[]
) >>
PairCases_on ‘x'’ >>
fs[] >>
Cases_on ‘x'1’ >> (
 fs[]
) >>
gvs[] >>
subgoal ‘~is_v x’ >- (
 imp_res_tac e_acc_v_not_red
) >>
res_tac >>
fs[stmt_exec]
QED

Theorem bigstep_stmt_ass_exec_sound_n_v:
!n ctx g_scope_list top_scope scope_list ascope funn lval e e' scope_list'' g_scope_list' scope_list'.
is_v e' ==>
e_multi_exec' (ctx:'a ctx) g_scope_list (top_scope::scope_list) e n = SOME e' ==>
stmt_exec_ass lval e' ((top_scope::scope_list)++g_scope_list) = SOME scope_list'' ==>
separate scope_list'' = (SOME g_scope_list', SOME scope_list') ==>
stmt_multi_exec' (ctx:'a ctx)
 (ascope, g_scope_list,
  [(funn, [stmt_ass lval e], (top_scope::scope_list))], status_running) (SUC n) =
 SOME (ascope, g_scope_list',
       [(funn, [stmt_empty], scope_list')],
       status_running)
Proof
Induct_on ‘n’ >- (
 rpt strip_tac >>
 fs[stmt_multi_exec'_def, e_multi_exec'_def] >>
 Cases_on ‘e'’ >> (
  gvs[stmt_exec, is_v]
 )
) >>
rpt strip_tac >>
fs[e_multi_exec'_def, stmt_multi_exec'_def] >>
Cases_on ‘e_multi_exec' ctx g_scope_list (top_scope::scope_list) e n’ >> (
 fs[]
) >>
Cases_on ‘e_exec ctx g_scope_list (top_scope::scope_list) x’ >> (
 fs[]
) >>
PairCases_on ‘x'’ >>
fs[] >>
Cases_on ‘x'1’ >> (
 fs[]
) >>
subgoal ‘~is_v x’ >- (
 rpt strip_tac >>
 Cases_on ‘x’ >> (
  fs[is_v, e_exec]
 )
) >>
imp_res_tac bigstep_stmt_ass_exec_sound_n_not_v >>
fs[stmt_exec]
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
fs[separate_def] >>
gs[arithmeticTheory.ADD_SUC] >>
FULL_SIMP_TAC pure_ss [GSYM SUC_ADD_ONE] >>
fs[oDROP_def, oTAKE_def, oDROP_APPEND, oTAKE_APPEND]
QED

Theorem bigstep_stmt_ass_exec_sound_n_call:
!top_scope scope_list g_scope_list funn funn' lval e_l e_l' n (ctx:'a ctx) ascope.
bigstep_f_arg_exec (NONE:(func_map # b_func_map # 'a ext_map) option) (top_scope::(scope_list ++ g_scope_list)) (funn',e_l) 0 = SOME (e_l', n) ==>
stmt_multi_exec' ctx
 (ascope, g_scope_list, [(funn,[stmt_ass lval (e_call funn' e_l)],top_scope::scope_list)],status_running) n =
  SOME (ascope, g_scope_list, [(funn,[stmt_ass lval (e_call funn' e_l')], top_scope::scope_list)], status_running)
Proof
Induct_on ‘n’ >- (
 rpt strip_tac >>
 fs[stmt_multi_exec'_def, bigstep_f_arg_exec_def]
) >>
rpt strip_tac >>
fs[stmt_multi_exec'_def, bigstep_f_arg_exec_def]
QED

(* TODO: Use separate to handle scope lists *)
Theorem bigstep_stmt_exec_sound_n:
!n scope_list scope_lists' scope_list' funn ascope stmt stmt' stmt_stack top_scope g_scope_list g_scope_list' ctx.
bigstep_stmt_exec (NONE:(func_map # b_func_map # 'a ext_map) option) ((top_scope::scope_list)++g_scope_list) stmt 0 = SOME (stmt', scope_lists', n) ==>
 LENGTH g_scope_list = 2 ==>
 separate scope_lists' = (SOME g_scope_list',SOME scope_list') ==>
 stmt_multi_exec' (ctx:'a ctx) (ascope:'a, g_scope_list:g_scope_list, [(funn, [stmt], (top_scope::scope_list))], status_running) n = SOME (ascope, g_scope_list', [(funn, [stmt'], scope_list')], status_running)
Proof
Induct_on ‘stmt’ >- (
 (* empty *)
 fs[stmt_multi_exec'_def, bigstep_stmt_exec_def] >>
 rpt strip_tac >> (
  gs[separate_def, SUC_ADD_ONE] >>
  gs[GSYM SUC_ADD_ONE, oDROP_def, oTAKE_def, oDROP_APPEND, oTAKE_APPEND]
 )
) >- (
 (* assignment *)
 fs[stmt_multi_exec'_def, bigstep_stmt_exec_def] >>
 rpt strip_tac >>
 (* Rule this out first... *)
 Cases_on ‘?funn e_l. e = e_call funn e_l’ >- (
  gs[] >>
  Cases_on ‘bigstep_f_arg_exec NONE (top_scope::(scope_list ++ g_scope_list))
              (funn',e_l) 0’ >> (
   fs[]
  ) >>
  PairCases_on ‘x’ >>
  fs[] >>
  Cases_on ‘x0’ >> (
   fs[]
  ) >> (
   gvs[] >>
   subgoal ‘g_scope_list = g_scope_list'’ >- (
    metis_tac[scope_lists_separate]
   ) >>
   subgoal ‘top_scope::scope_list = scope_list'’ >- (
    metis_tac[scope_lists_separate]
   ) >>
   gvs[stmt_multi_exec'_def, bigstep_f_arg_exec_def]
  )
 ) >>
 Cases_on ‘bigstep_e_exec (top_scope::(scope_list ++ g_scope_list)) (INL e) 0’ >> (
  fs[]
 ) >- (
  (* Case e is e_call *)
  Cases_on ‘e’ >> (
   fs[]
  )
 ) >>
 PairCases_on ‘x’ >>
 fs[] >>
 Cases_on ‘x0’ >> (
  fs[]
 ) >- (
  Cases_on ‘is_v x’ >> (
   fs[]
  ) >- (
   Cases_on ‘stmt_exec_ass l x (top_scope::(scope_list ++ g_scope_list))’ >> (
    fs[]
   ) >> (
    Cases_on ‘e’ >> (
     gvs[]
    )
   ) >> (
    FULL_SIMP_TAC pure_ss [GSYM listTheory.APPEND] >>
    imp_res_tac bigstep_e_exec_sound_n >>
    qpat_x_assum ‘!ctx. _’ (fn thm => ASSUME_TAC (Q.SPEC ‘ctx’ thm)) >>
    imp_res_tac bigstep_stmt_ass_exec_sound_n_v >>
    fs[SUC_ADD_ONE]
   )
  ) >>
  Cases_on ‘e’ >> (
   gvs[]
  ) >> (
   FULL_SIMP_TAC pure_ss [GSYM listTheory.APPEND] >>
   imp_res_tac bigstep_e_exec_sound_n >>
   qpat_x_assum ‘!ctx. _’ (fn thm => ASSUME_TAC (Q.SPEC ‘ctx’ thm)) >>
   imp_res_tac bigstep_stmt_ass_exec_sound_n_not_v >>
   fs[] >>
   irule scope_lists_separate >>
   fs[]
  )
 ) >>
 Cases_on ‘e’ >> (
  gvs[]
 )
) >> (
 (* The rest of the statements *)
 cheat
)
QED

(* TODO: Add length of scope lists identical? *)
Theorem bigstep_stmt_exec_imp:
!stmt stmt' scope_lists scope_lists' n m.
bigstep_stmt_exec (NONE:(func_map # b_func_map # 'a ext_map) option) scope_lists stmt n = SOME (stmt', scope_lists', m) ==>
((n <= m) /\
(n = m ==> (stmt = stmt' /\ scope_lists = scope_lists')))
Proof
Induct_on ‘stmt’ >> (
 rpt gen_tac >>
 rpt disch_tac
) >| [
 (* empty *)
 fs[bigstep_stmt_exec_def],

 (* assign *)
 fs[bigstep_stmt_exec_def] >>
 Cases_on ‘is_v e’ >> (
  fs[]
 ) >- (
  Cases_on ‘e’ >> (
   fs[is_v]
  ) >>
  fs[bigstep_e_exec_def, is_v] >>
  Cases_on ‘stmt_exec_ass l (e_v v) scope_lists’ >> (
   fs[]
  )
 ) >>
 Cases_on ‘?funn' e_l. e = e_call funn e_l’ >> (
  gs[bigstep_f_arg_exec_def]
 ) >>
 Cases_on ‘bigstep_e_exec scope_lists (INL e) n’ >> (
  fs[]
 ) >- (
  Cases_on ‘e’ >> (
   fs[]
  )
 ) >>
 PairCases_on ‘x’ >>
 fs[] >>
 Cases_on ‘x0’ >> (
  fs[]
 ) >> (
  Cases_on ‘is_v x’ >> (
   fs[]
  ) >- (
   Cases_on ‘stmt_exec_ass l x scope_lists’ >> (
    fs[]
   ) >> (
    Cases_on ‘e’ >> (
     fs[]
    )
   ) >> (
    gvs[is_v] >>
    imp_res_tac bigstep_e_exec_incr >>
    decide_tac
   )
  ) >> (
   Cases_on ‘e’ >> (
    fs[]
   )
  ) >> (
   gvs[is_v] >>
   imp_res_tac bigstep_e_exec_incr >>
   fs[] >>
   Cases_on ‘n = m’ >> (
    gvs[]
   ) >>
   imp_res_tac bigstep_e_exec_unchanged >>
   fs[]
  )
 ) >>
 Cases_on ‘e’ >> (
  fs[]
 ),

 (* Conditional *)
 fs[bigstep_stmt_exec_def] >>
 Cases_on ‘is_v e’ >> (
  fs[]
 ) >- (
  Cases_on ‘e’ >> (
   fs[is_v]
  ) >>
  fs[bigstep_e_exec_def, is_v]
 ) >>
 Cases_on ‘?funn' e_l. e = e_call funn e_l’ >> (
  gs[bigstep_f_arg_exec_def]
 ) >>
 Cases_on ‘bigstep_e_exec scope_lists (INL e) n’ >> (
  fs[]
 ) >- (
  Cases_on ‘e’ >> (
   fs[]
  )
 ) >>
 PairCases_on ‘x’ >>
 fs[] >>
 Cases_on ‘x0’ >> (
  fs[]
 ) >- (
  Cases_on ‘e’ >> (
   fs[]
  ) >> (
   gvs[is_v] >>
   imp_res_tac bigstep_e_exec_incr
  ) >> (
   fs[] >>
   Cases_on ‘n = m’ >> (
    gvs[]
   ) >>
   imp_res_tac bigstep_e_exec_unchanged >>
   fs[]
  )
 ) >>
 Cases_on ‘e’ >> (
  fs[]
 ),
 
 (* block *)
 fs[bigstep_stmt_exec_def],

 (* return *)
 fs[bigstep_stmt_exec_def] >>
 Cases_on ‘get_v e <> NONE’ >> (
  fs[]
 ) >- (
  subgoal ‘?x. get_v e = SOME x’ >- (
   fs[GSYM quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE, optionTheory.IS_SOME_EXISTS]
  ) >>
  Cases_on ‘e’ >> (
   fs[get_v]
  ) >>
  fs[bigstep_stmt_exec_def, bigstep_e_exec_def]
 ) >>
 (* e reduction *)
 Cases_on ‘bigstep_e_exec scope_lists (INL e) n’ >> (
  fs[]
 ) >>
 PairCases_on ‘x’ >>
 gs[] >>
 Cases_on ‘x0’ >> (
  fs[]
 ) >>
 gvs[] >>
 imp_res_tac bigstep_e_exec_incr >>
 fs[] >>
 Cases_on ‘n = m’ >> (
  gvs[]
 ) >>
 imp_res_tac bigstep_e_exec_unchanged >>
 fs[],

 (* seq - sole recursive case *)
 fs[bigstep_stmt_exec_def] >>
 Cases_on ‘is_empty stmt’ >> (
  fs[] >>
  res_tac >>
  Cases_on ‘n +1 = m’ >> (
   gvs[]
  )
 ) >>
 (* Nested statement execution *)
 Cases_on ‘bigstep_stmt_exec NONE scope_lists stmt n’ >> (
  fs[]
 ) >>
 PairCases_on ‘x’ >>
 fs[] >>
 Cases_on ‘is_empty x0’ >> (
  fs[]
 ) >- (
  res_tac >>
  fs[]
 ) >>
 res_tac >>
 fs[],

 (* transition *)
 fs[bigstep_stmt_exec_def] >>
 Cases_on ‘bigstep_e_exec scope_lists (INL e) n’ >> (
  fs[]
 ) >>
 PairCases_on ‘x’ >>
 gs[] >>
 Cases_on ‘x0’ >> (
  fs[]
 ) >>
 gvs[] >>
 imp_res_tac bigstep_e_exec_incr >>
 fs[] >>
 Cases_on ‘n = m’ >> (
  gvs[]
 ) >>
 imp_res_tac bigstep_e_exec_unchanged >>
 fs[],

 (* apply *)
 fs[bigstep_stmt_exec_def] >>
 Cases_on ‘bigstep_e_exec scope_lists (INR l) n’ >> (
  fs[]
 ) >>
 PairCases_on ‘x’ >>
 gs[] >>
 Cases_on ‘x0’ >> (
  fs[]
 ) >>
 imp_res_tac bigstep_e_exec_incr >>
 fs[] >>
 Cases_on ‘n = m’ >> (
  gvs[]
 ) >>
 imp_res_tac bigstep_e_exec_unchanged >>
 fs[],

 (* ext *)
 fs[bigstep_stmt_exec_def]
]
QED

(*
Theorem bigstep_stmt_exec_unchanged:
!stmt stmt' scope_lists scope_lists' n.
bigstep_stmt_exec (NONE:(func_map # b_func_map # 'a ext_map) option) scope_lists stmt n = SOME (stmt', scope_lists', n) ==>
stmt = stmt' /\ scope_lists = scope_lists'
Proof
cheat
QED
*)

(* TODO: Prove where that arch_frame_list_regular is obtained for all SOME results? *)
(* The addition of premises seem iffy, but this soundness theorem is only ever used
 * in a situation where they hold. *)
Theorem bigstep_stmt_exec_sound:
!h scope_list g_scope_list' g_scope_list''
stmt' scope_lists scope_list' funn t top_scope apply_table_f ext_map func_map x' pars_map x'' ascope.
bigstep_stmt_exec (NONE:(func_map # b_func_map # 'a ext_map) option) ((top_scope::scope_list)++g_scope_list') h 0 = SOME (stmt', scope_lists, 1) ==>
LENGTH g_scope_list' = 2 ==>
separate scope_lists = (SOME g_scope_list'',SOME scope_list') ==>
stmt_exec (apply_table_f,ext_map:'a ext_map,func_map,x',pars_map,x'')
             (ascope,g_scope_list',[(funn,h::t,(top_scope::scope_list))],status_running) = SOME (ascope, g_scope_list'', [(funn,stmt'::t,scope_list')], status_running)
Proof
Induct_on ‘h’ >> (
 rpt strip_tac
) >| [
 (* empty *)
 fs[bigstep_stmt_exec_def],

 (* assign *)
 Cases_on ‘t’ >> (
  fs[stmt_exec]
 ) >> (
  (* Both cases of t identical *)
  Cases_on ‘is_v e’ >> (
   fs[]
  ) >- (
   Cases_on ‘e’ >> (
    fs[is_v]
   ) >>
   fs[bigstep_stmt_exec_def, bigstep_e_exec_def, is_v] >>
   Cases_on ‘stmt_exec_ass l (e_v v) (top_scope::(scope_list ++ g_scope_list'))’ >> (
    fs[]
   )
  ) >>
  (* e reduction *)
  fs[bigstep_stmt_exec_def] >>
  Cases_on ‘?funn' e_l. e = e_call funn e_l’ >> (
   gs[bigstep_f_arg_exec_def]
  ) >>
  Cases_on ‘bigstep_e_exec (top_scope::(scope_list ++ g_scope_list')) (INL e) 0’ >> (
   fs[]
  ) >- (
   Cases_on ‘e’ >> (
    fs[]
   )
  ) >>
  PairCases_on ‘x’ >>
  fs[] >>
  (* TODO: This seems repetitive... *)
  subgoal ‘x1 = 1’ >- (
   Cases_on ‘e’ >> (
    fs[is_v]
   ) >> (
    Cases_on ‘x0’ >> (
     fs[]
    ) >>
    Cases_on ‘is_v x’ >> (
     fs[]
    ) >>
    Cases_on ‘stmt_exec_ass l x (top_scope::(scope_list ++ g_scope_list'))’ >> (
     fs[]
    ) >>
    gvs[] >>
    imp_res_tac bigstep_e_exec_unchanged >>
    gvs[is_v]
   )
  ) >>
  fs[] >>
  FULL_SIMP_TAC pure_ss [GSYM listTheory.APPEND] >>
  imp_res_tac bigstep_e_exec_sound >>
  fs[] >>
  Cases_on ‘e’ >> (
   fs[]
  ) >> (
   (* All different cases of e *)
   Cases_on ‘x0’ >> (
    fs[]
   ) >>
   Cases_on ‘is_v x’ >> (
    fs[]
   ) >- (
    Cases_on ‘stmt_exec_ass l x (top_scope::(scope_list ++ g_scope_list'))’ >> (
     fs[]
    )
   ) >>
   irule scope_lists_separate >>
   metis_tac[]
  )
 ),

 (* Conditional *)
 Cases_on ‘t’ >> (
  fs[stmt_exec]
 ) >> (
  Cases_on ‘is_v_bool e’ >> (
   fs[]
  ) >- (
   Cases_on ‘e’ >> (
    fs[is_v_bool]
   ) >>
   Cases_on ‘v’ >> (
    fs[is_v_bool]
   ) >>
   fs[bigstep_stmt_exec_def, bigstep_e_exec_def]
  ) >>
  (* e reduction *)
  fs[bigstep_stmt_exec_def] >>
  Cases_on ‘?funn' e_l. e = e_call funn e_l’ >> (
   gs[bigstep_f_arg_exec_def]
  ) >>
  Cases_on ‘bigstep_e_exec (top_scope::(scope_list ++ g_scope_list')) (INL e) 0’ >> (
   fs[]
  ) >- (
   Cases_on ‘e’ >> (
    fs[]
   )
  ) >>
  PairCases_on ‘x’ >>
  fs[] >>
  subgoal ‘x1 = 1’ >- (
   Cases_on ‘e’ >> (
    fs[]
   ) >> (
    Cases_on ‘x0’ >> (
     fs[]
    )
   )
  ) >>
  fs[] >>
  FULL_SIMP_TAC pure_ss [GSYM listTheory.APPEND] >>
  imp_res_tac bigstep_e_exec_sound >>
  fs[] >>
  Cases_on ‘x0’ >> (
   fs[]
  ) >>
  Cases_on ‘e’ >> (
   fs[]
  ) >> (
   (* All different cases of e *)
   irule scope_lists_separate >>
   metis_tac[]
  )
 ),
 
 (* block *)
 fs[bigstep_stmt_exec_def],

 (* return *)
 Cases_on ‘t’ >> (
  fs[stmt_exec]
 ) >> (
  Cases_on ‘get_v e <> NONE’ >> (
   fs[]
  ) >- (
   subgoal ‘?x. get_v e = SOME x’ >- (
    fs[GSYM quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE, optionTheory.IS_SOME_EXISTS]
   ) >>
   Cases_on ‘e’ >> (
    fs[get_v]
   ) >>
   fs[bigstep_stmt_exec_def, bigstep_e_exec_def]
  ) >>
  (* e reduction *)
  fs[bigstep_stmt_exec_def] >>
  Cases_on ‘bigstep_e_exec (top_scope::(scope_list ++ g_scope_list')) (INL e) 0’ >> (
   fs[]
  ) >>
  PairCases_on ‘x’ >>
  gs[] >>
  Cases_on ‘x0’ >> (
   fs[]
  ) >>
  rw[] >>
  FULL_SIMP_TAC pure_ss [GSYM listTheory.APPEND] >>
  imp_res_tac bigstep_e_exec_sound >>
  fs[] >>
  irule scope_lists_separate >>
  metis_tac[]
 ),

 (* seq - sole recursive case *)
 (* Make case split on statement stack - virtually same proof
  * for both cases, other than naming of certain variables *)
 Cases_on ‘t’ >> (
  fs[stmt_exec, bigstep_stmt_exec_def]
 ) >> (
  (* Go through regular and big-step execution simultaneously
   * prove soundness for every case *)
  Cases_on ‘is_empty h’ >> (
   fs[]
  ) >- (
   (* Everything unchanged, by looking at step counter
    * of bigstep_stmt_exec *)
   imp_res_tac bigstep_stmt_exec_imp >>
   fs[] >>
   irule scope_lists_separate >>
   metis_tac[]
  ) >>
  (* Nested statement execution *)
  Cases_on ‘bigstep_stmt_exec NONE (top_scope::(scope_list ++ g_scope_list'))
             h 0’ >> (
   fs[]
  ) >>
  PairCases_on ‘x’ >>
  fs[] >>
  (* Need to get to end of bigstep statement execution to get final
   * step counter for induction hypothesis *)
  Cases_on ‘is_empty x0’ >> (
   fs[]
  ) >- (
   subgoal ‘x2 = 0’ >- (
    (* Must be the case since step counter is strictly increasing *)
    imp_res_tac bigstep_stmt_exec_imp >>
    fs[]
   ) >>
   fs[] >>
   (* h and x0 must be the same since 0 steps were taken: but contradiction
    * since step counter says no steps were taken *)
   imp_res_tac bigstep_stmt_exec_imp >>
   fs[]
  ) >>
  gs[] >>
  (* Use induction hypothesis *)
  res_tac >>
  fs[]
 ),

 (* transition *)
 Cases_on ‘t’ >> (
  fs[stmt_exec]
 ) >> (
  Cases_on ‘is_v e’ >> (
   fs[]
  ) >- (
   Cases_on ‘is_v_str e’ >> (
    fs[]
   ) >> (
    Cases_on ‘e’ >> (
     fs[is_v, is_v_str]
    ) >>
    Cases_on ‘v’ >> (
     fs[is_v, is_v_str]
    ) >> (
     (* Contradiction, since only expression reduction can be done for transition *)
     fs[bigstep_stmt_exec_def, bigstep_e_exec_def]
    )
   )
  ) >>
  (* nested e reduction *)
  fs[bigstep_stmt_exec_def] >>
  Cases_on ‘bigstep_e_exec (top_scope::(scope_list ++ g_scope_list')) (INL e) 0’ >> (
   fs[]
  ) >>
  PairCases_on ‘x’ >>
  Cases_on ‘x0’ >> (
   fs[]
  ) >>
  gvs[] >>
  FULL_SIMP_TAC pure_ss [GSYM listTheory.APPEND] >>
  imp_res_tac bigstep_e_exec_sound >>
  fs[] >>
  irule scope_lists_separate >>
  metis_tac[]
 ),

 (* apply *)
 Cases_on ‘t’ >> (
  fs[stmt_exec]
 ) >> (
  Cases_on ‘index_not_const l’ >> (
   fs[]
  ) >- (
   (* Contradiction on l being reduced, while index_not_const l = NONE *)
   fs[bigstep_stmt_exec_def] >>
   Cases_on ‘bigstep_e_exec (top_scope::(scope_list ++ g_scope_list')) (INR l) 0’ >> (
    fs[]
   ) >>
   PairCases_on ‘x’ >>
   fs[] >>
   Cases_on ‘x0’ >> (
    fs[]
   ) >>
   gvs[] >>
   FULL_SIMP_TAC pure_ss [GSYM listTheory.APPEND] >>
   imp_res_tac bigstep_e_exec_sound >>
   Cases_on ‘l’ >> (
    fs[bigstep_e_exec_def]
   ) >>
   PAT_X_ASSUM “!tbl_map pars_map func_map ext_map b_func_map apply_table_f. _” (fn thm => ASSUME_TAC (Q.SPECL [‘x''’, ‘pars_map’, ‘func_map’, ‘ext_map’, ‘x'’, ‘apply_table_f’] thm)) >>
   fs[] >>
   subgoal ‘!h. index_not_const (h::t) = unred_mem_index (h::t)’ >- (
    fs[index_not_const_def, unred_mem_index_def, unred_mem_def]
   ) >>
   fs[]
  ) >>
  (* e reduction *)
  fs[bigstep_stmt_exec_def] >>
  Cases_on ‘bigstep_e_exec (top_scope::(scope_list ++ g_scope_list')) (INR l) 0’ >> (
   fs[]
  ) >>
  PairCases_on ‘x'3'’ >>
  fs[] >>
  Cases_on ‘x'''0’ >> (
   gvs[]
  ) >>
  FULL_SIMP_TAC pure_ss [GSYM listTheory.APPEND] >>
  imp_res_tac bigstep_e_exec_sound >>
  Cases_on ‘l’ >> (
   fs[bigstep_e_exec_def]
  ) >>
  PAT_X_ASSUM “!tbl_map pars_map func_map ext_map b_func_map apply_table_f. _” (fn thm => ASSUME_TAC (Q.SPECL [‘x''’, ‘pars_map’, ‘func_map’, ‘ext_map’, ‘x'’, ‘apply_table_f’] thm)) >>
  fs[] >>
  subgoal ‘!h. index_not_const (h::t) = unred_mem_index (h::t)’ >- (
   fs[index_not_const_def, unred_mem_index_def, unred_mem_def]
  ) >>
  gvs[] >>
  FULL_SIMP_TAC pure_ss [GSYM listTheory.APPEND] >>
  irule scope_lists_separate >>
  fs[] >>
  qexists_tac ‘((top_scope::scope_list) ++ g_scope_list')’ >>
  fs[]
 ),

 (* ext *)
 fs[bigstep_stmt_exec_def]
]
QED


Definition in_local_fun_def:
 (in_local_fun func_map (arch_frame_list_regular ((funn_name fname, stmt_stack, scope_list)::frame_list)) =
  (ALOOKUP func_map fname = NONE)) /\
 (in_local_fun func_map _ = F)
End

(* TODO: Add constraint that scope_list must be non-empty *)
Definition in_local_fun'_def:
 (in_local_fun' ((ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map):'a actx) (arch_frame_list_regular ((funn_name fname, stmt_stack, scope_list)::frame_list)) n =
  ((ALOOKUP func_map fname = NONE) /\ n <> 0)) /\
 (in_local_fun' ctx _ _ = F)
End

(*
Theorem bigstep_arch_exec_sound_NONE:
!i ab_list x el pblock_map pbl_type x_d_list b_func_map decl_list pars_map tbl_map funn stmt_stack top_scope scope_list frame_list func_map in_out_list in_out_list' ascope g_scope_list g_scope_list' g_scope_list'' arch_frame_list' n g_scope_list''' ffblock_map input_f output_f copyin_pbl copyout_pbl apply_table_f ext_map.
(EL i ab_list = (arch_block_pbl x el)) ==>
(ALOOKUP pblock_map x = SOME (pbl_type, x_d_list, b_func_map, decl_list, pars_map, tbl_map)) ==>
~(state_fin_exec status_running ((funn, stmt_stack, (top_scope::scope_list))::frame_list)) ==>
scopes_to_pass funn func_map b_func_map g_scope_list = SOME g_scope_list' ==>
map_to_pass funn b_func_map <> NONE ==>
tbl_to_pass funn b_func_map tbl_map <> NONE ==>
bigstep_arch_exec (NONE:('a actx # b_func_map) option) (g_scope_list':g_scope_list) (arch_frame_list_regular ((funn, stmt_stack, (top_scope::scope_list))::frame_list)) = SOME (g_scope_list'', arch_frame_list', n) ==>
in_local_fun func_map arch_frame_list' ==>
scopes_to_retrieve funn func_map b_func_map g_scope_list g_scope_list'' = SOME g_scope_list''' ==>
arch_multi_exec ((ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map):'a actx) ((i, in_out_list, in_out_list', ascope), g_scope_list, (arch_frame_list_regular ((funn, stmt_stack, (top_scope::scope_list))::frame_list)), status_running) n = SOME ((i, in_out_list, in_out_list', ascope), g_scope_list''', arch_frame_list', status_running)
Proof
cheat
QED
*)

Theorem bigstep_arch_exec_zero:
!g_scope_list arch_frame_list g_scope_list' arch_frame_list'.
bigstep_arch_exec NONE g_scope_list arch_frame_list =
 SOME (g_scope_list',arch_frame_list',0) ==>
g_scope_list = g_scope_list' /\ arch_frame_list = arch_frame_list'
Proof
rpt gen_tac >>
rpt disch_tac >>
Cases_on ‘g_scope_list’ >> (
 fs[bigstep_arch_exec_def]
) >>
Cases_on ‘t’ >> (
 fs[bigstep_arch_exec_def]
) >>
Cases_on ‘t'’ >> Cases_on ‘arch_frame_list’ >> (
 fs[bigstep_arch_exec_def]
) >>
Cases_on ‘l’ >> (
 fs[bigstep_arch_exec_def]
) >>
PairCases_on ‘h''’ >>
fs[] >>
Cases_on ‘h''1’ >> (
 fs[]
) >>
fs[bigstep_exec_def] >>
rpt strip_tac >> (
 Cases_on ‘bigstep_stmt_exec NONE (h''2 ++ [h; h']) h'' 0’ >> (
  fs[]
 ) >>
 PairCases_on ‘x’ >> (
  fs[]
 ) >>
 Cases_on ‘separate x1’ >> (
  fs[]
 ) >>
 Cases_on ‘q’ >> (
  fs[]
 ) >>
 Cases_on ‘r’ >> (
  fs[]
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

(*
Theorem bigstep_stmt_exec_stmt_unchanged:
!ctx_b_func_map_opt scope_lists scope_lists' stmt n m.
bigstep_stmt_exec (ctx_b_func_map_opt:(func_map # b_func_map # 'a ext_map) option) scope_lists stmt n = SOME (stmt, scope_lists', m) ==>
n = m
Proof
cheat
QED
*)

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
 fs[bigstep_arch_exec_def]
) >>
Cases_on ‘t’ >- (
 fs[bigstep_arch_exec_def]
) >>
fs[] >>
Cases_on ‘arch_frame_list’ >> (
 fs[bigstep_arch_exec_def]
) >>
Cases_on ‘t'’ >> (
 fs[bigstep_arch_exec_def]
) >>
Cases_on ‘l’ >> (
 fs[]
) >>
PairCases_on ‘h''’ >>
fs[] >>
Cases_on ‘h''1’ >> (
 fs[]
) >>
Cases_on ‘bigstep_exec
             (case ctx_b_func_map_opt of
                NONE => NONE
              | SOME
                ((ab_list,pblock_map,ffblock_map,input_f,output_f,copyin_pbl,
                  copyout_pbl,apply_table_f,ext_map,func_map),b_func_map) =>
                SOME (func_map,b_func_map,ext_map)) ([h; h'],h''2)
             h''’ >> (
 fs[]
) >>
PairCases_on ‘x’ >>
fs[] >>
metis_tac[]
QED

(* TODO: Move *)
Theorem arch_multi_exec_arch_frame_list_regular:
!ab_list pblock_map ffblock_map input_f output_f copyin_pbl
 copyout_pbl apply_table_f ext_map func_map aenv g_scope_list g_scope_list' frame_list frame_list' n i io_list io_list' ascope.
arch_multi_exec (ab_list,pblock_map,ffblock_map,input_f,output_f,copyin_pbl,
        copyout_pbl,apply_table_f,ext_map,func_map)
          (aenv,g_scope_list,arch_frame_list_regular frame_list,
           status_running) (SUC n) =
        SOME
          ((i,io_list,io_list',ascope),g_scope_list',
           arch_frame_list_regular frame_list',status_running) ==>
?x el pbl_type x_d_list b_func_map decl_list pars_map tbl_map.
 EL i ab_list = arch_block_pbl x el /\
 ALOOKUP pblock_map x =
          SOME (pbl_type,x_d_list,b_func_map,decl_list,pars_map,tbl_map)
Proof
rpt strip_tac >>
(* TODO: Requires n to be greater than 0... *)
fs[SUC_ADD_ONE] >>
FULL_SIMP_TAC pure_ss [Once arithmeticTheory.ADD_SYM] >>
fs[arch_multi_exec_add] >>
Cases_on ‘arch_multi_exec
             (ab_list,pblock_map,ffblock_map,input_f,output_f,copyin_pbl,
              copyout_pbl,apply_table_f,ext_map,func_map)
             (aenv,g_scope_list,arch_frame_list_regular frame_list,
              status_running) n’ >> (
 fs[]
) >>
PairCases_on ‘x’ >>
fs[] >>
FULL_SIMP_TAC pure_ss [Once arithmeticTheory.ONE] >>
fs[arch_multi_exec_def] >>
Cases_on ‘x5’ >- (
 Cases_on ‘x6’ >> (
  fs[arch_exec_def]
 ) >>
 Cases_on ‘EL x0 ab_list’ >> (
  fs[]
 ) >| [
  Cases_on ‘input_f (x1,x3)’ >> (
   fs[]
  ) >>
  PairCases_on ‘x’ >>
  fs[],

  Cases_on ‘ALOOKUP pblock_map s’ >> (
   fs[]
  ) >>
  PairCases_on ‘x’ >>
  fs[] >>
  Cases_on ‘lookup_block_body s x2'’ >> (
   fs[]
  ) >>
  Cases_on ‘LENGTH l = LENGTH x1'’ >> (
   fs[]
  ) >>
  Cases_on ‘copyin_pbl (MAP FST x1',MAP SND x1',l,x3)’ >> (
   fs[]
  ) >>
  Cases_on ‘oLASTN 1 x4’ >> (
   fs[]
  ) >>
  Cases_on ‘x''’ >> (
   fs[]
  ) >>
  Cases_on ‘t’ >> (
   fs[]
  ) >>
  Cases_on ‘initialise_var_stars func_map x2' ext_map
               [declare_list_in_scope (x3',x'); h]’ >> (
   fs[]
  ) >>
  gvs[],

  Cases_on ‘ALOOKUP ffblock_map s’ >> (
   fs[]
  ) >>
  Cases_on ‘x’ >>
  fs[] >>
  Cases_on ‘f x3’ >> (
   fs[]
  ),

  Cases_on ‘output_f (x2,x3)’ >> (
   fs[]
  ) >>
  PairCases_on ‘x’ >>
  fs[]
 ]
) >>
fs[arch_exec_def] >>
Cases_on ‘EL x0 ab_list’ >> (
 fs[]
) >>
Cases_on ‘ALOOKUP pblock_map s’ >> (
 fs[]
) >>
PairCases_on ‘x’ >>
fs[] >>
Cases_on ‘state_fin_exec x6 l’ >> (
 fs[]
) >- (
 Cases_on ‘lookup_block_body s x2'’ >> (
  fs[]
 ) >>
 Cases_on ‘LENGTH l' = LENGTH x1'’ >> (
  fs[]
 ) >>
 Cases_on ‘copyout_pbl
              (x4,x3,MAP SND x1',MAP FST x1',set_fin_status x0' x6)’ >> (
  fs[]
 )
) >>
Cases_on ‘x6’ >> (
 fs[]
) >- (
 Cases_on ‘frames_exec (apply_table_f,ext_map,func_map,x2',x4',x5)
              (x3,x4,l,status_running)’ >> (
  fs[]
 ) >>
 PairCases_on ‘x’ >>
 fs[] >>
 gvs[]
) >>
Cases_on ‘x0'’ >> (
 fs[]
) >>
Cases_on ‘ALOOKUP x4' s'’ >> (
 fs[]
) >>
gvs[]
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
!n h ascope g_scope1 g_scope2 funn x0 g_scope_list' x2 actx ctx aenv h0 h' t t' t''.
stmt_multi_exec' (ctx:'a ctx) (ascope, [g_scope1; g_scope2]:g_scope_list, [(funn,[h],h'::t'')], status_running) n =
 SOME (ascope,g_scope_list',[(funn, [x0], x2)],status_running) ==>
 arch_multi_exec' (actx:'a actx)
  (aenv,[g_scope1; g_scope2],
   arch_frame_list_regular ((h0,h::t',h'::t'')::t),status_running) n =
   SOME
    (aenv,g_scope_list',arch_frame_list_regular ((h0,x0::t',x2)::t),
     status_running)
Proof
Induct_on ‘n’ >> (
 rpt strip_tac >>
 fs[arch_multi_exec'_def, stmt_multi_exec'_def]
) >>
Cases_on ‘stmt_multi_exec' ctx
            (ascope,[g_scope1; g_scope2],[(funn,[h],h'::t'')],status_running)
            n’ >> (
 fs[]
) >>
PairCases_on ‘x’ >>
fs[] >>
(* TODO: Change stmt_multi_exec' to return NONE if any if the below are
 * broken. This shouldn't be any problem for soundness theorems since the bigstep
 * semantics keeps these invariants *)
subgoal ‘x0' = ascope /\
         ?g_scope1' g_scope2'. x1 = [g_scope1'; g_scope2'] /\
         ?stmt' h'' t'''. x2' = [(funn,[stmt'],h''::t''')] /\
         x3 = status_running ’ >- (
 cheat
) >>
fs[] >>
res_tac >>
PairCases_on ‘actx’ >>
PairCases_on ‘aenv’ >>
fs[arch_exec_def] >>
(* From top-level soundness theorem/ composition theorem *)
subgoal ‘?x el. EL aenv0 actx0 = arch_block_pbl x el’ >- (
 cheat
) >>
fs[] >>
subgoal ‘?pbl_type x_d_list b_func_map decl_list pars_map tbl_map. ALOOKUP actx1 x = SOME (pbl_type,x_d_list,b_func_map,decl_list,pars_map,tbl_map)’ >- (
 cheat
) >>
fs[] >>
subgoal ‘~state_fin_exec status_running ((h0,stmt'::t',h''::t'³')::t)’ >- (
 cheat
) >>
Cases_on ‘t’ >> (
 fs[]
) >- (
 fs[frames_exec] >>
 (* Needs all the to-pass information + identification of components of stmt_exec *)
 cheat
) >>
PairCases_on ‘h'3'’ >>
fs[frames_exec] >>
(* Needs all the to-pass information + identification of components of stmt_exec *)
cheat
QED

Theorem bigstep_arch_exec_sound_n:
!n g_scope_list g_scope_list' frame_list frame_list' aenv actx.
bigstep_arch_exec (NONE:('a actx # b_func_map) option) g_scope_list (arch_frame_list_regular frame_list) = SOME (g_scope_list', (arch_frame_list_regular frame_list'), n) ==>
arch_multi_exec' (actx:'a actx) ((aenv:'a aenv), g_scope_list, arch_frame_list_regular frame_list, status_running) n = SOME (aenv, g_scope_list', arch_frame_list_regular frame_list', status_running)
Proof
Cases_on ‘frame_list’ >- (
 rpt strip_tac >>
 imp_res_tac bigstep_arch_exec_SOME_imp >>
 fs[bigstep_arch_exec_def]
) >>
rpt strip_tac >>
imp_res_tac bigstep_arch_exec_SOME_imp >>
fs[arch_multi_exec'_def, bigstep_arch_exec_def] >>
Cases_on ‘frame_list’ >> (
 fs[]
) >>
PairCases_on ‘h'’ >>
fs[] >>
Cases_on ‘h'1’ >> (
 fs[]
) >>
Cases_on ‘bigstep_exec NONE ([g_scope1; g_scope2],h'2) h'’ >> (
 fs[]
) >>
PairCases_on ‘x’ >>
fs[] >>
gvs[] >>
fs[bigstep_exec_def] >>
Cases_on ‘bigstep_stmt_exec NONE (h'2 ++ [g_scope1; g_scope2]) h' 0’ >> (
 fs[]
) >>
PairCases_on ‘x’ >>
fs[] >>
Cases_on ‘separate x1’ >> (
 fs[]
) >>
Cases_on ‘q’ >> (
 fs[]
) >>
Cases_on ‘r’ >> (
 fs[]
) >>
gvs[] >>
(* Scope list non-empty should probably be added to in_local_fun' assumption, which can then be passed along to this theorem *)
Cases_on ‘h'2’ >- (
 cheat
) >>
(* TODO: We should be able to prove here that no ext was reduced by bigstep_arch_exec, in particular that next stmt to be reduced is not an ext *)
imp_res_tac bigstep_stmt_exec_sound_n >>
fs[] >>
res_tac >>
metis_tac[bigstep_arch_exec_sound_n_stmt]
QED

Theorem arch_multi_exec'_sound:
!n g_scope_list g_scope_list' frame_list arch_frame_list' aenv aenv' actx status'.
arch_multi_exec' (actx:'a actx) ((aenv:'a aenv), g_scope_list, arch_frame_list_regular frame_list, status_running) n = SOME (aenv', g_scope_list', arch_frame_list', status') ==>
arch_multi_exec (actx:'a actx) (aenv, g_scope_list, arch_frame_list_regular frame_list, status_running) n = SOME (aenv', g_scope_list', arch_frame_list', status')
Proof
Induct_on ‘n’ >- (
 rpt strip_tac >>
 fs[arch_multi_exec'_def, arch_multi_exec_def]
) >>
rpt strip_tac >>
fs[arch_multi_exec'_def] >>
Cases_on ‘arch_multi_exec' actx
             (aenv,g_scope_list,arch_frame_list_regular frame_list,
              status_running) n’ >> (
 fs[]
) >>
PairCases_on ‘x’ >>
res_tac >>
(* Use theorem to split execution of arch_multi_exec into 1+n *)
FULL_SIMP_TAC pure_ss [SUC_ADD_ONE, Once arithmeticTheory.ADD_SYM] >>
FULL_SIMP_TAC pure_ss [arch_multi_exec_add, Once arithmeticTheory.ONE] >>
fs[arch_multi_exec_def]
QED


Theorem arch_multi_exec_sound:
!n g_scope_list g_scope_list' frame_list arch_frame_list' aenv aenv' actx status' .
arch_multi_exec (actx:'a actx) ((aenv:'a aenv), g_scope_list, arch_frame_list_regular frame_list, status_running) n = SOME (aenv', g_scope_list', arch_frame_list', status') ==>
arch_multi_exec' (actx:'a actx) (aenv, g_scope_list, arch_frame_list_regular frame_list, status_running) n = SOME (aenv', g_scope_list', arch_frame_list', status')
Proof
Induct_on ‘n’ >- (
 rpt strip_tac >>
 fs[arch_multi_exec'_def, arch_multi_exec_def]
) >>
rpt strip_tac >>
FULL_SIMP_TAC pure_ss [SUC_ADD_ONE, Once arithmeticTheory.ADD_SYM] >>
FULL_SIMP_TAC pure_ss [arch_multi_exec_add, Once arithmeticTheory.ONE] >>
Cases_on ‘arch_multi_exec actx
             (aenv,g_scope_list,arch_frame_list_regular frame_list,
              status_running) n’ >> (
 fs[]
) >>
PairCases_on ‘x’ >>
res_tac >>
fs[arch_multi_exec'_def, GSYM SUC_ADD_ONE] >>
FULL_SIMP_TAC pure_ss [Once arithmeticTheory.ONE] >>
fs[arch_multi_exec_def] >>
Cases_on ‘arch_exec actx ((x0,x1,x2,x3),x4,x5,x6)’ >> (
 fs[]
) >>
PairCases_on ‘x’ >>
fs[]
QED


Theorem bigstep_arch_exec_comp'_NONE:
!n' n assl ctx g_scope_list frame_list aenv' g_scope_list' g_scope_list'' arch_frame_list' arch_frame_list'' aenv.
(assl ==> arch_multi_exec ctx (aenv, g_scope_list, arch_frame_list_regular frame_list, status_running) n = SOME (aenv', g_scope_list', arch_frame_list', status_running)) ==>
in_local_fun' (ctx:'a actx) arch_frame_list' n ==>
bigstep_arch_exec (NONE:('a actx # b_func_map) option) (g_scope_list':g_scope_list) arch_frame_list' = SOME (g_scope_list'', arch_frame_list'', n') ==>
(assl ==> arch_multi_exec ctx (aenv, g_scope_list, arch_frame_list_regular frame_list, status_running) (n+n') = SOME (aenv', g_scope_list'', arch_frame_list'', status_running))
Proof
rpt strip_tac >>
irule arch_multi_exec_comp_n_tl >>
imp_res_tac bigstep_arch_exec_SOME_imp >>
gvs[] >>
imp_res_tac bigstep_arch_exec_sound_n >>
metis_tac[arch_multi_exec'_sound]
QED

Theorem bigstep_arch_exec_comp'_SOME:
!assl ctx g_scope_list arch_frame_list status aenv' g_scope_list' g_scope_list'' n' arch_frame_list' arch_frame_list'' n aenv.
(assl ==> arch_multi_exec ctx (aenv, g_scope_list, arch_frame_list, status) n = SOME (aenv', g_scope_list', arch_frame_list', status_running)) ==>
in_local_fun' ctx arch_frame_list' n ==>
bigstep_arch_exec' (SOME (aenv', ctx)) (g_scope_list':g_scope_list) arch_frame_list' = SOME (g_scope_list'', arch_frame_list'', n') ==>
(assl ==> arch_multi_exec ctx (aenv, g_scope_list, arch_frame_list, status_running) (n+n') = SOME (aenv', g_scope_list'', arch_frame_list'', status_running))
Proof
cheat
QED

val _ = export_theory ();
