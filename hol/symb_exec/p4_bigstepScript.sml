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

(* Alternative experimental version for easier proofs *)
Definition bigstep_e_exec'_def:
 (********************)
 (* Variable look-up *)
 (bigstep_e_exec' (scope_lists:scope_list) (INL (e_var x)) n =
  case lookup_vexp scope_lists x of
  | SOME v => SOME (INL $ e_v v, n + 1)
  | NONE => NONE)
  /\
 (******************************)
 (* Struct/header field access *)
 (bigstep_e_exec' scope_lists (INL (e_acc e_v_struct x)) n =
  (case bigstep_e_exec' scope_lists (INL e_v_struct) n of
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
 (bigstep_e_exec' scope_lists (INL (e_struct x_e_l)) n =
  case bigstep_e_exec' scope_lists (INR (MAP SND x_e_l)) n of
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
 (bigstep_e_exec' scope_lists (INL (e_cast cast e)) n =
  (case bigstep_e_exec' scope_lists (INL e) n of
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
 (bigstep_e_exec' scope_lists (INL (e_unop unop e)) n =
  (case bigstep_e_exec' scope_lists (INL e) n of
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
 (bigstep_e_exec' scope_lists (INL (e_binop e1 binop e2)) n =
  (case bigstep_e_exec' scope_lists (INL e1) n of
   | SOME (INL $ e1', n') =>
    (case e1' of
     | (e_v v) =>
      if is_short_circuitable binop
      then
       (case e_exec_short_circuit v binop e2 of
        | SOME e' => SOME (INL $ e', n'+1)
        | NONE => NONE)
      else
       (case bigstep_e_exec' scope_lists (INL e2) n' of
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
 (bigstep_e_exec' scope_lists (INL (e_concat e1 e2)) n =
  case bigstep_e_exec' scope_lists (INL e1) n of
  | SOME (INL $ e1', n') =>
   if is_v_bit e1'
   then
    (case bigstep_e_exec' scope_lists (INL e2) n' of
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
 (bigstep_e_exec' scope_lists (INL (e_slice e1 e2 e3)) n =
  if (is_v_bit e2 /\ is_v_bit e3)
  then
   (case bigstep_e_exec' scope_lists (INL e1) n of
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
 (bigstep_e_exec' scope_lists (INL (e_call funn e_l)) n =
  case bigstep_e_exec' scope_lists (INR e_l) n of
  | SOME (INR $ e_l', n') =>
   SOME (INL $ e_call funn e_l', n')
  | _ => NONE)
 /\
*)
 (**********)
 (* Select *)
 (bigstep_e_exec' scope_lists (INL (e_select e s_l_x_l x)) n =
  case bigstep_e_exec' scope_lists (INL e) n of
  | SOME (INL $ e', n') =>
   SOME (INL $ e_select e' s_l_x_l x, n')
  | _ => NONE)
 /\
 (bigstep_e_exec' scope_lists (INL e) n = SOME (INL $ e,n))
 /\
 (bigstep_e_exec' scope_lists (INR []) n = SOME (INR $ [],n))
 /\
 (bigstep_e_exec' scope_lists (INR (h::t)) n =
  case bigstep_e_exec' scope_lists (INL h) n of
  | SOME (INL h', n') =>
   if is_v h'
   then
    (case bigstep_e_exec' scope_lists (INR t) n' of
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
  then bigstep_e_exec' scope_lists (INL e) n
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
    (case bigstep_e_exec' scope_lists (INL e) n of
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
  (case bigstep_e_exec' scope_lists (INL e) n of
   | SOME (INL e', n') =>
    SOME (stmt_ret e', scope_lists, n')
   | _ => NONE))
  /\
 (bigstep_stmt_exec func_maps_opt scope_lists (stmt_trans e) n =
  (case bigstep_e_exec' scope_lists (INL e) n of
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
    (case bigstep_e_exec' scope_lists (INL e) n of
     | SOME (INL e', n') =>
      SOME (stmt_cond e' stmt1 stmt2, scope_lists, n')
     | _ => NONE)))
  /\
 (bigstep_stmt_exec func_maps_opt scope_lists (stmt_app t_name e_l) n =
  (case bigstep_e_exec' scope_lists (INR e_l) n of
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
 (bigstep_arch_exec ctx_b_func_map_opt (g_scope_list:g_scope_list) (arch_frame_list_regular frame_list) =
  case frame_list of
  | ((funn, stmt_stack, scope_list)::t) =>
   (case stmt_stack of
    | (stmt::t') =>
     let func_maps_opt = (case ctx_b_func_map_opt of
                          | NONE => NONE
                          | SOME (((ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map):'a actx), b_func_map) => SOME (func_map, b_func_map, ext_map)) in
       (case bigstep_exec func_maps_opt (g_scope_list, scope_list) stmt of
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
 (bigstep_arch_exec' (aenv_ctx_opt:('a aenv # 'a actx) option) (g_scope_list:g_scope_list) (arch_frame_list_regular frame_list) =
  case aenv_ctx_opt of
  | NONE => bigstep_arch_exec (NONE:('a actx # b_func_map) option) (g_scope_list:g_scope_list) (arch_frame_list_regular frame_list)
  | SOME ((i, _, _, _), (ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map)) =>
   (case EL i ab_list of
    | (arch_block_pbl x el) =>
     (case ALOOKUP pblock_map x of
      | SOME (_, _, b_func_map, _, _, _) =>
       bigstep_arch_exec (SOME ((ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map), b_func_map)) (g_scope_list:g_scope_list) (arch_frame_list_regular frame_list)
      | NONE => NONE)
    | _ => NONE)
 ) /\
 (bigstep_arch_exec' _ _ _ = NONE)
End

val bigstep_e_exec_case_tac =
 Cases_on ‘bigstep_e_exec' scope_lists (INL e'') 0’ >> (
  fs[]
 ) >>
 PairCases_on ‘x’ >>
 fs[]
;

val bigstep_e_exec_case'_tac =
 Cases_on ‘bigstep_e_exec' scope_lists (INL e) n’ >> (
  fs[]
 ) >>
 PairCases_on ‘x’ >>
 fs[]
;

 (* TODO
val induct_traverse_e_then_tac tac =

;
*)

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

Theorem bigstep_e_exec'_var_REWR:
!scope_lists var n t' m v.
bigstep_e_exec' scope_lists (INL (e_var var)) n = SOME (t',m) <=>
(m = n + 1 /\ ?v. SOME v =  lookup_vexp scope_lists var /\ t' = (INL $ e_v v))
Proof
rpt strip_tac >>
eq_tac >> (
 rpt strip_tac >>
 fs[bigstep_e_exec'_def] >>
 Cases_on ‘lookup_vexp scope_lists var’ >> (
  fs[]
 )
)
QED

Theorem bigstep_e_exec'_var_REWR:
!scope_lists var n t' m v.
bigstep_e_exec' scope_lists (INL (e_var var)) n = SOME (t',m) <=>
 (m = n + 1 /\ ?v. SOME v =  lookup_vexp scope_lists var /\ t' = (INL $ e_v v))
Proof
rpt strip_tac >>
eq_tac >> (
 rpt strip_tac >>
 fs[bigstep_e_exec'_def] >>
 Cases_on ‘lookup_vexp scope_lists var’ >> (
  fs[]
 )
)
QED

Theorem bigstep_e_exec'_acc_REWR:
!scope_lists x s n t' m.
bigstep_e_exec' scope_lists (INL (e_acc x s)) n = SOME (t',m) <=>
 ?n' e_v_struct.
 bigstep_e_exec' scope_lists (INL x) n = SOME (INL e_v_struct, n') /\
 ((is_v e_v_struct /\ ?e'. e_exec_acc (e_acc e_v_struct s) = SOME e' /\ m = n' + 1 /\
  t' = (INL e')) \/
 (~is_v e_v_struct /\ t' = (INL (e_acc e_v_struct s)) /\ m = n'))
Proof
rpt strip_tac >>
eq_tac >> (
 rpt strip_tac >>
 fs[bigstep_e_exec'_def]
) >- (
 Cases_on ‘bigstep_e_exec' scope_lists (INL x) n’ >> (
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

Theorem bigstep_e_exec'_unop_REWR:
!scope_lists unop e n t' m.
bigstep_e_exec' scope_lists (INL (e_unop unop e)) n = SOME (t',m) <=>
 ?e' n'.
 bigstep_e_exec' scope_lists (INL e) n = SOME (INL e', n') /\
 ((is_v e' /\ ?v. e_exec_unop unop e' = SOME v /\ m = n' + 1 /\
  t' = (INL $ e_v v)) \/
 (~is_v e' /\ t' = (INL (e_unop unop e')) /\ m = n'))
Proof
rpt strip_tac >>
eq_tac >> (
 rpt strip_tac >>
 fs[bigstep_e_exec'_def]
) >>
Cases_on ‘bigstep_e_exec' scope_lists (INL e) n’ >> (
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

Theorem bigstep_e_exec'_cast_REWR:
!scope_lists cast x n t' m.
bigstep_e_exec' scope_lists (INL (e_cast cast x)) n = SOME (t',m) <=>
 ?n' e'.
 bigstep_e_exec' scope_lists (INL x) n = SOME (INL e', n') /\
 ((is_v e' /\ ?v. e_exec_cast cast e' = SOME v /\ m = n' + 1 /\
  t' = (INL $ e_v v)) \/
 (~is_v e' /\ t' = (INL (e_cast cast e')) /\ m = n'))
Proof
rpt strip_tac >>
eq_tac >> (
 rpt strip_tac >>
 fs[bigstep_e_exec'_def]
) >- (
 Cases_on ‘bigstep_e_exec' scope_lists (INL x) n’ >> (
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

Theorem bigstep_e_exec'_binop_REWR:
!scope_lists binop e1 e2 n t' m.
bigstep_e_exec' scope_lists (INL (e_binop e1 binop e2)) n = SOME (t',m) <=>
 ?e1' n'.
 bigstep_e_exec' scope_lists (INL e1) n = SOME (INL e1', n') /\
 ((is_v e1' /\
  ((is_short_circuitable binop /\
    ?v e'.
     (e1' = e_v v /\
      e_exec_short_circuit v binop e2 = SOME e' /\
      t' = INL e' /\ m = n' + 1)) \/
   (~is_short_circuitable binop /\
    ?e2' n''.
     bigstep_e_exec' scope_lists (INL e2) n' = SOME (INL e2', n'') /\
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
 fs[bigstep_e_exec'_def]
) >- (
 Cases_on ‘bigstep_e_exec' scope_lists (INL e1) n’ >> (
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
 Cases_on ‘bigstep_e_exec' scope_lists (INL e2) x1’ >> (
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

Theorem bigstep_e_exec'_concat_REWR:
!scope_lists e1 e2 n t' m.
bigstep_e_exec' scope_lists (INL (e_concat e1 e2)) n = SOME (t',m) <=>
 ?e1' n'.
 bigstep_e_exec' scope_lists (INL e1) n = SOME (INL e1', n') /\
 ((is_v_bit e1' /\
  (?e2' n''.
    bigstep_e_exec' scope_lists (INL e2) n' = SOME (INL e2', n'') /\
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
 fs[bigstep_e_exec'_def]
) >>
Cases_on ‘bigstep_e_exec' scope_lists (INL e1) n’ >> (
 fs[]
) >>
PairCases_on ‘x’ >>
fs[] >>
Cases_on ‘x0’ >>
fs[] >>
Cases_on ‘is_v_bit x’ >> (
 fs[]
) >>
Cases_on ‘bigstep_e_exec' scope_lists (INL e2) x1’ >> (
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

Theorem bigstep_e_exec'_slice_REWR:
!scope_lists e1 e2 e3 n t' m.
bigstep_e_exec' scope_lists (INL (e_slice e1 e2 e3)) n = SOME (t',m) <=>
 is_v_bit e2 /\ is_v_bit e3 /\
 ?e1' n'.
 bigstep_e_exec' scope_lists (INL e1) n = SOME (INL e1', n') /\
 ((is_v_bit e1' /\
  (?v. e_exec_slice e1' e2 e3 = SOME v /\
   t' = (INL $ e_v v) /\ m = n' + 1)) \/
  (~is_v_bit e1' /\ t' = (INL (e_slice e1' e2 e3)) /\ m = n'))
Proof
rpt strip_tac >>
eq_tac >> (
 rpt strip_tac >>
 fs[bigstep_e_exec'_def]
) >>
Cases_on ‘bigstep_e_exec' scope_lists (INL e1) n’ >> (
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

Theorem bigstep_e_exec'_select_REWR:
!scope_lists e s_l_x_l x n t' m.
bigstep_e_exec' scope_lists (INL (e_select e s_l_x_l x)) n = SOME (t',m) <=>
 ?e' n'.
 bigstep_e_exec' scope_lists (INL e) n = SOME (INL e', n') /\
 t' = (INL (e_select e' s_l_x_l x)) /\ m = n'
Proof
rpt strip_tac >>
eq_tac >> (
 rpt strip_tac >>
 fs[bigstep_e_exec'_def]
) >>
Cases_on ‘bigstep_e_exec' scope_lists (INL e) n’ >> (
 fs[]
) >>
PairCases_on ‘x'’ >>
fs[] >>
Cases_on ‘x'0’ >>
fs[]
QED

Theorem bigstep_e_exec'_struct_REWR:
!scope_lists x_e_l n t' m.
bigstep_e_exec' scope_lists (INL (e_struct x_e_l)) n = SOME (t',m) <=>
 ?e_l' n'.
 bigstep_e_exec' scope_lists (INR (MAP SND x_e_l)) n = SOME (INR e_l', n') /\
 ((EVERY is_v e_l' /\ t' = (INL (e_v (v_struct (ZIP (MAP FST x_e_l,vl_of_el e_l'))))) /\ m = n' + 1) \/
  (~(EVERY is_v e_l') /\ t' = (INL (e_struct (ZIP (MAP FST x_e_l,e_l')))) /\ m = n')
 )
Proof
rpt strip_tac >>
eq_tac >> (
 rpt strip_tac >>
 fs [bigstep_e_exec'_def]
) >- (
 Cases_on ‘bigstep_e_exec' scope_lists (INR (MAP SND x_e_l)) n’ >> (
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

val bigstep_e_exec'_ind_hyp_tac =
 PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
 fs[e_size_def] >>
 res_tac >>
 decide_tac
;

val bigstep_e_exec'_2_ind_hyp_tac =
 PAT_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
 PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x')’] thm)) >>
 fs[e_size_def] >>
 res_tac >>
 decide_tac
;

Theorem bigstep_e_exec'_incr:
!t n scope_lists t' m.
bigstep_e_exec' scope_lists t n = SOME (t', m) ==>
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
  fs[bigstep_e_exec'_def],

  (* var *)
  fs[bigstep_e_exec'_var_REWR],

  (* list *)
  fs[bigstep_e_exec'_def],

  (* acc *)
  fs[bigstep_e_exec'_acc_REWR] >>
  rpt strip_tac >> (
   bigstep_e_exec'_ind_hyp_tac
  ),

  (* unop *)
  fs[bigstep_e_exec'_unop_REWR] >>
  rpt strip_tac >> (
   bigstep_e_exec'_ind_hyp_tac
  ),

  (* cast *)
  fs[bigstep_e_exec'_cast_REWR] >>
  rpt strip_tac >> (
   bigstep_e_exec'_ind_hyp_tac
  ),

  (* binop *)
  fs[bigstep_e_exec'_binop_REWR] >>
  rpt strip_tac >- (
   bigstep_e_exec'_ind_hyp_tac
  ) >- (
   bigstep_e_exec'_2_ind_hyp_tac
  ) >- (
   bigstep_e_exec'_2_ind_hyp_tac
  ) >>
  bigstep_e_exec'_ind_hyp_tac,


  (* concat *)
  fs[bigstep_e_exec'_concat_REWR] >>
  rpt strip_tac >- (
   bigstep_e_exec'_2_ind_hyp_tac
  ) >- (
   bigstep_e_exec'_2_ind_hyp_tac
  ) >>
  bigstep_e_exec'_ind_hyp_tac,

  (* slice *)
  fs[bigstep_e_exec'_slice_REWR] >>
  rpt strip_tac >> (
   bigstep_e_exec'_ind_hyp_tac
  ),

  (* call *)
  fs[bigstep_e_exec'_def],

  (* select *)
  fs[bigstep_e_exec'_select_REWR] >>
  rpt strip_tac >>
  bigstep_e_exec'_ind_hyp_tac,

  (* struct *)
  fs[bigstep_e_exec'_struct_REWR] >>
  rpt strip_tac >> (
   PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INR (MAP SND (l:(string # e) list)))’] thm)) >>
   fs[e_size_def, e3_e1_size] >>
   res_tac >>
   decide_tac
  ),

  (* header *)
  fs[bigstep_e_exec'_def]
 ]
(* INR *)
) >>
Induct_on ‘y’ >> (
 rpt strip_tac >>
 fs[bigstep_e_exec'_def]
) >>
Cases_on ‘bigstep_e_exec' scope_lists (INL h) n’ >> (
 fs[]
) >>
PairCases_on ‘x’ >>
fs[] >>
Cases_on ‘x0’ >>
fs[] >>
Cases_on ‘bigstep_e_exec' scope_lists (INR y) x1’ >> (
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

val bigstep_e_exec'_unchanged_ind_hyp_tac =
 imp_res_tac bigstep_e_exec'_incr >>
 PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
 fs[e_size_def] >>
 res_tac >>
 fs[]
;

val bigstep_e_exec'_unchanged_2_ind_hyp_tac =
 imp_res_tac bigstep_e_exec'_incr >>
 PAT_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
 PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x')’] thm)) >>
 fs[e_size_def] >>
 res_tac >>
 fs[]
;

Theorem bigstep_e_exec'_unchanged:
!t t' scope_lists n.
bigstep_e_exec' scope_lists t n = SOME (t', n) ==>
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
  fs[bigstep_e_exec'_def],

  (* var *)
  fs[bigstep_e_exec'_var_REWR],

  (* list *)
  fs[bigstep_e_exec'_def],

  (* acc *)
  fs[bigstep_e_exec'_acc_REWR] >> (
   bigstep_e_exec'_unchanged_ind_hyp_tac
  ),

  (* unop *)
  fs[bigstep_e_exec'_unop_REWR] >> (
   bigstep_e_exec'_unchanged_ind_hyp_tac
  ),

  (* cast *)
  fs[bigstep_e_exec'_cast_REWR] >> (
   bigstep_e_exec'_unchanged_ind_hyp_tac
  ),

  (* binop *)
  fs[bigstep_e_exec'_binop_REWR] >- (
   bigstep_e_exec'_unchanged_ind_hyp_tac
  ) >- (
   bigstep_e_exec'_unchanged_2_ind_hyp_tac
  ) >- (
   imp_res_tac bigstep_e_exec'_incr >>
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
  bigstep_e_exec'_unchanged_ind_hyp_tac,


  (* concat *)
  fs[bigstep_e_exec'_concat_REWR] >- (
   bigstep_e_exec'_unchanged_2_ind_hyp_tac
  ) >- (
   imp_res_tac bigstep_e_exec'_incr >>
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
  bigstep_e_exec'_unchanged_ind_hyp_tac,

  (* slice *)
  fs[bigstep_e_exec'_slice_REWR] >> (
   bigstep_e_exec'_unchanged_ind_hyp_tac
  ),

  (* call *)
  fs[bigstep_e_exec'_def],

  (* select *)
  fs[bigstep_e_exec'_select_REWR] >>
  rpt strip_tac >>
  bigstep_e_exec'_unchanged_ind_hyp_tac,

  (* struct *)
  fs[bigstep_e_exec'_struct_REWR] >> (
   imp_res_tac bigstep_e_exec'_incr >>
   PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INR (MAP SND (l:(string # e) list)))’] thm)) >>
   fs[e_size_def, e3_e1_size] >>
   res_tac >>
   gvs[GSYM ZIP_MAP_FST_SND]
  ),

  (* header *)
  fs[bigstep_e_exec'_def]
 ]
(* INR *)
) >>
Induct_on ‘y’ >> (
 rpt strip_tac >>
 fs[bigstep_e_exec'_def]
) >>
Cases_on ‘bigstep_e_exec' scope_lists (INL h) n’ >> (
 fs[]
) >>
PairCases_on ‘x’ >>
fs[] >>
Cases_on ‘x0’ >>
fs[] >>
Cases_on ‘bigstep_e_exec' scope_lists (INR y) x1’ >> (
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
imp_res_tac bigstep_e_exec'_incr >>
PAT_ASSUM “!y'. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL h)’] thm)) >>
fs[e_size_def] >>
PAT_ASSUM “!y'.
          (case y' of INL e => e_size e | INR e_l => e3_size e_l) <
          e3_size y + (e_size h + 1) ==>
          !t' scope_lists n.
            bigstep_e_exec' scope_lists y' n = SOME (t',n) ==> y' = t'” (fn thm => ASSUME_TAC (Q.SPECL [‘(INR y)’] thm)) >>

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

fun bigstep_e_exec'_not_eq_ind_hyp_tac tmq =
 PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
 fs[e_size_def] >>
 subgoal tmq >- (
  fs[]
 ) >>
 res_tac
;

Theorem bigstep_e_exec'_not_eq:
!t t' scope_lists n.
t <> t' ==>
bigstep_e_exec' scope_lists t 0 = SOME (t',n) ==>
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
  fs[bigstep_e_exec'_def],

  (* var *)
  fs[bigstep_e_exec'_var_REWR],

  (* list *)
  fs[bigstep_e_exec'_def],

  (* acc *)
  fs[bigstep_e_exec'_acc_REWR] >>
  bigstep_e_exec'_not_eq_ind_hyp_tac ‘INL x <> ((INL e_v_struct):(e + e list))’,

  (* unop *)
  fs[bigstep_e_exec'_unop_REWR] >>
  bigstep_e_exec'_not_eq_ind_hyp_tac ‘INL x <> ((INL e'):(e + e list))’,

  (* cast *)
  fs[bigstep_e_exec'_cast_REWR] >>
  bigstep_e_exec'_not_eq_ind_hyp_tac ‘INL x <> ((INL e'):(e + e list))’,

  (* binop *)
  fs[bigstep_e_exec'_binop_REWR] >- (
   imp_res_tac bigstep_e_exec'_incr >>
   subgoal ‘n' = 0’ >- (
    fs[]
   ) >>
   fs[] >>
   imp_res_tac bigstep_e_exec'_unchanged >>
   fs[]
  ) >>
  bigstep_e_exec'_not_eq_ind_hyp_tac ‘INL x <> ((INL e1'):(e + e list))’,

  (* concat *)
  fs[bigstep_e_exec'_concat_REWR] >- (
   imp_res_tac bigstep_e_exec'_incr >>
   subgoal ‘n' = 0’ >- (
    fs[]
   ) >>
   fs[] >>
   imp_res_tac bigstep_e_exec'_unchanged >>
   fs[]
  ) >>
  bigstep_e_exec'_not_eq_ind_hyp_tac ‘INL x <> ((INL e1'):(e + e list))’,

  (* slice *)
  fs[bigstep_e_exec'_slice_REWR] >>
  bigstep_e_exec'_not_eq_ind_hyp_tac ‘INL x <> ((INL e1'):(e + e list))’,

  (* call *)
  fs[bigstep_e_exec'_def],

  (* select *)
  fs[bigstep_e_exec'_select_REWR] >>
  bigstep_e_exec'_not_eq_ind_hyp_tac ‘INL x <> ((INL e'):(e + e list))’,

  (* struct *)
  fs[bigstep_e_exec'_struct_REWR] >>
  PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INR (MAP SND (l:(string # e) list)))’] thm)) >>
  fs[e_size_def, e3_e1_size] >>
  imp_res_tac bigstep_e_exec'_unchanged >>
  gvs[ZIP_MAP_FST_SND],

  (* header *)
  fs[bigstep_e_exec'_def]
 ]
) >>
(* INR *)
Induct_on ‘y’ >> (
 rpt strip_tac >>
 fs[bigstep_e_exec'_def]
) >>
Cases_on ‘bigstep_e_exec' scope_lists (INL h) 0’ >> (
 fs[]
) >>
PairCases_on ‘x’ >>
fs[] >>
Cases_on ‘x0’ >>
fs[] >>
Cases_on ‘bigstep_e_exec' scope_lists (INR y) x1’ >> (
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
imp_res_tac bigstep_e_exec'_incr >>
PAT_ASSUM “!y'. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL h)’] thm)) >>
fs[e_size_def] >>
PAT_ASSUM “!y'.
          (case y' of INL e => e_size e | INR e_l => e3_size e_l) <
          e3_size y + (e_size h + 1) ==>
          !t'' scope_lists'.
            y' <> t'' ==> bigstep_e_exec' scope_lists' y' 0 <> SOME (t'',0)” (fn thm => ASSUME_TAC (Q.SPECL [‘(INR y)’] thm)) >>
fs[e_size_def] >>
Cases_on ‘is_v x’ >> (
 fs[]
) >- (
 gvs[] >>
 imp_res_tac bigstep_e_exec'_unchanged >>
 fs[]
) >>
gs[] >>
imp_res_tac bigstep_e_exec'_unchanged >>
fs[]
QED

Theorem bigstep_e_exec'_not_v_bit:
!e e' scope_lists n.
~is_v_bit e ==>
is_v_bit e' ==>
bigstep_e_exec' scope_lists (INL e) 0 = SOME (INL e',n) ==>
n <> 0
Proof
rpt strip_tac >>
rw[] >>
imp_res_tac bigstep_e_exec'_unchanged >>
Cases_on ‘e’ >> Cases_on ‘e'’ >> (
 fs[is_v_bit]
)
QED

Theorem bigstep_e_exec'_not_v:
!e e' scope_lists n.
~is_v e ==>
is_v e' ==>
bigstep_e_exec' scope_lists (INL e) 0 = SOME (INL e',n) ==>
n <> 0
Proof
rpt strip_tac >>
rw[] >>
imp_res_tac bigstep_e_exec'_unchanged >>
Cases_on ‘e’ >> Cases_on ‘e'’ >> (
 fs[is_v]
)
QED

Theorem bigstep_e_exec'_v:
!v scope_list g_scope_list' n.
bigstep_e_exec' (scope_list ++ g_scope_list') (INL (e_v v)) n = SOME (INL $ e_v v, n)
Proof
fs[bigstep_e_exec'_def]
QED

(* OLD
Theorem bigstep_e_exec'_all_red:
!e_l scope_lists n.
unred_mem_index e_l = NONE ==>
bigstep_e_exec' scope_lists (INR e_l) n = SOME (INR e_l,n+1)
Proof
cheat
QED

Theorem bigstep_e_exec'_single_unred:
!e_l e_l' e' x scope_lists n.
unred_mem_index e_l = SOME x ==>
bigstep_e_exec' scope_lists (INR e_l) n = SOME (INR e_l',n+1) ==>
bigstep_e_exec' scope_lists (INL (EL x e_l)) n = SOME (INL e', n+1) /\ e_l' = LUPDATE e' x e_l
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
bigstep_e_exec' (scope_list ++ g_scope_list') t 0 = SOME (t', 1) ==>
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
  gvs[bigstep_e_exec'_def],

  (* var *)
  rw[] >>
  fs[bigstep_e_exec'_var_REWR] >>
  fs[e_exec, lookup_vexp_def, lookup_vexp2_def] >>
  Cases_on ‘lookup_map (scope_list ++ g_scope_list') v’ >> (
   fs[]
  ) >>
  PairCases_on ‘x’ >>
  fs[],

  (* list *)
  gvs[bigstep_e_exec'_def],

  (* acc *)
  rw[] >>
  fs[bigstep_e_exec'_acc_REWR] >> (
   rw[] >>
   fs[e_exec]
  ) >- (
   Cases_on ‘is_v x’ >> (
    fs[]
   ) >- (
    Cases_on ‘x’ >> (
     fs[is_v, bigstep_e_exec'_def]
    )
   ) >>
   imp_res_tac bigstep_e_exec'_unchanged >>
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
   fs[is_v, bigstep_e_exec'_def]
  ),

  (* unop *)
  rw[] >>
  fs[bigstep_e_exec'_unop_REWR] >> (
   rw[] >>
   fs[e_exec]
  ) >- (
   Cases_on ‘is_v x’ >> (
    fs[]
   ) >- (
    Cases_on ‘x’ >> (
     fs[is_v, bigstep_e_exec'_def]
    )
   ) >>
   imp_res_tac bigstep_e_exec'_unchanged >>
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
   fs[is_v, bigstep_e_exec'_def]
  ),

  (* cast *)
  rw[] >>
  fs[bigstep_e_exec'_cast_REWR] >> (
   rw[] >>
   fs[e_exec]
  ) >- (
   Cases_on ‘is_v x’ >> (
    fs[]
   ) >- (
    Cases_on ‘x’ >> (
     fs[is_v, bigstep_e_exec'_def]
    )
   ) >>
   imp_res_tac bigstep_e_exec'_unchanged >>
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
   fs[is_v, bigstep_e_exec'_def]
  ),

  (* binop *)
  rw[] >>
  fs[bigstep_e_exec'_binop_REWR] >> (
   rw[] >>
   fs[e_exec]
  ) >- (
   fs[] >>
   imp_res_tac bigstep_e_exec'_unchanged >>
   fs[]
  ) >- (
   fs[] >>
   imp_res_tac bigstep_e_exec'_incr >>
   fs[] >>
   imp_res_tac bigstep_e_exec'_unchanged >>
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
      fs[bigstep_e_exec'_def]
     ) >>
     fs[bigstep_e_exec'_def] >>
     gvs[] >>
     PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x')’] thm)) >>
     fs[e_size_def] >>
     res_tac >>
     fs[]
    )
   ) >>
   imp_res_tac bigstep_e_exec'_incr >>
   subgoal ‘n' = 1’ >- (
    CCONTR_TAC >>
    subgoal ‘n' = 0’ >- (
     decide_tac
    ) >>
    fs[] >>
    imp_res_tac bigstep_e_exec'_unchanged >>
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
    imp_res_tac bigstep_e_exec'_unchanged >>
    fs[]
   )
  ) >- (
   fs[] >>
   PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
   fs[e_size_def] >>
   res_tac >>
   fs[] >>
   Cases_on ‘x’ >> (
    fs[bigstep_e_exec'_def]
   )
  ),

  (* concat *)
  rw[] >>
  fs[bigstep_e_exec'_concat_REWR] >> (
   rw[] >>
   fs[e_exec]
  ) >- (
   fs[] >>
   imp_res_tac bigstep_e_exec'_incr >>
   fs[] >>
   imp_res_tac bigstep_e_exec'_unchanged >>
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
     fs[bigstep_e_exec'_def]
    ) >>
    subgoal ‘n' = 0’ >- (
     fs[bigstep_e_exec'_def]
    ) >>
    fs[] >>
    PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x')’] thm)) >>
    fs[e_size_def] >>
    res_tac >>
    fs[] >>
    imp_res_tac bigstep_e_exec'_unchanged >>
    fs[]
   ) >>
   imp_res_tac bigstep_e_exec'_incr >>
   subgoal ‘n' = 1’ >- (
    CCONTR_TAC >>
    subgoal ‘n' = 0’ >- (
     decide_tac
    ) >>
    fs[] >>
    imp_res_tac bigstep_e_exec'_unchanged >>
    fs[]
   ) >>
   fs[] >>
   PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
   fs[e_size_def] >>
   res_tac >>
   fs[] >>
   imp_res_tac bigstep_e_exec'_unchanged >>
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
   fs[bigstep_e_exec'_def]
  ),

  (* slice *)
  rw[] >>
  fs[bigstep_e_exec'_slice_REWR] >> (
   rw[] >>
   fs[e_exec]
  ) >- (
   Cases_on ‘is_v_bit x’ >> (
    fs[]
   ) >- (
    Cases_on ‘x’ >> (
     fs[is_v_bit, bigstep_e_exec'_def]
    )
   ) >>
   imp_res_tac bigstep_e_exec'_unchanged >>
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
   fs[is_v_bit, bigstep_e_exec'_def]
  ),

  (* call *) 
  gvs[bigstep_e_exec'_def],

  (* select *)
  rw[] >>
  fs[bigstep_e_exec'_select_REWR] >> (
   rw[] >>
   fs[e_exec]
  ) >>
  Cases_on ‘is_v x’ >> (
   fs[]
  ) >- (
   Cases_on ‘x’ >> (
    fs[is_v, bigstep_e_exec'_def]
   )
  ) >>
  PAT_X_ASSUM “!y. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL x)’] thm)) >>
  fs[e_size_def] >>
  res_tac >>
  fs[],

  (* struct *)
  rw[] >>
  fs[bigstep_e_exec'_struct_REWR] >> (
   rw[] >>
   fs[e_exec]
  ) >- (
   fs[] >>
   imp_res_tac bigstep_e_exec'_unchanged >>
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
   fs[bigstep_e_exec'_def, e_exec]
  ) >>
  fs[e_exec] >>
  Cases_on ‘unred_mem_index (SND h::MAP SND t)’ >> (
   fs[]
  ) >>
  PAT_X_ASSUM “!tbl_map pars_map func_map ext_map b_func_map apply_table_f. _” (fn thm => ASSUME_TAC (Q.SPECL [‘tbl_map’, ‘pars_map’, ‘func_map’, ‘ext_map’, ‘b_func_map’, ‘apply_table_f’] thm)) >>
  fs[],

  (* header *)
  gvs[bigstep_e_exec'_def]
 ]
) >>
(* INR *)
Induct_on ‘y’ >> (
 rpt strip_tac >>
 fs[bigstep_e_exec'_def]
) >>
Cases_on ‘bigstep_e_exec' (scope_list ++ g_scope_list') (INL h) 0’ >> (
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
 Cases_on ‘bigstep_e_exec' (scope_list ++ g_scope_list') (INR y) x1’ >> (
  fs[]
 ) >>
 PairCases_on ‘x'’ >>
 fs[] >>
 Cases_on ‘x'0’ >>
 fs[] >>
 subgoal ‘x1 = 0 \/ x1 = 1’ >- (
  imp_res_tac bigstep_e_exec'_incr >>
  decide_tac
 ) >- (
  (* x1 = 0: y reduction contributes the step *)
  gs[] >>
  imp_res_tac bigstep_e_exec'_unchanged >>
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
   fs[bigstep_e_exec'_def]
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
   fs[is_const_def, bigstep_e_exec'_def]
  )
 ) >>
 PAT_ASSUM “!y'. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL h)’] thm)) >>
 fs[e_size_def] >>
 res_tac >>
 fs[] >>
 qexists_tac ‘0’ >>
 fs[unred_mem_index_def, unred_mem_def, listTheory.INDEX_FIND_def, listTheory.LUPDATE_def] >>
 imp_res_tac bigstep_e_exec'_unchanged >>
 fs[]
) >>
(* New case *)
gvs[] >>
qexists_tac ‘0’ >>
subgoal ‘~is_const h’ >- (
 CCONTR_TAC >>
 Cases_on ‘h’ >> (
  fs[is_const_def, bigstep_e_exec'_def]
 )
) >>
fs[unred_mem_index_def, unred_mem_def, listTheory.INDEX_FIND_def, listTheory.LUPDATE_def] >>
PAT_ASSUM “!y'. _” (fn thm => ASSUME_TAC (Q.SPECL [‘(INL h)’] thm)) >>
fs[e_size_def] >>
res_tac >>
fs[]
QED

Theorem scope_lists_separate:
!scope_lists top_scope scope_list scope_list' g_scope_list' g_scope_list''.
scope_lists = top_scope::(scope_list ++ g_scope_list') ==>
           separate scope_lists = (SOME g_scope_list'',SOME scope_list') ==>
           g_scope_list' = g_scope_list'' /\ top_scope::scope_list = scope_list'
Proof
rpt gen_tac >> rpt disch_tac >>
subgoal ‘LENGTH g_scope_list' = 2’ >- (
 (* TODO: Assert that LENGTH g_scope_list' = 2 in the "separate" function? *)
 (* TODO: Double-check assumptions where scope_lists_separate is used *)
 cheat
) >>
rpt strip_tac >> (
 rw[]
) >>
fs[separate_def] >>
gs[arithmeticTheory.ADD_SUC] >>
FULL_SIMP_TAC pure_ss [GSYM SUC_ADD_ONE] >>
fs[oDROP_def, oTAKE_def, oDROP_APPEND, oTAKE_APPEND]
QED

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
  fs[bigstep_e_exec'_def, is_v] >>
  Cases_on ‘stmt_exec_ass l (e_v v) scope_lists’ >> (
   fs[]
  )
 ) >>
 Cases_on ‘?funn' e_l. e = e_call funn e_l’ >> (
  gs[bigstep_f_arg_exec_def]
 ) >>
 Cases_on ‘bigstep_e_exec' scope_lists (INL e) n’ >> (
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
    imp_res_tac bigstep_e_exec'_incr >>
    decide_tac
   )
  ) >> (
   Cases_on ‘e’ >> (
    fs[]
   )
  ) >> (
   gvs[is_v] >>
   imp_res_tac bigstep_e_exec'_incr >>
   fs[] >>
   Cases_on ‘n = m’ >> (
    gvs[]
   ) >>
   imp_res_tac bigstep_e_exec'_unchanged >>
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
  fs[bigstep_e_exec'_def, is_v]
 ) >>
 Cases_on ‘?funn' e_l. e = e_call funn e_l’ >> (
  gs[bigstep_f_arg_exec_def]
 ) >>
 Cases_on ‘bigstep_e_exec' scope_lists (INL e) n’ >> (
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
   imp_res_tac bigstep_e_exec'_incr
  ) >> (
   fs[] >>
   Cases_on ‘n = m’ >> (
    gvs[]
   ) >>
   imp_res_tac bigstep_e_exec'_unchanged >>
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
  fs[bigstep_stmt_exec_def, bigstep_e_exec'_def]
 ) >>
 (* e reduction *)
 Cases_on ‘bigstep_e_exec' scope_lists (INL e) n’ >> (
  fs[]
 ) >>
 PairCases_on ‘x’ >>
 gs[] >>
 Cases_on ‘x0’ >> (
  fs[]
 ) >>
 gvs[] >>
 imp_res_tac bigstep_e_exec'_incr >>
 fs[] >>
 Cases_on ‘n = m’ >> (
  gvs[]
 ) >>
 imp_res_tac bigstep_e_exec'_unchanged >>
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
 Cases_on ‘bigstep_e_exec' scope_lists (INL e) n’ >> (
  fs[]
 ) >>
 PairCases_on ‘x’ >>
 gs[] >>
 Cases_on ‘x0’ >> (
  fs[]
 ) >>
 gvs[] >>
 imp_res_tac bigstep_e_exec'_incr >>
 fs[] >>
 Cases_on ‘n = m’ >> (
  gvs[]
 ) >>
 imp_res_tac bigstep_e_exec'_unchanged >>
 fs[],

 (* apply *)
 fs[bigstep_stmt_exec_def] >>
 Cases_on ‘bigstep_e_exec' scope_lists (INR l) n’ >> (
  fs[]
 ) >>
 PairCases_on ‘x’ >>
 gs[] >>
 Cases_on ‘x0’ >> (
  fs[]
 ) >>
 imp_res_tac bigstep_e_exec'_incr >>
 fs[] >>
 Cases_on ‘n = m’ >> (
  gvs[]
 ) >>
 imp_res_tac bigstep_e_exec'_unchanged >>
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
Theorem bigstep_stmt_exec_sound:
!h scope_list g_scope_list' g_scope_list''
stmt' scope_lists scope_list' funn t top_scope apply_table_f ext_map func_map x' pars_map x'' ascope.
bigstep_stmt_exec (NONE:(func_map # b_func_map # 'a ext_map) option) ((top_scope::scope_list)++g_scope_list') h 0 = SOME (stmt', scope_lists, 1) ==>
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
   fs[bigstep_stmt_exec_def, bigstep_e_exec'_def, is_v] >>
   Cases_on ‘stmt_exec_ass l (e_v v) (top_scope::(scope_list ++ g_scope_list'))’ >> (
    fs[]
   )
  ) >>
  (* e reduction *)
  fs[bigstep_stmt_exec_def] >>
  Cases_on ‘?funn' e_l. e = e_call funn e_l’ >> (
   gs[bigstep_f_arg_exec_def]
  ) >>
  Cases_on ‘bigstep_e_exec' (top_scope::(scope_list ++ g_scope_list')) (INL e) 0’ >> (
   fs[]
  ) >- (
   Cases_on ‘e’ >> (
    fs[]
   )
  ) >>
  PairCases_on ‘x’ >>
  fs[] >>
  (* TODO: Skip subgoal, make case splitting directly instead? *)
  subgoal ‘x1 = 1’ >- (
   cheat
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
   fs[bigstep_stmt_exec_def, bigstep_e_exec'_def]
  ) >>
  (* e reduction *)
  fs[bigstep_stmt_exec_def] >>
  Cases_on ‘?funn' e_l. e = e_call funn e_l’ >> (
   gs[bigstep_f_arg_exec_def]
  ) >>
  Cases_on ‘bigstep_e_exec' (top_scope::(scope_list ++ g_scope_list')) (INL e) 0’ >> (
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
   fs[bigstep_stmt_exec_def, bigstep_e_exec'_def]
  ) >>
  (* e reduction *)
  fs[bigstep_stmt_exec_def] >>
  Cases_on ‘bigstep_e_exec' (top_scope::(scope_list ++ g_scope_list')) (INL e) 0’ >> (
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
     fs[bigstep_stmt_exec_def, bigstep_e_exec'_def]
    )
   )
  ) >>
  (* nested e reduction *)
  fs[bigstep_stmt_exec_def] >>
  Cases_on ‘bigstep_e_exec' (top_scope::(scope_list ++ g_scope_list')) (INL e) 0’ >> (
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
   Cases_on ‘bigstep_e_exec' (top_scope::(scope_list ++ g_scope_list')) (INR l) 0’ >> (
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
    fs[bigstep_e_exec'_def]
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
  Cases_on ‘bigstep_e_exec' (top_scope::(scope_list ++ g_scope_list')) (INR l) 0’ >> (
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
   fs[bigstep_e_exec'_def]
  ) >>
  PAT_X_ASSUM “!tbl_map pars_map func_map ext_map b_func_map apply_table_f. _” (fn thm => ASSUME_TAC (Q.SPECL [‘x''’, ‘pars_map’, ‘func_map’, ‘ext_map’, ‘x'’, ‘apply_table_f’] thm)) >>
  fs[] >>
  subgoal ‘!h. index_not_const (h::t) = unred_mem_index (h::t)’ >- (
   fs[index_not_const_def, unred_mem_index_def, unred_mem_def]
  ) >>
  gvs[] >>
  FULL_SIMP_TAC pure_ss [GSYM listTheory.APPEND] >>
  irule scope_lists_separate >>
  qexists_tac ‘((top_scope::scope_list) ++ g_scope_list')’ >>
  fs[]
 ),

 (* ext *)
 fs[bigstep_stmt_exec_def]
]
QED

Theorem bigstep_arch_exec_sound_NONE_1:
!i ab_list x el pblock_map pbl_type x_d_list b_func_map decl_list pars_map tbl_map funn stmt_stack scope_list top_scope frame_list func_map in_out_list in_out_list' ascope g_scope_list g_scope_list' g_scope_list'' arch_frame_list' g_scope_list''' ffblock_map input_f output_f copyin_pbl copyout_pbl apply_table_f ext_map.
(EL i ab_list = (arch_block_pbl x el)) ==>
(ALOOKUP pblock_map x = SOME (pbl_type, x_d_list, b_func_map, decl_list, pars_map, tbl_map)) ==>
~(state_fin_exec status_running ((funn, stmt_stack, (top_scope::scope_list))::frame_list)) ==>
scopes_to_pass funn func_map b_func_map g_scope_list = SOME g_scope_list' ==>
map_to_pass funn b_func_map <> NONE ==>
tbl_to_pass funn b_func_map tbl_map <> NONE ==>
bigstep_arch_exec (NONE:('a actx # b_func_map) option) (g_scope_list':g_scope_list) (arch_frame_list_regular ((funn, stmt_stack, (top_scope::scope_list))::frame_list)) = SOME (g_scope_list'', arch_frame_list', 1) ==>
scopes_to_retrieve funn func_map b_func_map g_scope_list g_scope_list'' = SOME g_scope_list''' ==>
arch_exec ((ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map):'a actx) ((i, in_out_list, in_out_list', ascope), g_scope_list, (arch_frame_list_regular ((funn, stmt_stack, (top_scope::scope_list))::frame_list)), status_running) = SOME ((i, in_out_list, in_out_list', ascope), g_scope_list''', arch_frame_list', status_running)
Proof
fs [arch_exec_def] >>
rpt strip_tac >>
fs [state_fin_exec_equiv, state_fin_def] >>
Cases_on ‘map_to_pass funn b_func_map’ >> (
 fs[]
) >>
Cases_on ‘tbl_to_pass funn b_func_map tbl_map’ >> (
 fs[]
) >>
fs[bigstep_arch_exec_def] >>
Cases_on ‘stmt_stack’ >> (
 fs[]
) >>
fs[bigstep_exec_def] >>
Cases_on ‘bigstep_stmt_exec NONE ((top_scope::scope_list) ++ g_scope_list') h 0’ >> (
 fs[]
) >>
PairCases_on ‘x'3'’ >>
fs[] >>
Cases_on ‘separate x'''1’ >> (
 fs[]
) >>
Cases_on ‘q’ >> (
 fs[]
) >>
Cases_on ‘r’ >> (
 fs[]
) >>
rw[] >>
Cases_on `frames_exec
           (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)
           (ascope,g_scope_list,(funn,stmt_stack,(top_scope::scope_list))::frame_list,
            status_running)` >> (
 fs []
) >- (
 fs[bigstep_arch_exec_def] >>
 Cases_on ‘frame_list’ >> (
  fs[bigstep_exec_def, frames_exec]
 ) >| [
  ALL_TAC,

  PairCases_on ‘h'’ >>
  fs[bigstep_exec_def, frames_exec]
 ] >> (
  FULL_SIMP_TAC pure_ss [GSYM listTheory.APPEND] >>
  imp_res_tac bigstep_stmt_exec_sound >>
  gs[]
 )
) >>
PairCases_on ‘x'3'’ >>
fs[bigstep_arch_exec_def] >>
Cases_on ‘frame_list’ >> (
 fs[bigstep_exec_def, frames_exec]
) >| [
 ALL_TAC,

 PairCases_on ‘h'’ >>
 fs[bigstep_exec_def, frames_exec]
] >> (
 FULL_SIMP_TAC pure_ss [GSYM listTheory.APPEND] >>
 imp_res_tac bigstep_stmt_exec_sound >>
 gs[] >> (
  FULL_SIMP_TAC pure_ss [GSYM listTheory.APPEND] >>
  imp_res_tac bigstep_stmt_exec_sound >>
  gs[]
 )
)
QED

Theorem bigstep_arch_exec_sound_NONE:
!i ab_list x el pblock_map pbl_type x_d_list b_func_map decl_list pars_map tbl_map funn stmt_stack scope_list frame_list func_map in_out_list in_out_list' ascope g_scope_list g_scope_list' g_scope_list'' arch_frame_list' n g_scope_list''' ffblock_map input_f output_f copyin_pbl copyout_pbl apply_table_f ext_map.
(EL i ab_list = (arch_block_pbl x el)) ==>
(ALOOKUP pblock_map x = SOME (pbl_type, x_d_list, b_func_map, decl_list, pars_map, tbl_map)) ==>
~(state_fin_exec status_running ((funn, stmt_stack, scope_list)::frame_list)) ==>
scopes_to_pass funn func_map b_func_map g_scope_list = SOME g_scope_list' ==>
map_to_pass funn b_func_map <> NONE ==>
tbl_to_pass funn b_func_map tbl_map <> NONE ==>
bigstep_arch_exec NONE (g_scope_list':g_scope_list) (arch_frame_list_regular ((funn, stmt_stack, scope_list)::frame_list)) = SOME (g_scope_list'', arch_frame_list', n) ==>
scopes_to_retrieve funn func_map b_func_map g_scope_list g_scope_list'' = SOME g_scope_list''' ==>
arch_multi_exec ((ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map):'a actx) ((i, in_out_list, in_out_list', ascope), g_scope_list, (arch_frame_list_regular ((funn, stmt_stack, scope_list)::frame_list)), status_running) n = SOME ((i, in_out_list, in_out_list', ascope), g_scope_list''', arch_frame_list', status_running)
Proof
cheat
QED

(*
Theorem bigstep_arch_exec_sound_SOME:
!i ab_list x el pblock_map pbl_type x_d_list b_func_map decl_list pars_map tbl_map funn stmt_stack scope_list frame_list func_map g_scope_list g_scope_list' g_scope_list'' arch_frame_list' n g_scope_list''' ffblock_map input_f output_f copyin_pbl copyout_pbl apply_table_f ext_map aenv.
(EL i ab_list = (arch_block_pbl x el)) ==>
(ALOOKUP pblock_map x = SOME (pbl_type, x_d_list, b_func_map, decl_list, pars_map, tbl_map)) ==>
~(state_fin_exec status_running ((funn, stmt_stack, scope_list)::frame_list)) ==>
scopes_to_pass funn func_map b_func_map g_scope_list = SOME g_scope_list' ==>
map_to_pass funn b_func_map <> NONE ==>
tbl_to_pass funn b_func_map tbl_map <> NONE ==>
bigstep_arch_exec (SOME ((ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map), b_func_map)) (g_scope_list':g_scope_list) (arch_frame_list_regular ((funn, stmt_stack, scope_list)::frame_list)) = SOME (g_scope_list'', arch_frame_list', n) ==>
scopes_to_retrieve funn func_map b_func_map g_scope_list g_scope_list'' = SOME g_scope_list''' ==>
arch_multi_exec ((ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map):'a actx) (aenv, g_scope_list, (arch_frame_list_regular ((funn, stmt_stack, scope_list)::frame_list)), status_running) n = SOME (aenv, g_scope_list''', arch_frame_list', status_running)
Proof
cheat
QED
*)

Definition in_local_fun_def:
 (in_local_fun func_map (arch_frame_list_regular ((funn_name fname, stmt_stack, scope_list)::frame_list)) =
  (ALOOKUP func_map fname = NONE)) /\
 (in_local_fun func_map _ = F)
End

Definition in_local_fun'_def:
 (in_local_fun' ((ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map):'a actx) (arch_frame_list_regular ((funn_name fname, stmt_stack, scope_list)::frame_list)) =
  (ALOOKUP func_map fname = NONE)) /\
 (in_local_fun' ctx _ = F)
End

(* If funn can't be found in the global function map, we don't need to fiddle
 * with the g_scope_list *)
Theorem bigstep_arch_exec_comp_NONE:
!assl ab_list pblock_map func_map g_scope_list arch_frame_list status aenv' g_scope_list' g_scope_list'' n' arch_frame_list' arch_frame_list'' n ffblock_map input_f output_f copyin_pbl copyout_pbl apply_table_f ext_map aenv.
(assl ==> arch_multi_exec ((ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map):'a actx) (aenv, g_scope_list, arch_frame_list, status) n = SOME (aenv', g_scope_list', arch_frame_list', status_running)) ==>
in_local_fun func_map arch_frame_list' ==>
bigstep_arch_exec NONE (g_scope_list':g_scope_list) arch_frame_list' = SOME (g_scope_list'', arch_frame_list'', n') ==>
(assl ==> arch_multi_exec ((ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map):'a actx) (aenv, g_scope_list, arch_frame_list, status_running) (n+n') = SOME (aenv', g_scope_list'', arch_frame_list'', status_running))
Proof
cheat
QED

Theorem bigstep_arch_exec_local:
!g_scope_list arch_frame_list g_scope_list' arch_frame_list' n (ctx:'a actx) aenv'
g_scope_list'' arch_frame_list''.
bigstep_arch_exec (NONE:('a actx # b_func_map) option) g_scope_list arch_frame_list =
        SOME (g_scope_list',arch_frame_list',n) ==>
in_local_fun' ctx arch_frame_list ==>
!n' aenv.
n' <= n ==>
arch_multi_exec ctx (aenv,g_scope_list,arch_frame_list,status_running) n' =
 SOME (aenv',g_scope_list'',arch_frame_list'',status_running) ==>
in_local_fun' ctx arch_frame_list''
Proof
cheat
QED

Theorem bigstep_arch_exec_zero:
!g_scope_list arch_frame_list g_scope_list' arch_frame_list'.
bigstep_arch_exec NONE g_scope_list arch_frame_list =
 SOME (g_scope_list',arch_frame_list',0) ==>
g_scope_list = g_scope_list' /\ arch_frame_list = arch_frame_list'
Proof
Induct_on ‘arch_frame_list’ >> (
 fs[bigstep_arch_exec_def]
) >>
Cases_on ‘l’ >> (
 fs[bigstep_arch_exec_def]
) >>
PairCases_on ‘h’ >>
fs[] >>
Cases_on ‘h1’ >> (
 fs[]
) >>
 fs[bigstep_exec_def] >>
rpt strip_tac >> (
 Cases_on ‘bigstep_stmt_exec NONE (h2 ++ g_scope_list) h 0’ >> (
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
 (* Use bigstep_stmt_exec_zero *)
 cheat
)
QED

Theorem bigstep_arch_exec_stop:
!n g_scope_list arch_frame_list g_scope_list' arch_frame_list'.
bigstep_arch_exec (NONE:('a actx # b_func_map) option) g_scope_list arch_frame_list =
 SOME (g_scope_list',arch_frame_list',n) ==>
bigstep_arch_exec (NONE:('a actx # b_func_map) option) g_scope_list' arch_frame_list' =
 SOME (g_scope_list',arch_frame_list',0)
Proof
Induct_on ‘n’ >- (
 rpt strip_tac >>
 metis_tac[bigstep_arch_exec_zero]
) >>
rpt strip_tac >>
fs[SUC_ADD_ONE] >>
Cases_on ‘arch_frame_list’ >> (
 fs[bigstep_arch_exec_def]
) >>
Cases_on ‘l’ >> (
 fs[]
) >>
PairCases_on ‘h’ >> (
 fs[]
) >>
Cases_on ‘h1’ >> (
 fs[]
) >>
Cases_on ‘bigstep_exec NONE (g_scope_list,h2) h’ >> (
 fs[]
) >>
PairCases_on ‘x’ >> (
 fs[]
) >>
gvs[bigstep_arch_exec_def] >>
Cases_on ‘bigstep_exec NONE (g_scope_list',x2) x0’ >> (
 fs[]
) >- (
 (* TODO: bigstep_stmt_exec_stop *)
 cheat
) >>
PairCases_on ‘x’ >> (
 fs[]
) >>
(* TODO: bigstep_stmt_exec_stop *)
cheat
QED

Theorem bigstep_arch_exec_SOME_trace:
!n (ctx:'a actx) aenv g_scope_list arch_frame_list g_scope_list' arch_frame_list'.
bigstep_arch_exec (NONE:('a actx # b_func_map) option) g_scope_list arch_frame_list =
 SOME (g_scope_list',arch_frame_list',n+1) ==>
?g_scope_list'' arch_frame_list''.
arch_multi_exec ctx (aenv,g_scope_list,arch_frame_list,status_running) 1 =
 SOME (aenv,g_scope_list'',arch_frame_list'',status_running) /\
bigstep_arch_exec (NONE:('a actx # b_func_map) option) g_scope_list'' arch_frame_list'' =
 SOME (g_scope_list',arch_frame_list',n)
Proof
Induct_on ‘n’ >- (
 rpt strip_tac >>
 fs[bigstep_arch_exec_def] >>
 qexistsl_tac [‘g_scope_list'’, ‘arch_frame_list'’] >>
 rpt strip_tac >| [
  (* Use soundness *)
  cheat,

  (* Use bigstep_arch_exec_stop *)
  metis_tac[bigstep_arch_exec_stop]
 ]
) >>
rpt strip_tac >>
(* TODO: ??? *)
cheat
QED

Theorem bigstep_arch_exec_comp'_NONE:
!n' n assl ctx g_scope_list arch_frame_list aenv' g_scope_list' g_scope_list'' arch_frame_list' arch_frame_list'' aenv.
(assl ==> arch_multi_exec ctx (aenv, g_scope_list, arch_frame_list, status_running) n = SOME (aenv', g_scope_list', arch_frame_list', status_running)) ==>
in_local_fun' (ctx:'a actx) arch_frame_list' ==>
bigstep_arch_exec (NONE:('a actx # b_func_map) option) (g_scope_list':g_scope_list) arch_frame_list' = SOME (g_scope_list'', arch_frame_list'', n') ==>
(assl ==> arch_multi_exec ctx (aenv, g_scope_list, arch_frame_list, status_running) (n+n') = SOME (aenv', g_scope_list'', arch_frame_list'', status_running))
Proof
Induct_on ‘n'’ >- (
 rpt strip_tac >>
 (* If zero steps were taken by bigstep_arch_exec, g_scope_list' and arch_frame_list
  * must be preserved *)
 fs[bigstep_arch_exec_def, bigstep_arch_exec_zero] >>
 irule bigstep_arch_exec_zero >>
 fs[]
) >>
rpt strip_tac >>
fs[] >>
subgoal ‘?g_scope_list''' arch_frame_list'''.
         arch_multi_exec ctx (aenv',g_scope_list',arch_frame_list',status_running) 1 =
          SOME (aenv',g_scope_list''',arch_frame_list''',status_running) /\
         bigstep_arch_exec (NONE:('a actx # b_func_map) option) g_scope_list''' arch_frame_list''' =
          SOME (g_scope_list'',arch_frame_list'',n')’ >- (
 (* There must be an additional valid state after 1 step from n-step state, since
  * the big-step execution takes n'+1 steps from this state.
  * When executing the big-step semantics from this state, you reach the same end state
  * as if executing the big-step semantics from n-step state. *)
 gs[bigstep_arch_exec_SOME_trace]
) >>
subgoal ‘arch_multi_exec ctx (aenv,g_scope_list,arch_frame_list,status_running) (SUC n) =
          SOME (aenv',g_scope_list''',arch_frame_list''',status_running)’ >- (
 fs[SUC_ADD_ONE] >>
 irule arch_multi_exec_comp_n_tl >>
 qexistsl_tac [‘aenv'’, ‘arch_frame_list'’, ‘g_scope_list'’, ‘status_running’] >>
 fs[]
) >>
fs[] >>
subgoal ‘in_local_fun' (ctx:'a actx) arch_frame_list'3'’ >- (
 (* If big-step execution starts in a local function, all executions of equal or
  * fewer steps must also remain in the same local function *)
 irule bigstep_arch_exec_local >>
 qexistsl_tac [‘aenv'’, ‘aenv'’, ‘arch_frame_list'’, ‘arch_frame_list''’, ‘g_scope_list'’,
               ‘g_scope_list''’, ‘g_scope_list'3'’, ‘SUC n'’, ‘1’] >>
 fs[]
) >>
res_tac >>
subgoal ‘n + SUC n' = n' + SUC n’ >- (
 decide_tac
) >>
ASM_REWRITE_TAC []
QED

Theorem bigstep_arch_exec_comp'_SOME:
!assl ctx g_scope_list arch_frame_list status aenv' g_scope_list' g_scope_list'' n' arch_frame_list' arch_frame_list'' n aenv.
(assl ==> arch_multi_exec ctx (aenv, g_scope_list, arch_frame_list, status) n = SOME (aenv', g_scope_list', arch_frame_list', status_running)) ==>
in_local_fun' ctx arch_frame_list' ==>
bigstep_arch_exec' (SOME (aenv', ctx)) (g_scope_list':g_scope_list) arch_frame_list' = SOME (g_scope_list'', arch_frame_list'', n') ==>
(assl ==> arch_multi_exec ctx (aenv, g_scope_list, arch_frame_list, status_running) (n+n') = SOME (aenv', g_scope_list'', arch_frame_list'', status_running))
Proof
cheat
QED

val _ = export_theory ();
