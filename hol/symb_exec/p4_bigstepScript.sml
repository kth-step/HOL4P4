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

Definition bigstep_e_exec_def:
 (********************)
 (* Variable look-up *)
 (bigstep_e_exec (scope_lists:scope_list) (e_var x) n =
  case lookup_vexp scope_lists x of
  | SOME v => SOME (e_v v, n + 1)
  | NONE => NONE)
  /\
 (******************************)
 (* Struct/header field access *)
 (bigstep_e_exec scope_lists (e_acc e_v_struct x) n =
  (case bigstep_e_exec scope_lists e_v_struct n of
   | SOME (e_v_struct', n') =>
    if is_v e_v_struct'
    then
     (case e_exec_acc (e_acc e_v_struct' x) of
      | SOME v => SOME (v, n'+1)
      | NONE => NONE)
    else SOME (e_acc e_v_struct' x, n')
   | NONE => NONE))
  /\
 (*********************************)
 (* Struct/header field reduction *)
 (bigstep_e_exec scope_lists (e_struct x_e_l) n =
  case bigstep_e_exec_l scope_lists (MAP SND x_e_l) n of
  | SOME (e_l', n') =>
   if (EVERY is_v e_l')
   then
    SOME (e_v $ v_struct (ZIP (MAP FST x_e_l, vl_of_el e_l')) , n'+1)
   else
    SOME (e_struct (ZIP (MAP FST x_e_l, e_l')) , n')
  | NONE => NONE)
  /\
 (********)
 (* Cast *)
 (bigstep_e_exec scope_lists (e_cast cast e) n =
  (case bigstep_e_exec scope_lists e n of
   | SOME (e', n') =>
    if is_v e'
    then
     (case e_exec_cast cast e' of
      | SOME v => SOME (e_v v, n'+1)
      | NONE => NONE)
    else
     SOME (e_cast cast e', n')
   | NONE => NONE))
  /\
 (********************)
 (* Unary arithmetic *)
 (bigstep_e_exec scope_lists (e_unop unop e) n =
  (case bigstep_e_exec scope_lists e n of
   | SOME (e', n') =>
    if is_v e'
    then 
     (case e_exec_unop unop e' of
      | SOME v => SOME (e_v v, n'+1)
      | NONE => NONE)
    else
     SOME (e_unop unop e', n')
   | NONE => NONE))
  /\
 (*********************)
 (* Binary arithmetic *)
 (bigstep_e_exec scope_lists (e_binop e1 binop e2) n =
  (case bigstep_e_exec scope_lists e1 n of
   | SOME (e1', n') =>
    (case e1' of
     | (e_v v) =>
      if is_short_circuitable binop
      then
       (case e_exec_short_circuit v binop e2 of
        | SOME e' => SOME (e', n'+1)
        | NONE => NONE)
      else
       (case bigstep_e_exec scope_lists e2 n' of
        | SOME (e2', n'') =>
         if is_v e2'
         then
          (case e_exec_binop e1' binop e2' of
           | SOME v' => SOME (e_v v', n''+1)
           | NONE => NONE)
         else
          SOME (e_binop e1' binop e2', n'')
        | NONE => NONE)
     | _ =>
      SOME (e_binop e1' binop e2, n'))
   | NONE => NONE))
  /\
 (*****************)
 (* Concatenation *)
 (bigstep_e_exec scope_lists (e_concat e1 e2) n =
  case bigstep_e_exec scope_lists e1 n of
  | SOME (e1', n') =>
   if is_v_bit e1'
   then
    (case bigstep_e_exec scope_lists e2 n' of
     | SOME (e2', n'') =>
      (if is_v_bit e2'
       then 
        (case e_exec_concat e1' e2' of
         | SOME v => SOME (e_v v, n''+1)
         | NONE => NONE)
       else
        SOME (e_concat e1' e2', n''))
     | NONE => NONE)
   else
    SOME (e_concat e1' e2, n')
  | NONE => NONE)
  /\
 (***********)
 (* Slicing *)
 (bigstep_e_exec scope_lists (e_slice e1 e2 e3) n =
  if (is_v_bit e2 /\ is_v_bit e3)
  then
   (case bigstep_e_exec scope_lists e1 n of
    | SOME (e1', n') =>
     if is_v_bit e1'
     then 
      (case e_exec_slice e1' e2 e3 of
       | SOME v => SOME (e_v v, n'+1)
       | NONE => NONE)
     else
      SOME (e_slice e1' e2 e3, n')
    | NONE => NONE)
   else NONE)
  /\
 (**********************)
 (* NESTED EXPRESSIONS *)
 (**********************)
(*
 (************************)
 (* Function/extern call *)
 (* TODO: Needs directions... *)
 (bigstep_e_exec scope_lists (e_call funn e_l) n =
  case bigstep_e_exec_l scope_lists e_l n of
  | SOME (e_l', n') =>
   SOME (e_call funn e_l', n')
  | NONE => NONE)
 /\
*)
 (**********)
 (* Select *)
 (bigstep_e_exec scope_lists (e_select e s_l_x_l x) n =
  case bigstep_e_exec scope_lists e n of
  | SOME (e', n') =>
   SOME (e_select e' s_l_x_l x, n')
  | NONE => NONE)
 /\
 (bigstep_e_exec scope_lists e n = SOME (e,n))
 /\
 (bigstep_e_exec_l scope_lists [] n = SOME ([],n))
 /\
 (bigstep_e_exec_l scope_lists (h::t) n =
  case bigstep_e_exec scope_lists h n of
  | SOME (h', n') =>
   (case bigstep_e_exec_l scope_lists t n' of
    | SOME (t', n'') => SOME (h'::t', n'')
    | NONE => NONE)
  | NONE => NONE)
Termination
WF_REL_TAC `measure ( \ t. case t of
                           | (INL (scope_lists, e, n)) => e_size e
                           | (INR (scope_lists, e_l, n)) => e3_size e_l)` >>
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
  then bigstep_e_exec scope_lists e n
  else if is_e_lval e
  then SOME (e, n)
  else NONE
 )
End

Definition bigstep_f_arg_exec'_l_def:
 (bigstep_f_arg_exec'_l scope_lists [] n = SOME ([],n))
 /\
 (bigstep_f_arg_exec'_l scope_lists (h::t) n =
  case bigstep_f_arg_exec' scope_lists h n of
  | SOME (h', n') =>
   (case bigstep_f_arg_exec'_l scope_lists t n' of
    | SOME (t', n'') => SOME (h'::t', n'')
    | NONE => NONE)
  | NONE => NONE)
End

(* NOTE: This can return no reductions in case the next item to be reduced in
 * e_l is a function call *)
Definition bigstep_f_arg_exec_def:
 (bigstep_f_arg_exec func_maps_opt scope_lists (funn, e_l) n =
  (case func_maps_opt of
   | SOME (func_map, b_func_map, ext_fun_map) =>
    (case lookup_funn_sig funn func_map b_func_map ext_fun_map of
     | SOME x_d_l =>
      bigstep_f_arg_exec'_l scope_lists (ZIP (MAP SND x_d_l, e_l)) n
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
    (case bigstep_e_exec scope_lists e n of
     | SOME (e', n') =>
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
  (case bigstep_e_exec scope_lists e n of
   | SOME (e', n') =>
    SOME (stmt_ret e', scope_lists, n')
   | _ => NONE))
  /\
 (bigstep_stmt_exec func_maps_opt scope_lists (stmt_trans e) n =
  (case bigstep_e_exec scope_lists e n of
   | SOME (e', n') =>
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
    (case bigstep_e_exec scope_lists e n of
     | SOME (e', n') =>
      SOME (stmt_cond e' stmt1 stmt2, scope_lists, n')
     | _ => NONE)))
  /\
 (bigstep_stmt_exec func_maps_opt scope_lists (stmt_app t_name e_l) n =
  (case bigstep_e_exec_l scope_lists e_l n of
   | SOME (e_l', n') =>
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
 Cases_on ‘bigstep_e_exec scope_lists e'' 0’ >> (
  fs[]
 ) >>
 PairCases_on ‘x’ >>
 fs[]
;

val bigstep_e_exec_case'_tac =
 Cases_on ‘bigstep_e_exec scope_lists e n’ >> (
  fs[]
 ) >>
 PairCases_on ‘x’ >>
 fs[]
;

 (* TODO
val induct_traverse_e_then_tac tac =

;
*)

Theorem bigstep_e_exec_l_incr:
!e_l e_l' scope_lists n m.
bigstep_e_exec_l scope_lists e_l n = SOME (e_l', m) ==>
n <= m
Proof
Induct_on ‘e_l’ >> (
rpt disch_tac >>
 fs[bigstep_e_exec_def]
) >>
cheat
(*
(* OLD *)
Induct_on ‘h’ >> (
 fs[bigstep_e_exec_def]
) >| [
 rpt strip_tac >>
 Cases_on ‘bigstep_e_exec_l scope_lists e_l n’ >> (
  fs[]
 ) >>
 PairCases_on ‘x’ >>
 fs[] >>
 res_tac >>
 decide_tac,

 rpt strip_tac >>
 Cases_on ‘lookup_vexp scope_lists v’ >> (
  fs[]
 ) >>
 Cases_on ‘bigstep_e_exec_l scope_lists e_l (n + 1)’ >> (
  fs[]
 ) >>
 PairCases_on ‘x'’ >>
 fs[] >>
 res_tac >>
 decide_tac,

 rpt strip_tac >>
 Cases_on ‘bigstep_e_exec_l scope_lists e_l n’ >> (
  fs[]
 ) >>
 PairCases_on ‘x’ >>
 fs[] >>
 res_tac >>
 decide_tac,

 rpt strip_tac >>
 Cases_on ‘bigstep_e_exec scope_lists h n’ >> (
  fs[]
 ) >>
 PairCases_on ‘x’ >>
 fs[] >>
 Cases_on ‘is_v x0’ >> (
  fs[]
 ) >- (
  Cases_on ‘e_exec_acc (e_acc x0 s)’ >> (
   fs[]
  ) >>
  Cases_on ‘bigstep_e_exec_l scope_lists e_l (x1 + 1)’ >> (
   fs[]
  ) >>
  PairCases_on ‘x'’ >>
  fs[] >>
  subgoal ‘x1 + 1 <= m’ >- (
   cheat
  ) >>
  PAT_X_ASSUM “!e_l' scope_lists n m.
          (case bigstep_e_exec scope_lists h n of
             NONE => NONE
           | SOME (h',n') =>
             case bigstep_e_exec_l scope_lists e_l n' of
               NONE => NONE
             | SOME (t',n'') => SOME (h'::t',n'')) =
          SOME (e_l',m) ==>
          n <= m” (fn thm => ASSUME_TAC (Q.SPECL [‘x0::x'0’, ‘scope_lists’, ‘n’, ‘m’] thm)) >>
  rfs[] >>
  Cases_on ‘bigstep_e_exec_l scope_lists e_l x1’ >- (
   (* Why can't this be NONE? *)
   cheat
  ) >>
 PairCases_on ‘x'’ >>
 fs[] >>
 res_tac >>
 rw[]

  Cases_on ‘bigstep_e_exec_l scope_lists e_l (x1 + 1)’ >> (
   fs[]
  ) >>

  res_tac >>
  decide_tac
 ) >>
 res_tac >>
 decide_tac


cheat

Induct_on ‘l’ >> (
 rpt strip_tac >>
 fs[bigstep_e_exec_def]
) >>
 Cases_on ‘bigstep_e_exec scope_lists (SND h) n’ >> (
  fs[]
 ) >>
 PairCases_on ‘x’ >>
 fs[] >>
 Cases_on ‘bigstep_e_exec_l scope_lists (MAP SND l) x1’ >> (
  fs[]
 ) >>
 PairCases_on ‘x’ >>
 fs[] >>
 PAT_X_ASSUM “!e. _” (fn thm => irule thm) >>

 Cases_on ‘is_v x0’ >> Cases_on ‘EVERY is_v x0'’ >> (
  fs[]
 ) >>
 qexistsl_tac [‘e_v (v_struct (ZIP (MAP FST l,vl_of_el (x0'))))’, ‘scope_lists’] >>
*)
QED
 
Theorem bigstep_e_exec_incr:
!e e' scope_lists n m.
bigstep_e_exec scope_lists e n = SOME (e', m) ==>
n <= m
Proof
Induct_on ‘e’ >> (
 fs[bigstep_e_exec_def] >>
 rpt strip_tac
) >| [
 Cases_on ‘lookup_vexp scope_lists v’ >>
 fs[] >>
 decide_tac,

 bigstep_e_exec_case'_tac >>
 Cases_on ‘is_v x0’ >> (
  fs[]
 ) >- (
  Cases_on ‘e_exec_acc (e_acc x0 s)’ >> (
   fs[]
  ) >>
  res_tac >>
  decide_tac
 ) >>
 res_tac >>
 decide_tac,

 bigstep_e_exec_case'_tac >>
 Cases_on ‘is_v x0’ >> (
  fs[]
 ) >- (
  Cases_on ‘e_exec_unop u x0’ >> (
   fs[]
  ) >>
  res_tac >>
  decide_tac
 ) >>
 res_tac >>
 decide_tac,

 bigstep_e_exec_case'_tac >>
 Cases_on ‘is_v x0’ >> (
  fs[]
 ) >- (
  Cases_on ‘e_exec_cast c x0’ >> (
   fs[]
  ) >>
  res_tac >>
  decide_tac
 ) >>
 res_tac >>
 decide_tac,

 bigstep_e_exec_case'_tac >>
 Cases_on ‘is_v x0’ >- (
  Cases_on ‘x0’ >>
  fs[is_v] >>
  Cases_on ‘is_short_circuitable b’ >> (
   fs[]
  ) >- (
   Cases_on ‘e_exec_short_circuit v b e'’ >> (
    fs[]
   ) >>
   res_tac >>
   decide_tac
  ) >>
  Cases_on ‘bigstep_e_exec scope_lists e' x1’ >> (
   fs[]
  ) >>
  PairCases_on ‘x’ >>
  fs[] >>
  Cases_on ‘is_v x0’ >> (
   fs[]
  ) >- (
   Cases_on ‘e_exec_binop (e_v v) b x0’ >> (
    fs[]
   ) >>
   res_tac >>
   decide_tac
  ) >>
  res_tac >>
  decide_tac
 ) >>
 Cases_on ‘x0’ >> (
  fs[is_v] >>
  rw[] >>
  res_tac >>
  decide_tac
 ),

 (* Concat *)
 bigstep_e_exec_case'_tac >>
 Cases_on ‘is_v_bit x0’ >> (
  fs[]
 ) >- (
  Cases_on ‘bigstep_e_exec scope_lists e' x1’ >> (
   fs[]
  ) >>
  PairCases_on ‘x’ >>
  fs[] >>
  Cases_on ‘is_v_bit x0'’ >> (
   fs[]
  ) >- (
   Cases_on ‘e_exec_concat x0 x0'’ >> (
    fs[]
   ) >>
   res_tac >>
   decide_tac
  ) >>
  res_tac >>
  decide_tac
 ) >>
 res_tac >>
 decide_tac,

 bigstep_e_exec_case'_tac >>
 Cases_on ‘is_v_bit x0’ >> (
  fs[]
 ) >- (
  Cases_on ‘e_exec_slice x0 e' e''’ >> (
   fs[]
  ) >>
  res_tac >>
  decide_tac
 ) >>
 res_tac >>
 decide_tac,

 bigstep_e_exec_case'_tac >>
 res_tac >>
 decide_tac,

 Cases_on ‘bigstep_e_exec_l scope_lists (MAP SND l) n’ >> (
  fs[]
 ) >>
 PairCases_on ‘x’ >>
 fs[] >>
 Cases_on ‘EVERY is_v x0’ >> (
  (* Need to be delicate here... *)
  FULL_SIMP_TAC std_ss [] >>
  fs[]
 ) >> (
  cheat
 )
]
QED

Theorem bigstep_e_exec_unchanged:
!e e' scope_lists n.
bigstep_e_exec scope_lists e n = SOME (e', n) ==>
e = e'
Proof
cheat
QED

Theorem bigstep_e_exec_l_unchanged:
!e_l e_l' scope_lists n.
bigstep_e_exec_l scope_lists e_l n = SOME (e_l', n) ==>
e_l = e_l'
Proof
cheat
QED

Theorem bigstep_e_exec_not_eq:
!e e' scope_lists n.
e <> e' ==>
bigstep_e_exec scope_lists e 0 = SOME (e',n) ==>
n <> 0
Proof
rpt strip_tac >>
Cases_on ‘e’ >> (
 fs[bigstep_e_exec_def]
) >| [
 Cases_on ‘lookup_vexp scope_lists v’ >>
 fs[],

 bigstep_e_exec_case_tac >>
 Cases_on ‘is_v x0’ >> (
  fs[]
 ) >- (
  Cases_on ‘e_exec_acc (e_acc x0 s)’ >> (
   fs[]
  )
 ) >>
 rw[] >>
 imp_res_tac bigstep_e_exec_unchanged,

 bigstep_e_exec_case_tac >>
 Cases_on ‘is_v x0’ >> (
  fs[]
 ) >- (
  Cases_on ‘e_exec_unop u x0’ >> (
   fs[]
  )
 ) >>
 rw[] >>
 imp_res_tac bigstep_e_exec_unchanged,

 bigstep_e_exec_case_tac >>
 Cases_on ‘is_v x0’ >> (
  fs[]
 ) >- (
  Cases_on ‘e_exec_cast c x0’ >> (
   fs[]
  )
 ) >>
 rw[] >>
 imp_res_tac bigstep_e_exec_unchanged,

 bigstep_e_exec_case_tac >>
 Cases_on ‘is_v x0’ >- (
  Cases_on ‘x0’ >>
  fs[is_v] >>
  Cases_on ‘is_short_circuitable b’ >> (
   fs[]
  ) >- (
   Cases_on ‘e_exec_short_circuit v b e0’ >> (
    fs[]
   )
  ) >>
  Cases_on ‘bigstep_e_exec scope_lists e0 x1’ >> (
   fs[]
  ) >>
  PairCases_on ‘x’ >>
  fs[] >>
  Cases_on ‘is_v x0’ >> (
   fs[]
  ) >- (
   Cases_on ‘e_exec_binop (e_v v) b x0’ >> (
    fs[]
   )
  ) >>
  subgoal ‘x1 = 0’ >- (
   rw[] >>
   imp_res_tac bigstep_e_exec_incr >>
   decide_tac
  ) >>
  rw[] >>
  imp_res_tac bigstep_e_exec_unchanged >>
  fs[]
 ) >>
 Cases_on ‘x0’ >>
 fs[is_v] >> (
  rw[] >>
  imp_res_tac bigstep_e_exec_unchanged
 ),

 bigstep_e_exec_case_tac >>
 Cases_on ‘is_v_bit x0’ >> (
  fs[]
 ) >- (
  Cases_on ‘bigstep_e_exec scope_lists e0 x1’ >> (
   fs[]
  ) >>
  PairCases_on ‘x’ >>
  fs[] >>
  Cases_on ‘is_v_bit x0'’ >> (
   fs[]
  ) >- (
   Cases_on ‘e_exec_concat x0 x0'’ >> (
    fs[]
   )
  ) >>
  subgoal ‘x1 = 0’ >- (
   rw[] >>
   imp_res_tac bigstep_e_exec_incr >>
   decide_tac
  ) >>
  rw[] >>
  imp_res_tac bigstep_e_exec_unchanged >>
  fs[]
 ) >>
 rw[] >>
 imp_res_tac bigstep_e_exec_unchanged,

 bigstep_e_exec_case_tac >>
 Cases_on ‘is_v_bit x0’ >> (
  fs[]
 ) >- (
  Cases_on ‘e_exec_slice x0 e0 e1’ >> (
   fs[]
  )
 ) >>
 rw[] >>
 imp_res_tac bigstep_e_exec_unchanged,

 bigstep_e_exec_case_tac >>
 rw[] >>
 imp_res_tac bigstep_e_exec_unchanged,

 Cases_on ‘bigstep_e_exec_l scope_lists (MAP SND l) 0’ >> (
  fs[]
 ) >>
 PairCases_on ‘x’ >>
 fs[] >>
 Cases_on ‘EVERY is_v x0’ >> (
  (* Need to be delicate here... *)
  FULL_SIMP_TAC std_ss []
 ) >>
 fs[] >>
 rw[] >>
 imp_res_tac bigstep_e_exec_l_unchanged >>
 rw[] >>
 fs[p4_auxTheory.ZIP_MAP_FST_SND]
] 
QED

Theorem bigstep_e_exec_not_v_bit:
!e e' scope_lists n.
~is_v_bit e ==>
is_v_bit e' ==>
bigstep_e_exec scope_lists e 0 = SOME (e',n) ==>
n <> 0
Proof
cheat
QED

Theorem bigstep_e_exec_not_v:
!e e' scope_lists n.
~is_v e ==>
is_v e' ==>
bigstep_e_exec scope_lists e 0 = SOME (e',n) ==>
n <> 0
Proof
cheat
(* OLD
Induct_on ‘e’ >> (
 fs[is_v]
) >>
rpt strip_tac >>
Cases_on ‘e'’ >> (

) >> 
fs[is_v, bigstep_e_exec_def] >| [
 Cases_on ‘lookup_vexp scope_lists v'’ >>
 fs[],

 bigstep_e_exec_case_tac >>
 Cases_on ‘is_v x0’ >> (
  fs[]
 ) >>
 Cases_on ‘e_exec_acc (e_acc x0 s)’ >> (
  fs[]
 ),

 bigstep_e_exec_case_tac >>
 Cases_on ‘is_v x0’ >> (
  fs[]
 ) >>
 Cases_on ‘e_exec_unop u x0’ >> (
  fs[]
 ),

 bigstep_e_exec_case_tac >>
 Cases_on ‘is_v x0’ >> (
  fs[]
 ) >>
 Cases_on ‘e_exec_cast c x0’ >> (
  fs[]
 ),

 bigstep_e_exec_case_tac >>
 Cases_on ‘is_v x0’ >> (
  Cases_on ‘x0’ >>
  fs[is_v]
 ) >>
 Cases_on ‘is_short_circuitable b’ >> (
  fs[]
 ) >- (
  Cases_on ‘e_exec_short_circuit v' b e0’ >> (
   fs[]
  )
 ) >>
 Cases_on ‘bigstep_e_exec scope_lists e0 x1’ >> (
  fs[]
 ) >>
 PairCases_on ‘x’ >>
 fs[] >>
 Cases_on ‘is_v x0’ >> (
  Cases_on ‘x0’ >>
  fs[is_v]
 ) >>
 Cases_on ‘e_exec_binop (e_v v') b (e_v v'')’ >> (
  fs[]
 ),

 bigstep_e_exec_case_tac >>
 Cases_on ‘is_v_bit x0’ >> (
  fs[]
 ) >>
 Cases_on ‘bigstep_e_exec scope_lists e0 x1’ >> (
  fs[]
 ) >>
 PairCases_on ‘x’ >>
 fs[] >>
 Cases_on ‘is_v_bit x0'’ >> (
  fs[]
 ) >>
 Cases_on ‘e_exec_concat x0 x0'’ >> (
  fs[]
 ),

 bigstep_e_exec_case_tac >>
 Cases_on ‘is_v_bit x0’ >> (
  fs[]
 ) >>
 Cases_on ‘e_exec_slice x0 e0 e1’ >> (
  fs[]
 ),

 bigstep_e_exec_case_tac,

 Cases_on ‘bigstep_e_exec_l scope_lists (MAP SND l) 0’ >> (
  fs[]
 ) >>
 PairCases_on ‘x’ >>
 fs[] >>
 Cases_on ‘EVERY is_v x0’ >> (
  (* Need to be delicate here... *)
  FULL_SIMP_TAC std_ss []
 ) >>
 fs[]
]
*)
QED


fun bigstep_e_exec_sound_single_rec_tac tmq1 tmq2 =
 Cases_on ‘is_v e’ >> (
  fs[]
 ) >- (
  (* Base case *)
  Cases_on ‘e’ >> (
   fs[is_v, bigstep_e_exec_def]
  ) >>
  Cases_on tmq1 >> (
   fs[]
  )
 ) >>
 (* Recursive case *)
 Cases_on ‘bigstep_e_exec (scope_list ++ g_scope_list') e 0’ >> (
  fs[]
 ) >>
 PairCases_on ‘x’ >>
 fs[] >>
 Cases_on ‘is_v x0’ >> (
  fs[]
 ) >| [
  Cases_on tmq2 >> (
   fs[]
  ) >>
  imp_res_tac bigstep_e_exec_not_v,

  rfs[] >>
  res_tac >>
  fs[]
 ]
;


Theorem bigstep_e_exec_v:
!v scope_list g_scope_list' n.
bigstep_e_exec (scope_list ++ g_scope_list') (e_v v) n = SOME (e_v v, n)
Proof
cheat
QED

Theorem bigstep_e_exec_l_all_red:
!e_l scope_lists n.
unred_mem_index e_l = NONE ==>
bigstep_e_exec_l scope_lists e_l n = SOME (e_l,n+1)
Proof
cheat
QED

Theorem bigstep_e_exec_l_single_unred:
!e_l e_l' e' x scope_lists n.
unred_mem_index e_l = SOME x ==>
bigstep_e_exec_l scope_lists e_l n = SOME (e_l',n+1) ==>
bigstep_e_exec scope_lists (EL x e_l) n = SOME (e', n+1) /\ e_l' = LUPDATE e' x e_l
Proof
cheat
QED

Theorem bigstep_e_exec_sound:
!e scope_list g_scope_list' e' apply_table_f (ext_map:'a ext_map) func_map b_func_map pars_map tbl_map.
bigstep_e_exec (scope_list ++ g_scope_list') e 0 = SOME (e', 1) ==>
e_exec (apply_table_f,ext_map,func_map,b_func_map,pars_map,tbl_map)
             g_scope_list' scope_list e = SOME (e', [])
Proof
Induct_on ‘e’ >> (
 rpt strip_tac >>
 fs[bigstep_e_exec_def, e_exec]
) >| [
 (* var *)
 fs[lookup_vexp_def, lookup_vexp2_def] >>
 Cases_on ‘lookup_map (scope_list ++ g_scope_list') v’ >> (
  fs[]
 ) >>
 Cases_on ‘x’ >> (
  fs[]
 ),

 (* acc *)
 (*
  val tmq1 = ‘e_exec_acc (e_acc (e_v v) s)’
  val tmq2 = ‘e_exec_acc (e_acc x0 s)’
 *)
 bigstep_e_exec_sound_single_rec_tac ‘e_exec_acc (e_acc (e_v v) s)’ ‘e_exec_acc (e_acc x0 s)’,

 (* Unop *)
 bigstep_e_exec_sound_single_rec_tac ‘e_exec_unop u (e_v v)’ ‘e_exec_unop u x0’,

 (* Cast *)
 bigstep_e_exec_sound_single_rec_tac ‘e_exec_cast c (e_v v)’ ‘e_exec_cast c x0’,

 (* Binop *)
 Cases_on ‘bigstep_e_exec (scope_list ++ g_scope_list') e 0’ >> (
  fs[]
 ) >>
 PairCases_on ‘x’ >>
 fs[] >>
 Cases_on ‘is_v e’ >- (
  Cases_on ‘e’ >> (
   fs[is_v]
  ) >>
  subgoal ‘x0 = e_v v /\ x1 = 0’ >- (
   fs[bigstep_e_exec_v]
  ) >>
  gs[] >>
  Cases_on ‘is_short_circuitable b’ >> (
   fs[]
  ) >- (
   Cases_on ‘e_exec_short_circuit v b e'’ >> (
    fs[]
   )
  ) >>
  Cases_on ‘bigstep_e_exec (scope_list ++ g_scope_list') e' 0’ >> (
   fs[]
  ) >>
  PairCases_on ‘x’ >>
  fs[] >>
  Cases_on ‘is_v e'’ >> (
   fs[]
  ) >- (
   (* Second operand not reduced *)
   rw[] >>
   Cases_on ‘e'’ >> (
    fs[is_v]
   ) >>
   subgoal ‘x0' = e_v v' /\ x1' = 0’ >- (
    fs[bigstep_e_exec_v]
   ) >>
   fs[is_v] >>
   Cases_on ‘e_exec_binop (e_v v) b (e_v v')’ >> (
    fs[]
   )
  ) >>
  Cases_on ‘is_v x0'’ >> (
   fs[]
  ) >- (
   (* Contradiction on n *)
   imp_res_tac bigstep_e_exec_not_v >>
   Cases_on ‘e_exec_binop (e_v v) b x0'’ >> (
    fs[]
   )
  ) >>
  (* Inductive case *)
  gs[] >>
  res_tac >>
  fs[] >>
  Cases_on ‘e’ >> (
   fs[is_v_bit, bigstep_e_exec_def]
  )
 ) >>
 (* Second operand *)
 Cases_on ‘is_v x0’ >> (
  fs[]
 ) >- (
  Cases_on ‘x0’ >> (
   fs[is_v]
  ) >>
  subgoal ‘x1 = 1’ >- (
   subgoal ‘is_v $ e_v v’ >- (
    fs[is_v]
   ) >>
   imp_res_tac bigstep_e_exec_not_v >>
   Cases_on ‘bigstep_e_exec (scope_list ++ g_scope_list') e' x1’ >> (
    fs[]
   ) >- (
    Cases_on ‘e_exec_short_circuit v b e'’ >> (
     fs[]
    )
   ) >>
   PairCases_on ‘x’ >>
   fs[] >>
   Cases_on ‘is_short_circuitable b’ >> (
    fs[]
   ) >- (
    Cases_on ‘e_exec_short_circuit v b e'’ >> (
     fs[]
    )
   ) >>
   Cases_on ‘is_v x0’ >> (
    fs[]
   ) >- (
    Cases_on ‘e_exec_binop (e_v v) b x0’ >> (
     fs[]
    ) >>
    imp_res_tac bigstep_e_exec_incr >>
    decide_tac
   ) >>
   imp_res_tac bigstep_e_exec_incr >>
   decide_tac
  ) >>
  fs[] >>
  Cases_on ‘bigstep_e_exec (scope_list ++ g_scope_list') e' 1’ >> (
   fs[]
  ) >- (
   Cases_on ‘e_exec_short_circuit v b e'’ >> (
    fs[]
   )
  ) >>
  Cases_on ‘is_short_circuitable b’ >> (
   fs[]
  ) >- (
   Cases_on ‘e_exec_short_circuit v b e'’ >> (
    fs[]
   )
  ) >>
  PairCases_on ‘x’ >>
  fs[] >>
  subgoal ‘~is_v x0’ >- (
   CCONTR_TAC >>
   fs[] >>
   Cases_on ‘e_exec_binop (e_v v) b x0’ >> (
    fs[]
   ) >>
   imp_res_tac bigstep_e_exec_incr >>
   decide_tac
  ) >>
  gs[] >>
  res_tac >>
  fs[] >>
  subgoal ‘e' = x0’ >- (
   imp_res_tac bigstep_e_exec_unchanged
  ) >>
  Cases_on ‘e’ >> (
   fs[is_v, bigstep_e_exec_def]
  )
 ) >>
 Cases_on ‘x0’ >> Cases_on ‘e’ >> (
  fs[is_v, bigstep_e_exec_def] >>
  gs[] >>
  res_tac >>
  fs[]
 ),

 (* Concat *)
 Cases_on ‘bigstep_e_exec (scope_list ++ g_scope_list') e 0’ >> (
  fs[]
 ) >>
 PairCases_on ‘x’ >>
 fs[] >>
 Cases_on ‘is_v_bit e’ >> (
  fs[]
 ) >- (
  Cases_on ‘e’ >> (
   fs[is_v_bit]
  ) >>
  (* First operand not reduced *)
  subgoal ‘x0 = e_v v /\ x1 = 0’ >- (
   fs[bigstep_e_exec_v]
  ) >>
  fs[] >>
  Cases_on ‘bigstep_e_exec (scope_list ++ g_scope_list') e' 0’ >> (
   fs[]
  ) >>
  PairCases_on ‘x’ >>
  fs[] >>
  Cases_on ‘is_v_bit e'’ >> (
   fs[]
  ) >- (
   (* Second operand not reduced *)
   rw[] >>
   Cases_on ‘e'’ >> (
    fs[is_v_bit]
   ) >>
   subgoal ‘x0' = e_v v' /\ x1' = 0’ >- (
    fs[bigstep_e_exec_v]
   ) >>
   fs[] >>
   Cases_on ‘v’ >> (
    gvs[is_v_bit]
   ) >>
   Cases_on ‘v'’ >> (
    gvs[is_v_bit]
   ) >>
   Cases_on ‘e_exec_concat (e_v (v_bit p)) (e_v (v_bit p'))’ >> (
    fs[]
   )
  ) >>
  (* Second operand was reduced, or e subtype contradiction *)
  Cases_on ‘is_v_bit x0'’ >> (
   fs[]
  ) >- (
   (* Contradiction on n *)
   Cases_on ‘x0'’ >> (
    fs[is_v_bit]
   ) >>
   imp_res_tac bigstep_e_exec_not_v_bit >>
   Cases_on ‘e_exec_concat (e_v v) (e_v v')’ >> (
    fs[]
   )
  ) >>
  (* Inductive case *)
  gs[] >>
  res_tac >>
  fs[] >>
  Cases_on ‘e’ >> (
   fs[is_v_bit, bigstep_e_exec_def]
  )
 ) >>
 (* First operand was reduced *)
 Cases_on ‘is_v_bit x0’ >> (
  fs[]
 ) >- (
  subgoal ‘x1 = 1’ >- (
   imp_res_tac bigstep_e_exec_not_v_bit >>
   Cases_on ‘bigstep_e_exec (scope_list ++ g_scope_list') e' x1’ >> (
    fs[]
   ) >>
   PairCases_on ‘x’ >>
   fs[] >>
   Cases_on ‘is_v_bit x0'’ >> (
    fs[]
   ) >- (
    Cases_on ‘e_exec_concat x0 x0'’ >> (
     fs[]
    ) >>
    imp_res_tac bigstep_e_exec_incr >>
    decide_tac
   ) >>
   imp_res_tac bigstep_e_exec_incr >>
   decide_tac
  ) >>
  fs[] >>
  Cases_on ‘bigstep_e_exec (scope_list ++ g_scope_list') e' 1’ >> (
   fs[]
  ) >>
  PairCases_on ‘x’ >>
  fs[] >>
  subgoal ‘~is_v_bit x0'’ >- (
   CCONTR_TAC >>
   fs[] >>
   Cases_on ‘e_exec_concat x0 x0'’ >> (
    fs[]
   ) >>
   imp_res_tac bigstep_e_exec_incr >>
   decide_tac
  ) >>
  fs[] >>
  gs[] >>
  res_tac >>
  fs[] >>
  subgoal ‘e' = x0'’ >- (
   imp_res_tac bigstep_e_exec_unchanged
  ) >>
  fs[]
 ) >>
 (* Inductive case *)
 gs[] >>
 res_tac >>
 fs[] >>
 Cases_on ‘e’ >> (
  fs[is_v_bit, bigstep_e_exec_def]
 ),

 (* Slice *)
 Cases_on ‘bigstep_e_exec (scope_list ++ g_scope_list') e 0’ >> (
  fs[]
 ) >>
 PairCases_on ‘x’ >>
 fs[] >>
 Cases_on ‘is_v_bit e’ >> (
  fs[]
 ) >- (
  Cases_on ‘e’ >> (
   fs[is_v_bit]
  ) >>
  subgoal ‘x0 = e_v v /\ x1 = 0’ >- (
   fs[bigstep_e_exec_v]
  ) >>
  fs[] >>
  Cases_on ‘e_exec_slice (e_v v) e' e''’ >> (
   fs[]
  )
 ) >>
 subgoal ‘~is_v_bit x0’ >> (
  CCONTR_TAC >>
  fs[] >>
  Cases_on ‘e_exec_slice x0 e' e''’ >> (
   fs[]
  ) >>
  rfs[] >>
  imp_res_tac bigstep_e_exec_unchanged >>
  fs[is_v_bit]
 ) >>
 gs[] >>
 res_tac >>
 fs[],

 (* Select *)
 Cases_on ‘bigstep_e_exec (scope_list ++ g_scope_list') e 0’ >> (
  fs[]
 ) >>
 PairCases_on ‘x’ >>
 fs[] >>
 Cases_on ‘is_v e’ >> (
  fs[]
 ) >- (
  Cases_on ‘e’ >> (
   fs[is_v]
  ) >>
  fs[bigstep_e_exec_v]
 ) >>
 gs[] >>
 res_tac >>
 fs[],

 (* Struct entry *)
(* OLD
 Induct_on ‘l’ >> (
  fs[bigstep_e_exec_def]
 ) >- (
  fs[unred_mem_index_def, unred_mem_def, listTheory.INDEX_FIND_def]
 ) >>
*)
 rpt strip_tac >>
 Cases_on ‘unred_mem_index (MAP SND l)’ >> (
  fs[]
 ) >- (
  imp_res_tac bigstep_e_exec_l_all_red >>
  Cases_on ‘bigstep_e_exec_l (scope_list ++ g_scope_list') (MAP SND l) 0’ >> (
   fs[]
  ) >>
  PairCases_on ‘x’ >>
  fs[] >>
  subgoal ‘EVERY is_v x0’ >- (
   cheat
  ) >>
  fs[] >>
  gvs[]
 ) >>
 Cases_on ‘bigstep_e_exec_l (scope_list ++ g_scope_list') (MAP SND l) 0’ >> (
  fs[]
 ) >>
 PairCases_on ‘x'’ >>
 fs[] >>
 subgoal ‘~EVERY is_v x'0’ >- (
  cheat
 ) >>
 FULL_SIMP_TAC std_ss [] >>
 rw[] >>
 imp_res_tac bigstep_e_exec_l_single_unred >>
 (* TODO: This requires some further thought... *)
 cheat
]
QED

Theorem scope_lists_separate:
!scope_lists top_scope scope_list scope_list' g_scope_list' g_scope_list''.
scope_lists = top_scope::(scope_list ++ g_scope_list') ==>
           separate scope_lists = (SOME g_scope_list'',SOME scope_list') ==>
           g_scope_list' = g_scope_list'' /\ top_scope::scope_list = scope_list'
Proof
rpt gen_tac >> rpt disch_tac >>
subgoal ‘LENGTH g_scope_list' = 2’ >- (
 (* TODO: ??? *)
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
  Cases_on ‘bigstep_e_exec (top_scope::(scope_list ++ g_scope_list')) e 0’ >> (
   fs[]
  ) >- (
   Cases_on ‘e’ >> (
    fs[]
   )
  ) >>
  PairCases_on ‘x’ >>
  fs[] >>
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
   Cases_on ‘is_v x0’ >> (
    fs[]
   ) >- (
    Cases_on ‘stmt_exec_ass l x0 (top_scope::(scope_list ++ g_scope_list'))’ >> (
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
  Cases_on ‘bigstep_e_exec (top_scope::(scope_list ++ g_scope_list')) e 0’ >> (
   fs[]
  ) >- (
   Cases_on ‘e’ >> (
    fs[]
   )
  ) >>
  PairCases_on ‘x’ >>
  fs[] >>
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
  Cases_on ‘bigstep_e_exec (top_scope::(scope_list ++ g_scope_list')) e 0’ >> (
   fs[]
  ) >>
  PairCases_on ‘x’ >>
  gs[] >>
  rw[] >>
  FULL_SIMP_TAC pure_ss [GSYM listTheory.APPEND] >>
  imp_res_tac bigstep_e_exec_sound >>
  fs[] >>
  irule scope_lists_separate >>
  metis_tac[]
 ),

 (* seq - recursive case *)
 cheat,

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
    ) >>
    fs[bigstep_stmt_exec_def, bigstep_e_exec_def]
   )
  ) >>
  (* e reduction *)
  fs[bigstep_stmt_exec_def] >>
  Cases_on ‘bigstep_e_exec (top_scope::(scope_list ++ g_scope_list')) e 0’ >> (
   fs[]
  ) >>
  PairCases_on ‘x’ >>
  gs[] >>
  rw[] >>
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
   cheat
  ) >>
  (* e reduction *)
  fs[bigstep_stmt_exec_def] >>
  Cases_on ‘bigstep_e_exec_l (top_scope::(scope_list ++ g_scope_list')) l 0’ >> (
   fs[]
  ) >>
  PairCases_on ‘x'3'’ >>
  gs[] >>
  rw[] >>
  FULL_SIMP_TAC pure_ss [GSYM listTheory.APPEND] >>
  cheat
(*
  imp_res_tac bigstep_e_exec_l_sound >>
  fs[] >>
  irule scope_lists_separate >>
  metis_tac[]
*)
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
imp_res_tac bigstep_arch_exec_SOME_trace >>
qpat_x_assum ‘!ctx aenv. ?g_scope_list'' arch_frame_list''. _’ (fn thm => ASSUME_TAC (Q.SPECL [‘ctx’, ‘aenv’] thm)) >>
fs[] >>
res_tac
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
