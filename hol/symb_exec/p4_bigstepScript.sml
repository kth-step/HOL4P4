open HolKernel boolLib liteLib simpLib Parse bossLib;
open p4Theory p4_exec_semTheory;

val _ = new_theory "p4_bigstep";

(* This file contains a big-step semantics for a fragment of P4 that
 * contains mostly local instructions *)

(* The symbolic execution should attempt to use this when
 * then next statement to be reduced is stmt_empty, (stmt_seq stmt_ass _)
 * or (stmt_seq stmt_empty _) *)

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
      | SOME v => SOME (v, n+1)
      | NONE => NONE)
    else SOME (e_acc e_v_struct' x, n')
   | NONE => NONE))
  /\
 (*********************************)
 (* Struct/header field reduction *)
 (bigstep_e_exec scope_lists (e_struct x_e_l) n =
  case bigstep_e_exec_l scope_lists (MAP SND x_e_l) n of
  | SOME (e_l', n') =>
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
cheat
End

Definition bigstep_stmt_exec_def:
 (bigstep_stmt_exec scope_lists (stmt_ass lval e) n =
  (case bigstep_e_exec scope_lists e n of
   | SOME (e', n') =>
    if is_v e'
    then
     (case stmt_exec_ass lval e' scope_lists of
      | SOME scope_lists' =>
       SOME (stmt_empty, scope_lists', n'+1)
      | NONE => NONE)
    else SOME (stmt_ass lval e', scope_lists, n')
   | _ => NONE))
  /\
 (bigstep_stmt_exec scope_lists (stmt_seq stmt1 stmt2) n =
  if is_empty stmt1
  then bigstep_stmt_exec scope_lists stmt2 (n+1)
  else
   (case bigstep_stmt_exec scope_lists stmt1 n of
    | SOME (stmt1', scope_lists', n') =>
     if is_empty stmt1'
     then bigstep_stmt_exec scope_lists' stmt2 (n'+1)
     else SOME (stmt_seq stmt1' stmt2, scope_lists', n')
    | _ => NONE)) /\
 (**********************)
 (* NESTED EXPRESSIONS *)
 (**********************)
 (bigstep_stmt_exec scope_lists (stmt_ret e) n =
  (case bigstep_e_exec scope_lists e n of
   | SOME (e', n') =>
    SOME (stmt_ret e', scope_lists, n')
   | _ => NONE))
  /\
 (bigstep_stmt_exec scope_lists (stmt_trans e) n =
  (case bigstep_e_exec scope_lists e n of
   | SOME (e', n') =>
    SOME (stmt_trans e', scope_lists, n')
   | _ => NONE))
  /\
(* TODO: Some problem with p4_symb_exec_test2
 (bigstep_stmt_exec scope_lists (stmt_cond e stmt1 stmt2) n =
  (case bigstep_e_exec scope_lists e n of
   | SOME (e', n') =>
    SOME (stmt_cond e' stmt1 stmt2, scope_lists, n')
   | _ => NONE))
  /\
*)
 (bigstep_stmt_exec scope_lists (stmt_app t_name e_l) n =
  (case bigstep_e_exec_l scope_lists e_l n of
   | SOME (e_l', n') =>
    SOME (stmt_app t_name e_l', scope_lists, n')
   | _ => NONE))
  /\
 (bigstep_stmt_exec scope_lists stmt n =
  SOME (stmt, scope_lists, n))
End

(* TODO: The result of this should be sound with respect to n steps of
 * the executable semantics running inside a programmable block *)
Definition bigstep_exec_def:
 bigstep_exec (g_scope_list, scope_list) stmt =
  case bigstep_stmt_exec (scope_list++g_scope_list) stmt 0 of
  | SOME (stmt', scope_lists, n) =>
   (case separate scope_lists of
    | (SOME g_scope_list', SOME scope_list') =>
     SOME (stmt', g_scope_list', scope_list', n)
    | _ => NONE)
  | NONE => NONE
End

(* This uses top-level constructs and might be more convenient to use *)
Definition bigstep_arch_exec_def:
 (bigstep_arch_exec (g_scope_list:g_scope_list) (arch_frame_list_regular frame_list) =
  case frame_list of
  | ((funn, stmt_stack, scope_list)::t) =>
   (case stmt_stack of
    | (stmt::t') =>
     (case bigstep_exec (g_scope_list, scope_list) stmt of
      | SOME (stmt', g_scope_list', scope_list', n) =>
       SOME (g_scope_list', arch_frame_list_regular ((funn, (stmt'::t'), scope_list')::t), n)
      | _ => NONE)
    | _ => NONE)
  | _ => NONE
 ) /\
 (bigstep_arch_exec _ _ = NONE)
End

Theorem bigstep_arch_exec_sound:
!i ab_list x el pblock_map pbl_type x_d_list b_func_map decl_list pars_map tbl_map funn stmt_stack scope_list frame_list func_map g_scope_list g_scope_list' g_scope_list'' arch_frame_list' n g_scope_list''' ffblock_map input_f output_f copyin_pbl copyout_pbl apply_table_f ext_map aenv.
(EL i ab_list = (arch_block_pbl x el)) ==>
(ALOOKUP pblock_map x = SOME (pbl_type, x_d_list, b_func_map, decl_list, pars_map, tbl_map)) ==>
~(state_fin_exec status_running ((funn, stmt_stack, scope_list)::frame_list)) ==>
scopes_to_pass funn func_map b_func_map g_scope_list = SOME g_scope_list' ==>
map_to_pass funn b_func_map <> NONE ==>
tbl_to_pass funn b_func_map tbl_map <> NONE ==>
bigstep_arch_exec (g_scope_list':g_scope_list) (arch_frame_list_regular ((funn, stmt_stack, scope_list)::frame_list)) = SOME (g_scope_list'', arch_frame_list', n) ==>
scopes_to_retrieve funn func_map b_func_map g_scope_list g_scope_list'' = SOME g_scope_list''' ==>
arch_multi_exec ((ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map):'a actx) (aenv, g_scope_list, (arch_frame_list_regular ((funn, stmt_stack, scope_list)::frame_list)), status_running) n = SOME (aenv, g_scope_list''', arch_frame_list', status_running)
Proof
cheat
QED

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
Theorem bigstep_arch_exec_comp:
!assl ab_list pblock_map func_map g_scope_list arch_frame_list status aenv' g_scope_list' g_scope_list'' n' arch_frame_list' arch_frame_list'' n ffblock_map input_f output_f copyin_pbl copyout_pbl apply_table_f ext_map aenv.
(assl ==> arch_multi_exec ((ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map):'a actx) (aenv, g_scope_list, arch_frame_list, status) n = SOME (aenv', g_scope_list', arch_frame_list', status_running)) ==>
in_local_fun func_map arch_frame_list' ==>
bigstep_arch_exec (g_scope_list':g_scope_list) arch_frame_list' = SOME (g_scope_list'', arch_frame_list'', n') ==>
(assl ==> arch_multi_exec ((ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map):'a actx) (aenv, g_scope_list, arch_frame_list, status_running) (n+n') = SOME (aenv', g_scope_list'', arch_frame_list'', status_running))
Proof
cheat
QED

Theorem bigstep_arch_exec_comp':
!assl ctx g_scope_list arch_frame_list status aenv' g_scope_list' g_scope_list'' n' arch_frame_list' arch_frame_list'' n aenv.
(assl ==> arch_multi_exec ctx (aenv, g_scope_list, arch_frame_list, status) n = SOME (aenv', g_scope_list', arch_frame_list', status_running)) ==>
in_local_fun' ctx arch_frame_list' ==>
bigstep_arch_exec (g_scope_list':g_scope_list) arch_frame_list' = SOME (g_scope_list'', arch_frame_list'', n') ==>
(assl ==> arch_multi_exec ctx (aenv, g_scope_list, arch_frame_list, status_running) (n+n') = SOME (aenv', g_scope_list'', arch_frame_list'', status_running))
Proof
cheat
QED

val _ = export_theory ();
