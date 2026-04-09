open HolKernel boolLib Parse bossLib;

val _ = new_theory "p4_full_bigstep";

open p4Syntax;
open ottTheory;
open p4Theory p4_auxTheory;

open p4_exec_semTheory;

val _ = intLib.deprecate_int();

(* This file contains a HOL4P4 big-step semantics for the entire pipeline *)
(* Known issues/design choices:
 * * The statement-level semantics returns upon every function call pushing a new frame. An alternative
 *   may be to use a mutual recursion scheme.
 * * This keeps certain half-reduced results instead of returning NONE. Easier for debugging, but bad
 *   for compiler and reachability proofs.
 * * Expression semantics could perhaps re-use the list expression (INR) reductions for function call
 * * Proofs of bigstep_e_exec_decr and bigstep_stmt_exec_decr
 * * To simplify the termination proofs, the semantics currently performs checks (e.g. "n' > n") for
 *   fuel consumed by certain recursive calls.
 * *)

(* TODO: Move this? *)
Definition lookup_vexp_def:
 lookup_vexp scope_list x =
  case lookup_map scope_list x of
  | SOME (v,str_opt) => SOME v
  | NONE => NONE
End

Definition bigstep_e_exec_def:
 (********************)
 (* Variable look-up *)
 (bigstep_e_exec (e_ctx:'a e_ctx) (scope_lists:scope_list) (INL (e_var x)) ((SUC n):num) =
  case lookup_vexp scope_lists x of
  | SOME v => SOME (INL $ e_v v, [], n)
  | NONE => NONE)
  /\
 (******************************)
 (* Struct/header field access *)
 (bigstep_e_exec e_ctx scope_lists (INL (e_acc e_v_struct x)) (SUC n) =
  (case bigstep_e_exec e_ctx scope_lists (INL e_v_struct) n of
   | SOME (INL $ e_v_struct', frame_list, n') =>
    if n' = 0 \/ ~NULL frame_list
    then SOME (INL $ (e_acc e_v_struct' x), frame_list, n')
    else
     (* NOTE that an expression that has been fully reduced to a value entails
      * that no new frame list has been pushed *)
     (if is_v e_v_struct'
      then
       (case e_exec_acc (e_acc e_v_struct' x) of
        | SOME v => SOME (INL $ v, frame_list, n'-1)
        | NONE => NONE)
      else SOME (INL $ e_acc e_v_struct' x, frame_list, n'-1))
   | _ => NONE))
  /\
 (**************************)
 (* Struct field reduction *)
 (bigstep_e_exec e_ctx scope_lists (INL (e_struct x_e_l)) (SUC n) =
  case bigstep_e_exec e_ctx scope_lists (INR (MAP SND x_e_l)) n of
  | SOME (INR $ e_l', frame_list, n') =>
   if n' = 0 \/ ~NULL frame_list \/ n' > n
   then SOME (INL $ (e_struct (ZIP (MAP FST x_e_l, e_l'))), frame_list, n')
   else
    (case vl_of_el_exec e_l' of
     | SOME v_l =>
      SOME (INL $ e_v $ v_struct (ZIP (MAP FST x_e_l, v_l)), frame_list, n'-1)
     | NONE =>
      SOME (INL $ e_struct (ZIP (MAP FST x_e_l, e_l')), frame_list, n'-1))
  | _ => NONE)
  /\
 (**************************)
 (* Header field reduction *)
 (bigstep_e_exec e_ctx scope_lists (INL (e_header validity x_e_l)) (SUC n) =
  case bigstep_e_exec e_ctx scope_lists (INR (MAP SND x_e_l)) n of
  | SOME (INR $ e_l', frame_list, n') =>
   if n' = 0 \/ ~NULL frame_list \/ n' > n
   then SOME (INL $ (e_header validity (ZIP (MAP FST x_e_l, e_l'))), frame_list, n')
   else
    (case vl_of_el_exec e_l' of
     | SOME v_l =>
      SOME (INL $ e_v $ v_header validity (ZIP (MAP FST x_e_l, v_l)), frame_list, n'-1)
     | NONE =>
      SOME (INL $ e_header validity (ZIP (MAP FST x_e_l, e_l')), frame_list, n'-1))
  | _ => NONE)
  /\
 (********)
 (* Cast *)
 (bigstep_e_exec e_ctx scope_lists (INL (e_cast cast e)) (SUC n) =
  (case bigstep_e_exec e_ctx scope_lists (INL e) n of
   | SOME (INL $ e', frame_list, n') =>
    if n' = 0 \/ ~NULL frame_list
    then SOME (INL $ (e_cast cast e'), frame_list, n')
    else
     if is_v e'
     then
      (case e_exec_cast cast e' of
       | SOME v => SOME (INL $ e_v v, frame_list, n'-1)
       | NONE => NONE)
     else
      SOME (INL $ e_cast cast e', frame_list, n'-1)
   | _ => NONE))
  /\
 (********************)
 (* Unary arithmetic *)
 (bigstep_e_exec e_ctx scope_lists (INL (e_unop unop e)) (SUC n) =
  (case bigstep_e_exec e_ctx scope_lists (INL e) n of
   | SOME (INL $ e', frame_list, n') =>
    if n' = 0 \/ ~NULL frame_list
    then SOME (INL $ (e_unop unop e'), frame_list, n')
    else
     if is_v e'
     then 
      (case e_exec_unop unop e' of
       | SOME v => SOME (INL $ e_v v, frame_list, n'-1)
       | NONE => NONE)
     else
      SOME (INL $ e_unop unop e', frame_list, n'-1)
   | _ => NONE))
  /\
 (*********************)
 (* Binary arithmetic *)
 (bigstep_e_exec e_ctx scope_lists (INL (e_binop e1 binop e2)) (SUC n) =
  (case bigstep_e_exec e_ctx scope_lists (INL e1) n of
   | SOME (INL $ e1', frame_list, 0) =>
    SOME (INL $ (e_binop e1' binop e2), frame_list, 0)
   | SOME (INL $ e1', frame_list, SUC n') =>
    if ~NULL frame_list \/ n' > n
    then SOME (INL $ (e_binop e1' binop e2), frame_list, SUC n')
    else
     (case e1' of
      | (e_v v) =>
       if is_short_circuitable binop
       then
        (case e_exec_short_circuit v binop e2 of
         | SOME e' => SOME (INL $ e', frame_list, n')
         | NONE => NONE)
       else
        (* NOTE that since e1' was reduced to a value, frame_list must have been
         * [] - this is abused here for simplicity *)
        (case bigstep_e_exec e_ctx scope_lists (INL e2) n' of
         | SOME (INL $ e2', frame_list', 0) =>
          SOME (INL $ (e_binop e1' binop e2'), frame_list', 0)
         | SOME (INL $ e2', frame_list', SUC n'') =>
          if ~NULL frame_list'
          then SOME (INL $ (e_binop e1' binop e2'), frame_list', SUC n'')
          else         
           if is_v e2'
           then
            (case e_exec_binop e1' binop e2' of
             | SOME v' => SOME (INL $ e_v v', frame_list', n'')
             | NONE => NONE)
           else
            SOME (INL $ e_binop e1' binop e2', frame_list', n'')
         | _ => NONE)
      | _ =>
       SOME (INL $ e_binop e1' binop e2, frame_list, n'))
   | _ => NONE))
  /\
 (*****************)
 (* Concatenation *)
 (bigstep_e_exec e_ctx scope_lists (INL (e_concat e1 e2)) (SUC n) =
  case bigstep_e_exec e_ctx scope_lists (INL e1) n of
  | SOME (INL $ e1', frame_list, n') =>
   if n' = 0 \/ ~NULL frame_list \/ n' > n
   then SOME (INL $ (e_concat e1' e2), frame_list, n')
   else
    if is_v_bit e1'
    then
     (case bigstep_e_exec e_ctx scope_lists (INL e2) (n'-1) of
      | SOME (INL $ e2', frame_list', n'') =>
       if n'' = 0 \/ ~NULL frame_list'
       then SOME (INL $ (e_concat e1' e2'), frame_list', n'')
       else
        (if is_v_bit e2'
         then 
          (case e_exec_concat e1' e2' of
           | SOME v => SOME (INL $ e_v v, frame_list', n''-1)
           | NONE => NONE)
         else
          SOME (INL $ e_concat e1' e2', frame_list', n''-1))
      | _ => NONE)
    else
     SOME (INL $ e_concat e1' e2, frame_list, n')
  | _ => NONE)
  /\
 (***********)
 (* Slicing *)
 (bigstep_e_exec e_ctx scope_lists (INL (e_slice e1 e2 e3)) (SUC n) =
  if (is_v_bit e2 /\ is_v_bit e3)
  then
   (case bigstep_e_exec e_ctx scope_lists (INL e1) n of
    | SOME (INL $ e1', frame_list, n') =>
     if n' = 0 \/ ~NULL frame_list
     then SOME (INL $ (e_concat e1' e2), frame_list, n')
     else
      if is_v_bit e1'
      then 
       (case e_exec_slice e1' e2 e3 of
        | SOME v => SOME (INL $ e_v v, frame_list, n'-1)
        | NONE => NONE)
      else
       SOME (INL $ e_slice e1' e2 e3, frame_list, n'-1)
    | _ => NONE)
   else NONE)
  /\
 (************************)
 (* Function/extern call *)
 (bigstep_e_exec (ext_map, func_map, b_func_map) scope_lists (INL (e_call funn e_l)) (SUC n) =
  (case lookup_funn_sig_body funn func_map b_func_map ext_map of
  | SOME (stmt, x_d_l) =>
   if LENGTH x_d_l = LENGTH e_l
   then
    (* TODO: Inefficient, but re-uses existing stuff *)
    (case unred_arg_index (MAP SND x_d_l) e_l of
     | SOME i =>
      (case oEL i e_l of
       | SOME elem =>
        (case bigstep_e_exec (ext_map, func_map, b_func_map) scope_lists (INL elem) n of
         | SOME (INL $ e', frame_list, n') =>
          if n' = 0 \/ ~NULL frame_list \/ n' > n
          then SOME (INL $ e_call funn (LUPDATE e' i e_l), frame_list, (n'-1))
          else bigstep_e_exec (ext_map, func_map, b_func_map) scope_lists (INL $ e_call funn (LUPDATE e' i e_l)) (n'-1)
         | _ => NONE)
       | NONE => NONE)
     | NONE =>
      (case copyin_exec uninit_arb (MAP FST x_d_l) (MAP SND x_d_l) e_l (LASTN 2 scope_lists) (BUTLASTN 2 scope_lists) of
       | SOME scope => 
        SOME (INL $ e_var (varn_star funn), [(funn, [stmt], [scope])], n)
       | NONE => NONE))
   else NONE
  | NONE => NONE))
 /\
 (**********)
 (* Select *)
 (bigstep_e_exec e_ctx scope_lists (INL (e_select e s_l_x_l x)) (SUC n) =
  case bigstep_e_exec e_ctx scope_lists (INL e) n of
  | SOME (INL $ e', frame_list, n') =>
   if n' = 0 \/ ~NULL frame_list
   then SOME (INL $ e_select e' s_l_x_l x, frame_list, n')
   else
    if is_v e'
    then 
     (case e_exec_select e' s_l_x_l x of
      | SOME x' => SOME (INL $ e_v (v_str x'), frame_list, n'-1)
      | NONE => NONE)
    else SOME (INL $ e_select e' s_l_x_l x, frame_list, n'-1)
  | _ => NONE)
 /\
 (********)
 (* List *)
 (* TODO: Left unimplemented, since this is also the case for the executable semantics *)
 (bigstep_e_exec e_ctx scope_lists (INL (e_list e_l)) n = NONE)
 /\
 (bigstep_e_exec e_ctx scope_lists (INL $ e_v v) (SUC n) = SOME (INL $ e_v v, [], n))
 /\
 (bigstep_e_exec e_ctx scope_lists (INL e) 0 = SOME (INL $ e, [], 0))
 /\
 (bigstep_e_exec e_ctx scope_lists (INR el) 0 = SOME (INR $ el, [], 0))
 /\
 (bigstep_e_exec e_ctx scope_lists (INR []) n = SOME (INR $ [], [], n))
 /\
 (bigstep_e_exec e_ctx scope_lists (INR (h::t)) (SUC n) =
  case bigstep_e_exec e_ctx scope_lists (INL h) n of
  | SOME (INL h', frame_list, n') =>
   if n' = 0 \/ ~NULL frame_list \/ n' > n
   then SOME (INR $ h'::t, frame_list, n')
   else
    if is_v h'
    then
     (case bigstep_e_exec e_ctx scope_lists (INR t) n' of
      | SOME (INR t', frame_list', n'') => SOME (INR $ h'::t', frame_list', n'')
      | _ => NONE)
    else SOME (INR $ h'::t, frame_list, n'-1)
  | _ => NONE)
End

(* TODO: This has recursive calls, so may require induction *)
Theorem bigstep_e_exec_decr:
!ctx scope_lists e_el n e_el' frame_list n'.
bigstep_e_exec ctx scope_lists e_el n = SOME (e_el',frame_list,n') ==>
n' <= n
Proof
Induct_on ‘e_el’ >- (
 Induct_on ‘x’ >> (
   rpt strip_tac >>
   Cases_on ‘n’ >>
   gvs[bigstep_e_exec_def, AllCaseEqs()] >>
   res_tac >> gs[]
 ) >> (
  (* TODO: Remaining cases also require induction on list *)
  cheat
 )
) >>
Induct_on ‘y’ >- (
 rpt strip_tac >>
 Cases_on ‘n’ >>
 gvs[bigstep_e_exec_def, AllCaseEqs()] >>
 res_tac >> gs[]
) >>
rpt strip_tac >>
Cases_on ‘n’ >>
gvs[bigstep_e_exec_def, AllCaseEqs()] >- (
 (* Case: function was called *)
 cheat
) >- (
 (* Case: ??? *)
 cheat
) >>
res_tac >>
decide_tac
QED

Definition bigstep_stmt_exec_def:
 (bigstep_stmt_exec (ctx:'a ctx) ((ascope, g_scope_list, frame_list, (status_returnv v)):'a state) _ = NONE)
  /\
 (bigstep_stmt_exec _ (_, _, _, status_trans x) _ = NONE)
  /\
 (* Empty frame list *)
 (bigstep_stmt_exec _ (_, _, [], _) _ = NONE)
  /\
 (* Empty scope stack *)
 (bigstep_stmt_exec _ (_, _, [(funn, stmt_stack, [])], _) _ = NONE)
  /\
 (bigstep_stmt_exec ctx (ascope, g_scope_list, [(funn, [stmt_empty], scope_list)], status) (SUC n) = SOME (ascope, g_scope_list, [(funn, [stmt_empty], scope_list)], status, n))
  /\
 (**************)
 (* Assignment *)
 (bigstep_stmt_exec ctx (ascope, g_scope_list, [(funn, [stmt_ass lval e], scope_list)], status_running) (SUC n) =
    (case bigstep_e_exec (get_e_ctx ctx) (scope_list++g_scope_list) (INL e) (SUC n) of
     | SOME (INL e', frame_list, n') =>
      if n' = 0
      then SOME (ascope, g_scope_list, frame_list++[(funn, [stmt_ass lval e'], scope_list)], status_running, 0)
      else
       if is_v e'
       then
        (case stmt_exec_ass lval e' (scope_list++g_scope_list) of
         | SOME scope_lists' =>
          (case separate_exec scope_lists' of
           | SOME (g_scope_list', scope_list'') =>
            SOME (ascope, g_scope_list', [(funn, [stmt_empty], scope_list'')], status_running, n'-1)
           | _ => NONE)
         | NONE => NONE)
       else
        SOME (ascope, g_scope_list, frame_list++[(funn, [stmt_ass lval e'], scope_list)], status_running, n')
     | _ => NONE))
  /\
 (**************)
 (* Transition *)
 (bigstep_stmt_exec ctx (ascope, g_scope_list, [(funn, [stmt_trans e], scope_list)], status_running) (SUC n) =
  (case bigstep_e_exec (get_e_ctx ctx) (scope_list++g_scope_list) (INL e) (SUC n) of
   | SOME (INL e', frame_list, n') =>
    if n' = 0
    then SOME (ascope, g_scope_list, frame_list++[(funn, [stmt_trans e'], scope_list)], status_running, 0)
    else
     if is_v e'
     then
      (case stmt_exec_trans e' of
       | SOME status' => SOME (ascope, g_scope_list, [(funn, [stmt_empty], scope_list)], status', n'-1)
       | NONE => NONE)
     else
      SOME (ascope, g_scope_list, frame_list++[(funn, [stmt_trans e'], scope_list)], status_running, n')
   | _ => NONE))
  /\
 (***************)
 (* Conditional *)
 (bigstep_stmt_exec ctx (ascope, g_scope_list, [(funn, [stmt_cond e stmt1 stmt2], scope_list)], status_running) (SUC n) =
  (case bigstep_e_exec (get_e_ctx ctx) (scope_list++g_scope_list) (INL e) (SUC n) of
   | SOME (INL e', frame_list, n') =>
    if n' = 0
    then SOME (ascope, g_scope_list, frame_list++[(funn, [stmt_cond e' stmt1 stmt2], scope_list)], status_running, 0)
    else
     if is_v_bool e'
     then
      (case stmt_exec_cond e' of
       | SOME T => bigstep_stmt_exec ctx (ascope, g_scope_list, [(funn, [stmt1], scope_list)], status_running) (n'-1)
       | SOME F => bigstep_stmt_exec ctx (ascope, g_scope_list, [(funn, [stmt2], scope_list)], status_running) (n'-1)
       | NONE => NONE)
     else
      SOME (ascope, g_scope_list, frame_list++[(funn, [stmt_cond e' stmt1 stmt2], scope_list)], status_running, n')
   | _ => NONE))
  /\
 (*********************)
 (* Table application *)
 (bigstep_stmt_exec (apply_table_f, ext_map, func_map, b_func_map, pars_map, tbl_map) (ascope, g_scope_list, [(funn, [stmt_app t_name e_l], scope_list)], status_running) (SUC n) =
  (case bigstep_e_exec (ext_map,func_map,b_func_map) (scope_list++g_scope_list) (INR e_l) (SUC n) of
   | SOME (INR e_l', frame_list, n') =>
    if n' = 0
    then SOME (ascope, g_scope_list, frame_list++[(funn, [stmt_app t_name e_l'], scope_list)], status_running, 0)
    else
    (if index_not_const e_l = NONE
     then
      (case ALOOKUP tbl_map t_name of
       | SOME (mk_l, (default_f, default_f_args)) =>
        (if LENGTH mk_l = LENGTH e_l
         then
          (case apply_table_f (t_name, e_l, mk_l, (default_f, default_f_args), ascope) of
           | SOME (f, f_args) =>
            SOME (ascope, g_scope_list, [(funn, [stmt_ass lval_null (e_call (funn_name f) f_args)], scope_list)], status_running, (n'-1))
           | NONE => NONE)
         else NONE)
       | _ => NONE)
     else
      SOME (ascope, g_scope_list, frame_list++[(funn, [stmt_app t_name e_l'], scope_list)], status_running, n')
     )
   | _ => NONE))
  /\
 (**********)
 (* Return *)
 (bigstep_stmt_exec ctx (ascope, g_scope_list, [(funn, [stmt_ret e], scope_list)], status_running) (SUC n) =
  (case bigstep_e_exec (get_e_ctx ctx) (scope_list++g_scope_list) (INL e) (SUC n) of
   | SOME (INL e', frame_list, n') =>
    if n' = 0
    then SOME (ascope, g_scope_list, frame_list++[(funn, [stmt_ret e'], scope_list)], status_running, 0)
    else
     (case get_v e' of
      | SOME v =>
       SOME (ascope, g_scope_list, [(funn, [stmt_empty], scope_list)], status_returnv v, n'-1)
      | NONE =>
       SOME (ascope, g_scope_list, frame_list++[(funn, [stmt_ret e'], scope_list)], status_running, n'))
   | _ => NONE))
  /\
 (**********)
 (* Extern *)
 (bigstep_stmt_exec (apply_table_f, ext_map, func_map, b_func_map, pars_map, tbl_map) (ascope, g_scope_list, [(funn, [stmt_ext], scope_list)], status_running) (SUC n) =
  (case lookup_ext_fun funn ext_map of
   | SOME ext_fun =>
    (case ext_fun (ascope, g_scope_list, scope_list) of
     | SOME (ascope', scope_list', status') =>
      SOME (ascope', g_scope_list, [(funn, [stmt_empty], scope_list')], status', n)
     | NONE => NONE)
   | NONE => NONE))
  /\
 (*********)
 (* Block *)
 (bigstep_stmt_exec ctx (ascope, g_scope_list, [(funn, [stmt_block decl_list stmt], scope_list)], status_running) (SUC n) =
   SOME (ascope, g_scope_list, [(funn, [stmt]++[stmt_empty], ((declare_list_in_fresh_scope_exec' decl_list)::scope_list))], status_running, n))
  /\
 (************)
 (* Sequence *)
 (bigstep_stmt_exec ctx (ascope, g_scope_list, [(funn, [stmt_seq stmt1 stmt2], scope_list)], status_running) (SUC n) =
  if is_empty stmt1
  then bigstep_stmt_exec ctx (ascope, g_scope_list, [(funn, [stmt2], scope_list)], status_running) n
  else
   (case bigstep_stmt_exec ctx (ascope, g_scope_list, [(funn, [stmt1], scope_list)], status_running) n of
    | SOME (ascope', g_scope_list', frame_list', status', n') =>
     if n' = 0
     then SOME (ascope', g_scope_list', frame_list', status', 0)
     else
      if n' < n
      then
       (case status' of
        | status_running =>
         (case frame_list' of
          | [(funn, [stmt'], scope_list')] =>
           if stmt' = stmt_empty
           then
            bigstep_stmt_exec ctx (ascope', g_scope_list', [(funn, [stmt2], scope_list')], status_running) (n'-1)
           else SOME (ascope', g_scope_list', frame_list', status', n')
          | [(funn, stmt'::stmt_stack', scope_list')] =>
           (* If a block is not fully reduced, this must signify something irreducible *)
           SOME (ascope', g_scope_list', [(funn, stmt'::stmt_stack', scope_list')], status', n')
          | (frame::frame_list'') =>
           SOME (ascope', g_scope_list', frame::frame_list'', status', n')
          | _ => NONE
         )
        | _ =>
         SOME (ascope', g_scope_list', frame_list', status', n'))
      else NONE
    | _ => NONE)) /\
 (*********************)
 (* Stmt stack clause *)
 (bigstep_stmt_exec ctx (ascope, g_scope_list, [(funn, stmt::stmt_stack, scope_list)], status) (SUC n) =
  if is_empty stmt
  then
   (case stmt_stack of
    | [] => NONE
    | _ =>
     (case scope_list of
      | [] => NONE
      | (h_scope::scope_list') =>
       bigstep_stmt_exec ctx (ascope, g_scope_list, [(funn, stmt_stack, scope_list')], status) n))
  else
   (case bigstep_stmt_exec ctx (ascope, g_scope_list, [(funn, [stmt], scope_list)], status) n of
    | SOME (ascope',g_scope_list',frame_list',status',n') =>
      (case frame_list' of
       | [(funn,[stmt'],scope_list')] =>
        if stmt' = stmt_empty
        then
         if n' = 0 \/ n' > n
         then SOME (ascope', g_scope_list', frame_list', status', n')
         else
          bigstep_stmt_exec ctx (ascope', g_scope_list', [(funn, stmt_stack, scope_list')], status') (n'-1)
        else SOME (ascope', g_scope_list', frame_list', status', n')
       | [(funn,[stmt'; stmt''],scope_list')] =>
        SOME (ascope', g_scope_list', frame_list', status', n')
       | (frame::frame_list'') =>
        SOME (ascope', g_scope_list', frame::frame_list'', status', n')
       | _ => NONE)
    | NONE => NONE))
  /\  
 (bigstep_stmt_exec ctx (ascope, g_scope_list, frame_list, status) 0 = SOME (ascope, g_scope_list, frame_list, status, 0))
Termination
WF_REL_TAC `measure ( \ (ctx, (ascope, g_scope_list, frame_list, status), n). n)` >>
gs[is_empty_def] >>
rpt strip_tac >> (
 imp_res_tac bigstep_e_exec_decr >>
 gs[]
)
End

(*
Definition bigstep_frames_exec_comp2_def:
 bigstep_frames_exec_comp2 frame_list' g_scope_list'' v func_map b_func_map g_scope_list ext_map funn' scope_list' ascope' stmt_stack' frame_list'' n' =
            (case frame_list' of
             | [(funn, stmt_stack'', scope_list'')] =>
              (case assign' g_scope_list'' v (lval_varname (varn_star funn)) of
               | SOME g_scope_list''' =>
                (case scopes_to_retrieve_exec funn func_map b_func_map g_scope_list g_scope_list''' of
                 | SOME g_scope_list'''' =>
                  (case lookup_funn_sig_body funn func_map b_func_map ext_map of
                   | SOME (stmt'', x_d_l) =>
                    (case scopes_to_pass_exec funn' func_map b_func_map g_scope_list'''' of
                     | SOME g_scope_list''''' =>
                      (case copyout_exec (MAP FST x_d_l) (MAP SND x_d_l) g_scope_list''''' scope_list' scope_list'' of
                       | SOME (g_scope_list'''''', scope_list''') =>
                        (case scopes_to_retrieve_exec funn' func_map b_func_map g_scope_list'''' g_scope_list'''''' of
                         | SOME g_scope_list''''''' =>
                          SOME (ascope', g_scope_list''''''', ((funn', stmt_stack', scope_list''')::frame_list''), status_running, n')
                         | _ => NONE)
                       | _ => NONE)
                     | _ => NONE)
                   | _ => NONE)
                 | _ => NONE)
               | NONE => NONE)
             | _ => NONE)
End
*)

(* TODO: This has recursive calls, so may require induction *)
Theorem bigstep_stmt_exec_decr:
!ctx astate n n' ascope' g_scope_list' frame_list' status'.
bigstep_stmt_exec ctx astate n = SOME (ascope', g_scope_list', frame_list', status', n') ==>
n' <= n
Proof
rpt strip_tac >>
PairCases_on ‘ctx’ >>
PairCases_on ‘astate’ >>
Cases_on ‘n’ >>
Cases_on ‘astate3’ >> Cases_on ‘astate2’ >>
gs[bigstep_stmt_exec_def] >- (
 PairCases_on ‘h’ >>
 Cases_on ‘t’ >> (gs[bigstep_stmt_exec_def]) >>
 Cases_on ‘h1’ >>  Cases_on ‘h2’ >>
 gs[bigstep_stmt_exec_def] >>
 Cases_on ‘h’ >> Cases_on ‘t’ >> Cases_on ‘h2’ >> (
  gs[bigstep_stmt_exec_def]
 )
) >>
cheat
QED

(* TODO: Why can't you pattern match on fuel here? *)
Definition bigstep_frames_exec_def:
 (*****************************************)
 (* Comp2 + Comp1 case of multiple frames *)
 (bigstep_frames_exec (apply_table_f, ext_map, func_map, b_func_map, pars_map, tbl_map) (ascope, g_scope_list, ((funn, stmt_stack, scope_list)::((funn', stmt_stack', scope_list')::frame_list'')), status_running) n =
 if n = 0
 then SOME (ascope, g_scope_list, ((funn, stmt_stack, scope_list)::((funn', stmt_stack', scope_list')::frame_list'')), status_running, 0)
 else
  (case scopes_to_pass_exec funn func_map b_func_map g_scope_list of
   | SOME g_scope_list' =>
    (case map_to_pass funn b_func_map of
     | SOME b_func_map' =>
      (case tbl_to_pass funn b_func_map tbl_map of
       | SOME tbl_map' =>
        (case bigstep_stmt_exec (apply_table_f, ext_map, func_map, b_func_map', pars_map, tbl_map') (ascope, g_scope_list', [(funn, stmt_stack, scope_list)], status_running) n of
         | SOME (ascope', g_scope_list'', frame_list', status', n') =>
          (case status' of
           | status_returnv v =>
            (* Comp2 *)
(*
           bigstep_frames_exec_comp2 frame_list' g_scope_list'' v func_map b_func_map g_scope_list ext_map funn' scope_list' ascope' stmt_stack' frame_list'' n'
*)
            (case frame_list' of
             | [(funn, stmt_stack'', scope_list'')] =>
              (case assign' g_scope_list'' v (lval_varname (varn_star funn)) of
               | SOME g_scope_list''' =>
                (case scopes_to_retrieve_exec funn func_map b_func_map g_scope_list g_scope_list''' of
                 | SOME g_scope_list'''' =>
                  (case lookup_funn_sig_body funn func_map b_func_map ext_map of
                   | SOME (stmt'', x_d_l) =>
                    (case scopes_to_pass_exec funn' func_map b_func_map g_scope_list'''' of
                     | SOME g_scope_list''''' =>
                      (case copyout_exec (MAP FST x_d_l) (MAP SND x_d_l) g_scope_list''''' scope_list' scope_list'' of
                       | SOME (g_scope_list'''''', scope_list''') =>
                        (case scopes_to_retrieve_exec funn' func_map b_func_map g_scope_list'''' g_scope_list'''''' of
                         | SOME g_scope_list''''''' =>
                          SOME (ascope', g_scope_list''''''', ((funn', stmt_stack', scope_list''')::frame_list''), status_running, n')
                         | _ => NONE)
                       | _ => NONE)
                     | _ => NONE)
                   | _ => NONE)
                 | _ => NONE)
               | NONE => NONE)
             | _ => NONE)
           | _ => 
            (* Comp1 *)
            (case scopes_to_retrieve_exec funn func_map b_func_map g_scope_list g_scope_list'' of
             | SOME g_scope_list''' =>
              SOME (ascope', g_scope_list''', frame_list'++((funn', stmt_stack', scope_list')::frame_list''), status', n')
             | _ => NONE))
         | _ => NONE)
       | _ => NONE)
     | _ => NONE)
   | _ => NONE))
  /\
 (*********)
 (* Comp1, remaining cases *)
 (bigstep_frames_exec (apply_table_f, ext_map, func_map, b_func_map, pars_map, tbl_map) (ascope, g_scope_list, [(funn, stmt_stack, scope_list)], status_running) n =
 if n = 0
 then SOME (ascope, g_scope_list, [(funn, stmt_stack, scope_list)], status_running, 0)
 else
  (case scopes_to_pass_exec funn func_map b_func_map g_scope_list of
   | SOME g_scope_list' =>
    (case map_to_pass funn b_func_map of
     | SOME b_func_map' =>
      (case tbl_to_pass funn b_func_map tbl_map of
       | SOME tbl_map' =>
        (case bigstep_stmt_exec (apply_table_f, ext_map, func_map, b_func_map', pars_map, tbl_map') (ascope, g_scope_list', [(funn, stmt_stack, scope_list)], status_running) n of
         | SOME (ascope', g_scope_list'', frame_list', status', n') =>
          (case scopes_to_retrieve_exec funn func_map b_func_map g_scope_list g_scope_list'' of
           | SOME g_scope_list''' =>
            SOME (ascope', g_scope_list''', frame_list', status', n')
           | _ => NONE)
         | _ => NONE)
       | _ => NONE)
     | _ => NONE)
   | _ => NONE))
 /\
 (bigstep_frames_exec _ _ _ = NONE)
End

Theorem bigstep_frames_exec_decr:
!ctx astate n n' ascope' g_scope_list' frame_list' status'.
bigstep_frames_exec ctx astate n = SOME (ascope', g_scope_list', frame_list', status', n') ==>
n' <= n
Proof
rpt strip_tac >>
PairCases_on ‘ctx’ >>
PairCases_on ‘astate’ >>
Cases_on ‘n’ >> Cases_on ‘astate3’ >> Cases_on ‘astate2’ >> (
 gs[bigstep_frames_exec_def]
) >- (
 PairCases_on ‘h’ >>
 Cases_on ‘t’ >> (gs[bigstep_frames_exec_def]) >>
 PairCases_on ‘h’ >>
 gs[bigstep_frames_exec_def]
) >>
PairCases_on ‘h’ >>
Cases_on ‘t’ >> (gs[bigstep_frames_exec_def]) >- (
 gvs[AllCaseEqs()] >>
 metis_tac[bigstep_stmt_exec_decr]
) >>
PairCases_on ‘h’ >>
gvs[bigstep_frames_exec_def, AllCaseEqs()] >> (
 metis_tac[bigstep_stmt_exec_decr]
)
QED

(* This uses top-level constructs and might be more convenient to use *)
Definition bigstep_arch_exec_def:
 (bigstep_arch_exec ((ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map):'a actx) (((i, in_out_list, in_out_list', scope):'a aenv), g_scope_list:g_scope_list, arch_frame_list_regular frame_list, status:status) (SUC n) =
  (case oEL i ab_list of
   | SOME (arch_block_pbl x e_l) =>
    (case ALOOKUP pblock_map x of
     | SOME (pbl_type, x_d_list, b_func_map, decl_list, pars_map, tbl_map) =>
      if state_fin_exec status frame_list
      then
       (case lookup_block_body x b_func_map of
        | SOME stmt =>
         (* TODO: The below LENGTH check is only used for proofs (e.g. soundness proof) *)
         (if LENGTH e_l = LENGTH x_d_list
          then
           (* pbl_ret *)
           (case copyout_pbl (g_scope_list, scope, MAP SND x_d_list, MAP FST x_d_list, set_fin_status pbl_type status) of
            | SOME scope' =>
             (case oLASTN 1 g_scope_list of
              | SOME g_scope_sing =>
               bigstep_arch_exec (ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map)
                ((i+1, in_out_list, in_out_list', scope'), g_scope_sing,
                 arch_frame_list_empty, status_running) n
              | NONE => NONE)
            | _ => NONE)
          else NONE)
        | NONE => NONE)
      else
       (case status of
        | status_trans x' =>
         (* parser_trans *)
         (case pbl_type of
          | pbl_type_parser =>
           (case ALOOKUP pars_map x' of
            | SOME stmt' =>
             bigstep_arch_exec (ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map)
              ((i, in_out_list, in_out_list', scope), g_scope_list, (arch_frame_list_regular [(funn_name x', [stmt'], [ [] ])]), status_running) n
            | _ => NONE)
          | _ => NONE)
        | status_running =>
         (* pbl_exec *)
         (case bigstep_frames_exec (apply_table_f, ext_map, func_map, b_func_map, pars_map, tbl_map) (scope, g_scope_list, frame_list, status) (SUC n) of
          | SOME (scope', g_scope_list', frame_list', status', n') =>
           if n' = 0 \/ n' > (SUC n)
           then SOME ((i, in_out_list, in_out_list', scope'), g_scope_list', arch_frame_list_regular frame_list', status', 0)
           else
            bigstep_arch_exec (ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map)
             ((i, in_out_list, in_out_list', scope'), g_scope_list', (arch_frame_list_regular frame_list'), status') (n'-1)
          | _ => NONE)
        | _ => NONE)
     | _ => NONE)
   | _ => NONE)
 )
 /\
 (bigstep_arch_exec (ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map)
            ((i, in_out_list, in_out_list', scope), g_scope_list,
             arch_frame_list_empty, status_running) (SUC n) =
  (case oEL i ab_list of
   (* in *)
   | SOME arch_block_inp =>
    (case input_f (in_out_list, scope) of
     | SOME (in_out_list'', scope') =>
      bigstep_arch_exec (ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map)
       ((i+1, in_out_list'', in_out_list', scope'), g_scope_list, arch_frame_list_empty, status_running) n
     | NONE => NONE)
   | SOME (arch_block_pbl x e_l) =>
    (case ALOOKUP pblock_map x of
     (* pbl_init *)
     | SOME (pbl_type, x_d_list, b_func_map, decl_list, pars_map, tbl_map) =>
      (case lookup_block_body x b_func_map of
       | SOME stmt =>
        (* TODO: The below LENGTH check is only used for proofs (e.g. soundness proof) *)
        (if LENGTH e_l = LENGTH x_d_list
         then
          (case copyin_pbl ((MAP FST x_d_list), (MAP SND x_d_list), e_l, scope) of
           | SOME scope' =>
            (case oLASTN 1 g_scope_list of
             | SOME [g_scope] =>
              (* TODO: Use declare_list_in_scope_exec'? *)
              let g_scope_list' = ([declare_list_in_scope (decl_list, scope')]++[g_scope]) in
               (case initialise_var_stars func_map b_func_map ext_map g_scope_list' of
                | SOME g_scope_list'' =>
                 bigstep_arch_exec (ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map)
                  ((i, in_out_list, in_out_list', scope), g_scope_list'',
                       arch_frame_list_regular [(funn_name x, [stmt], [ [] ])], status_running) n
                | NONE => NONE)
             | _ => NONE)
           | _ => NONE)
         else NONE)
       | NONE => NONE)
     | _ => NONE)
   (* ffbl *)
   | SOME (arch_block_ffbl x) =>
    (case ALOOKUP ffblock_map x of
     | SOME (ffblock_ff ff) =>
      (case ff scope of
       | SOME scope' =>
        bigstep_arch_exec (ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map)
         ((i+1, in_out_list, in_out_list', scope'), g_scope_list, arch_frame_list_empty, status_running) n
       | NONE => NONE)
     | NONE => NONE)
   (* out *)
   | SOME arch_block_out =>
    (case output_f (in_out_list', scope) of
     | SOME (in_out_list'', scope') =>
      if NULL in_out_list
      then
       SOME ((0, in_out_list, in_out_list'', scope'), g_scope_list, arch_frame_list_empty, status_running, n)
      else
       bigstep_arch_exec (ab_list, pblock_map, ffblock_map, input_f, output_f, copyin_pbl, copyout_pbl, apply_table_f, ext_map, func_map)
         ((0, in_out_list, in_out_list'', scope'), g_scope_list, arch_frame_list_empty, status_running) n
     | NONE => NONE)
   | _ => NONE)
 ) /\
 (bigstep_arch_exec _ ((i, in_out_list, in_out_list', scope), g_scope_list, arch_frame_list, status) 0 = SOME ((i, in_out_list, in_out_list', scope), g_scope_list, arch_frame_list, status, 0))
Termination
WF_REL_TAC `measure ( \ (actx, astate, n). n)` >>
rpt strip_tac >>
imp_res_tac bigstep_frames_exec_decr >>
gs[]
End

val _ = export_theory ();
