open HolKernel boolLib liteLib simpLib Parse bossLib;

val _ = new_theory "imp";

open listTheory alistTheory stringTheory;

(*************************)
(* Auxiliary definitions *)

Definition AUPDATE_def:
 AUPDATE alist (k,v) =
  case ALOOKUP alist k of
     SOME _ => AFUPDKEY k (\old_v. v) alist
   | NONE => (alist++[(k,v)])
End

Definition AUPDATE_LIST_def:
 AUPDATE_LIST = FOLDL AUPDATE
End

(****************)
(* IMP language *)

Datatype:
v = (* value *)
   v_bool bool (* Boolean *)
 | v_num num (* natural number, possibly zero *)
End

Datatype:
bop = (* binary operation *)
   bop_mul (* multiplication *)
 | bop_div (* (integer) division *)
 | bop_mod (* modulo *)
 | bop_add (* addition *)
 | bop_sub (* (saturated) subtraction *)
 | bop_lt (* less than *)
 | bop_eq (* equal *)
 | bop_and (* and *)
 | bop_or (* or *)
End

Datatype:
uop = (* binary operation *)
 uop_neg (* negation *)
End

Datatype:
e =  (* expression *)
   e_v v (* value *)
 | e_var string (* variable *)
 | e_uop uop e (* unary operation *)
 | e_bop e bop e (* binary operation *)
End

Datatype:
tau =  (* type *)
   tau_bool (* boolean *)
 | tau_num (* number *)
End

(* TODO: Should language have declare, block or only assign? *)
Datatype:
stmt =  (* statement *)
   stmt_empty (* empty statement *)
 | stmt_ass string e (* assignment *)
 | stmt_cond e stmt stmt (* conditional *)
 | stmt_while e stmt (* loop *)
 | stmt_seq stmt stmt (* sequence *)
End

val _ = type_abbrev("imp_store", ``:((string, v) alist)``);

Definition v_exec_uop_def:
 (v_exec_uop uop_neg (v_bool b) = SOME (v_bool ~b))
 /\
 (v_exec_uop uop v = NONE)
End

Definition v_exec_bop_def:
 (v_exec_bop bop_mul (v_num n1) (v_num n2) =
  SOME (v_num (n1 * n2)))
 /\
 (v_exec_bop bop_div (v_num n1) (v_num n2) =
  SOME (v_num (n1 DIV n2)))
 /\
 (v_exec_bop bop_mod (v_num n1) (v_num n2) =
  SOME (v_num (n1 MOD n2)))
 /\
 (v_exec_bop bop_add (v_num n1) (v_num n2) =
  SOME (v_num (n1 + n2)))
 /\
 (v_exec_bop bop_sub (v_num n1) (v_num n2) =
  SOME (v_num (n1 - n2)))
 /\
 (v_exec_bop bop_lt (v_num n1) (v_num n2) =
  SOME (v_bool (n1 < n2)))
 /\
 (v_exec_bop bop_eq (v_num n1) (v_num n2) =
  SOME (v_bool (n1 = n2)))
 /\
 (v_exec_bop bop_eq (v_bool b1) (v_bool b2) =
  SOME (v_bool (b1 = b2)))
 /\
 (v_exec_bop bop_and (v_bool b1) (v_bool b2) =
  SOME (v_bool (b1 /\ b2)))
 /\
 (v_exec_bop bop_or (v_bool b1) (v_bool b2) =
  SOME (v_bool (b1 \/ b2)))
 /\
 (v_exec_bop bop v1 v2 = NONE)
End

Definition e_exec_def:
 (e_exec (st:imp_store) (e_var x) =
  case ALOOKUP st x of
    SOME v => SOME (e_v v)
  | NONE => NONE)
  /\
 (e_exec st (e_uop uop e) =
  case e of
    e_v v =>
   (case v_exec_uop uop v of
      SOME v' => SOME (e_v v')
    | NONE => NONE)
  | _ =>
   (case e_exec st e of
      SOME e' => SOME (e_uop uop e')
    | NONE => NONE))
  /\
 (e_exec st (e_bop e1 bop e2) =
  (case e1 of
     (e_v v1) =>
    (case e2 of
       (e_v v2) =>
      (case v_exec_bop bop v1 v2 of
         SOME v' => SOME (e_v v')
       | NONE => NONE)
     | _ =>
      (case e_exec st e2 of
         SOME e2' => SOME (e_bop e1 bop e2')
       | NONE => NONE))
   | _ =>
    (case e_exec st e1 of
       SOME e1' => SOME (e_bop e1' bop e2)
     | NONE => NONE)))
  /\
 (e_exec _ _ = NONE)
End

Definition get_v_def:
 get_v e =
  case e of
    e_v v => SOME v
  | _ => NONE
End

Definition get_v_bool_def:
 get_v_bool e =
  case get_v e of
    SOME v =>
   (case v of
      v_bool b => SOME b
    | _ => NONE)
  | NONE => NONE
End

Definition stmt_exec_ass_def:
 stmt_exec_ass varname v st =
  AUPDATE st (varname, v)
End

Definition stmt_exec_def:
 (* Assignment *)
 (stmt_exec st (stmt_ass varname e) =
  case get_v e of
    SOME v =>
   SOME (stmt_exec_ass varname v st, stmt_empty)
  | NONE =>
   (case e_exec st e of
      SOME e' =>
     SOME (st, stmt_ass varname e')
    | _ => NONE))
  /\
 (* Conditional *)
 (stmt_exec st (stmt_cond e stmt1 stmt2) =
  case get_v_bool e of
    SOME b =>
   (if b
    then SOME (st, stmt1)
    else SOME (st, stmt2))
  | NONE =>
   (case e_exec st e of
      SOME e' =>
     SOME (st, stmt_cond e' stmt1 stmt2)
    | NONE => NONE))
  /\
 (* While *)
 (stmt_exec st (stmt_while e stmt) =
  SOME (st, stmt_cond e (stmt_seq stmt (stmt_while e stmt)) stmt_empty))
  /\
 (* Sequence *)
 (stmt_exec st (stmt_seq stmt1 stmt2) =
  case stmt1 of
    stmt_empty =>
   SOME (st, stmt2)
  | _ =>
   (case stmt_exec st stmt1 of
      SOME (st', stmt1') =>
       SOME (st', stmt_seq stmt1' stmt2)
    | _ => NONE))
  /\
 (stmt_exec _ _ = NONE)
End

Definition stmt_multi_exec_def:
 (stmt_multi_exec (st, stmt) 0 =
  SOME (st, stmt))
  /\
 (stmt_multi_exec (st, stmt) (SUC fuel) =
  case stmt_exec st stmt of
    SOME (st', stmt') =>
   stmt_multi_exec (st', stmt') fuel
  | NONE => NONE)
End

(******************************************)
(* Symbolic execution function parameters *)

open symb_execTheory;

(** imp_is_finished **)

val stmt_empty_tm = prim_mk_const {Name="stmt_empty", Thy="imp"};
fun is_stmt_empty tm = term_eq tm stmt_empty_tm;

(* From p4_testLib.sml, should be moved to symbexec library? *)
fun the_final_state_imp step_thm =
 optionSyntax.dest_some $ snd $ dest_eq $ snd $ dest_imp $ concl step_thm;

fun imp_is_finished step_thm =
 let
  val state = the_final_state_imp step_thm
  val (store, statement) = pairSyntax.dest_pair state
 in
  is_stmt_empty statement
 end
;


(** imp_regular_step **)

val (stmt_multi_exec_tm, _, dest_stmt_multi_exec, is_stmt_multi_exec) =
  syntax_fns2 "imp" "stmt_multi_exec";
val mk_stmt_multi_exec =
 (fn (state, fuel) => (#2 (syntax_fns2 "imp" "stmt_multi_exec")) (state, numSyntax.term_of_int fuel));

(* From p4_testLib.sml, should be moved to symbexec library? *)
fun the_final_state_hyp_imp step_thm =
 let
  val (hyp, step_tm) = dest_imp $ concl step_thm
 in
  (hyp, optionSyntax.dest_some $ snd $ dest_eq step_tm)
 end
;

fun mk_exec n = (fn state => mk_stmt_multi_exec (state, n));

(* TODO: Test freezing compset *)
fun imp_norewr_eval_ctxt st = EVAL (mk_exec 1 st);

open evalwrapLib;

fun imp_eval_ctxt path_cond state =
 eval_ctxt_gen [] [] (ASSUME path_cond) (mk_exec 1 state)
;

(* TODO: Put in generic symb_execLib? *)
val simple_arith_ss = pure_ss++numSimps.REDUCE_ss;

Theorem stmt_multi_exec_add:
!st stmt m n.
stmt_multi_exec (st, stmt) (m+n) =
 case stmt_multi_exec (st, stmt) n of
 | SOME (st', stmt') =>
  stmt_multi_exec (st', stmt') m
 | NONE => NONE
Proof
Induct_on `n` >- (
 fs [stmt_multi_exec_def]
) >>
rpt strip_tac >>
fs [stmt_multi_exec_def, arithmeticTheory.ADD_CLAUSES] >>
Cases_on `stmt_exec st stmt` >> (
 fs []
) >>
PairCases_on `x` >>
fs []
QED

Theorem stmt_multi_exec_comp_n_tl_assl:
!n m assl st stmt st' stmt' st'' stmt''.
(assl ==> stmt_multi_exec (st, stmt) n = SOME (st', stmt')) ==>
(assl ==> stmt_multi_exec (st', stmt') m = SOME (st'', stmt'')) ==>
(assl ==> stmt_multi_exec (st, stmt) (n+m) = SOME (st'', stmt''))
Proof
rpt strip_tac >>
gs [] >>
fs [stmt_multi_exec_add]
QED

Theorem stmt_multi_exec_comp_n_tl_assl_conj:
!n m assl st stmt st' stmt' st'' stmt''.
((assl ==> stmt_multi_exec (st, stmt) n = SOME (st', stmt')) /\
 (assl ==> stmt_multi_exec (st', stmt') m = SOME (st'', stmt''))) ==>
(assl ==> stmt_multi_exec (st, stmt) (n+m) = SOME (st'', stmt''))
Proof
metis_tac[stmt_multi_exec_comp_n_tl_assl]
QED

Theorem stmt_multi_exec_comp_n_tl_assl_conj_nomidassl:
!n m assl st stmt st' stmt' st'' stmt''.
((assl ==> stmt_multi_exec (st, stmt) n = SOME (st', stmt')) /\
 (stmt_multi_exec (st', stmt') m = SOME (st'', stmt''))) ==>
(assl ==> stmt_multi_exec (st, stmt) (n+m) = SOME (st'', stmt''))
Proof
metis_tac[stmt_multi_exec_comp_n_tl_assl_conj]
QED

fun imp_regular_step branch_just_happened step_thm =
 let
  val (ante, st) = the_final_state_hyp_imp step_thm
  val step_thm2 =
   if branch_just_happened
   then imp_eval_ctxt ante st
   else imp_norewr_eval_ctxt st
 in
  let
   val res =
    SIMP_RULE simple_arith_ss []
     (if branch_just_happened
      then
       (MATCH_MP stmt_multi_exec_comp_n_tl_assl_conj (CONJ step_thm step_thm2))
      else
       (MATCH_MP stmt_multi_exec_comp_n_tl_assl_conj_nomidassl (CONJ step_thm step_thm2)))
  in
   res
  end
 end
;


(** imp_should_branch **)

val (stmt_cond_tm, mk_stmt_cond, dest_stmt_cond, is_stmt_cond) =
  syntax_fns3 "imp"  "stmt_cond";
val (stmt_seq_tm, mk_stmt_seq, dest_stmt_seq, is_stmt_seq) =
  syntax_fns2 "imp"  "stmt_seq";
val (e_v_tm,  mk_e_v, dest_e_v, is_e_v) =
  syntax_fns1 "imp" "e_v";
val (v_bool_tm, mk_v_bool, dest_v_bool, is_v_bool) =
  syntax_fns1 "imp" "v_bool";

fun stmt_get_next stmt =
 if is_stmt_seq stmt
 then stmt_get_next $ fst $ dest_stmt_seq stmt
 else stmt
;

datatype branch_data =
   no_branch
 | conditional of term;

fun state_get_branch_data state =
  let
   val (store, stmt) = pairSyntax.dest_pair state
   val stmt' = stmt_get_next stmt
  in
   if is_stmt_cond stmt'
   then conditional $ #1 $ dest_stmt_cond stmt'
   else no_branch
  end
;

fun imp_should_branch (fv_index:int, step_thm) =
 let
  val (_, state) = the_final_state_hyp_imp step_thm
  val res =
  (*
   val conditional branch_cond = it
  *)
   (case state_get_branch_data state of
    conditional branch_cond =>
   if is_e_v branch_cond andalso not $ null $ free_vars branch_cond
   then
    let
     val branch_cond' = dest_v_bool $ dest_e_v branch_cond
    in
     SOME (SPEC branch_cond' disj_list_EXCLUDED_MIDDLE, [fv_index, fv_index])
    end
   else NONE
  | no_branch => NONE)
 in
  res
 end
;


fun get_init_step_thm path_cond init_st init_stmt =
 (eval_ctxt_gen [] [] (ASSUME path_cond) (mk_exec 0 “(^init_st, ^init_stmt)”))
;

(*************************************************************)
(* AbsMinus (toy example adapted from Gordon and Collavizza)
 * https://hal.science/hal-03015714/document *)

val toy_program = “stmt_seq (stmt_ass "k" (e_v $ v_num 0))
                   (stmt_seq (stmt_cond (e_uop uop_neg (e_bop (e_var "j") bop_lt (e_var "i"))) (stmt_ass "k" (e_bop (e_var "k") bop_add (e_v $ v_num 1))) stmt_empty)
                   (stmt_cond (e_bop (e_bop (e_var "k") bop_eq (e_v $ v_num 1)) bop_and (e_uop uop_neg $ e_bop (e_var "i") bop_eq (e_var "j")))
                              (stmt_ass "result" (e_bop (e_var "j") bop_sub (e_var "i")))
                              (stmt_ass "result" (e_bop (e_var "i") bop_sub (e_var "j")))))”
val toy_init_state = “[("i", v_num i); ("j", v_num j); ("Result", v_num Result); ("result", v_num result)]”

val toy_loop = “stmt_while (e_bop (e_var "a") bop_lt (e_var "b"))
                           (stmt_ass "a" (e_bop (e_var "a") bop_add (e_v $ v_num 1)))”

(*****************)
(* Performing symbolic execution *)
val init_step_thm = get_init_step_thm T toy_init_state toy_program
val debug_flag = true
val path_cond = ASSUME T
val fuel = 50

open symb_execLib;

val (res_path_tree, path_cond_step_list) = symb_exec (debug_flag, imp_regular_step, init_step_thm, imp_should_branch, imp_is_finished) path_cond fuel


(* Proving the postcondition *)
val postcond =
 “\s:(string # imp$v) list # imp$stmt. (i < j ==> ALOOKUP (FST s) "result" = SOME (v_num (j - i))) /\
      (i >= j ==> ALOOKUP (FST s) "result" = SOME (v_num (i - j)))”

fun prove_postcond postcond step_thm =
 let
  val prel_res_thm = HO_MATCH_MP symb_exec_add_postcond step_thm
  val (hypo, step_tm) = dest_imp $ concl step_thm
  val res_state_tm = optionSyntax.dest_some $ snd $ dest_eq step_tm
  val postcond_thm = EQT_ELIM $ (computeLib.EVAL_CONV THENC (SIMP_CONV (srw_ss()) []) THENC numLib.ARITH_CONV) $ mk_imp (hypo, mk_comb (postcond, res_state_tm))
 in
  MATCH_MP prel_res_thm postcond_thm
 end
;

fun prove_postconds_debug' postcond []     _ = []
  | prove_postconds_debug' postcond (h::t) n =
 let
  val res = prove_postcond postcond h
   handle exc => (print (("Error when proving postcondition for n-step theorem at 0-index "^(Int.toString n))^"\n"); raise exc)
 in
  (res::(prove_postconds_debug' postcond t (n + 1)))
 end
;
fun prove_postconds debug_flag postcond path_cond_step_list =
 if debug_flag
 then
  let
   val (l', l'') = unzip $ map (fn (a,b,c) => (a, c)) path_cond_step_list
  in
   zip l' (prove_postconds_debug' postcond l'' 0)
  end
 else map (fn (a,b,c) => (a, prove_postcond postcond c)) path_cond_step_list
;

prove_postconds debug_flag postcond path_cond_step_list;

val _ = export_theory();
