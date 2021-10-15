open HolKernel boolLib Parse bossLib;

val _ = new_theory "p4_e_sem_exec_sketch";

open p4Theory;
open ottTheory;


(* TODO: Move to ottSyntax *)
val (clause_name_tm,  mk_clause_name, dest_clause_name, is_clause_name) =
  syntax_fns1 "ott"  "clause_name";

(* Obtains a list of assumptions for a reduction clause *)
fun get_clause_assums thm =
 (strip_conj o fst o dest_imp o concl o SPEC_ALL) thm
;

(* Finds in a red_rules-theorem exported from ott the rule with name clause_name_str *)
fun find_clause thm clause_name_str =
 let
  val clause_name_str_tm = stringSyntax.fromMLstring clause_name_str
  val conj_thms = CONJUNCTS thm
 in
  List.find (
   (fn assums => isSome (List.find
    (fn tm =>
     if is_clause_name tm
     then term_eq (dest_clause_name tm) clause_name_str_tm
     else false)
    assums)
   ) o get_clause_assums) conj_thms
 end
;
val find_clause_e_red = find_clause e_red_rules

(***************************)

(* NOTE: e_red is a small-step semantics *)

(* First, some kind of executable semantics definition *)
(* No state modification, for now *)
(* TODO: Write explicit NONE-reducing clauses for operands of wrong types?
 *       This would reduce the number of clauses pattern completion needs to add *)
Definition e_exec:
 (e_exec (e_v v) (stacks:stacks) (status:status) =
  SOME (e_v v))
  /\
 (********************)
 (* Unary arithmetic *)
 (e_exec (e_unop unop_neg (e_v (v_bool b))) (stacks:stacks) (status:status) =
  SOME (e_v (v_bool ~b)))
  /\
 (e_exec (e_unop unop_compl (e_v (v_bit bitv))) stacks status =
  SOME (e_v (v_bit (bitv_bl_unop bnot bitv))))
  /\
 (e_exec (e_unop unop_neg_signed (e_v (v_bit bitv))) stacks status =
  SOME (e_v (v_bit (bitv_unop unop_neg_signed bitv))))
  /\
 (e_exec (e_unop unop_un_plus (e_v (v_bit bitv))) stacks status =
  SOME (e_v (v_bit bitv)))
  /\
 (*****************************************)
 (* Argument reduction of unary operation *)
 (e_exec (e_unop unop e) (stacks:stacks) (status:status) =
  case e_exec e stacks status of
  | SOME e' => SOME (e_unop unop e')
  | NONE => NONE)
  /\
 (*********************)
 (* Binary arithmetic *)
 (e_exec (e_binop (e_v (v_bit bitv1)) binop_mul (e_v (v_bit bitv2))) (stacks:stacks) (status:status) =
  case bitv_binop binop_mul bitv1 bitv2 of
  | SOME bitv3 => SOME (e_v (v_bit bitv3))
  | NONE => NONE)
  /\
 (e_exec (e_binop (e_v (v_bit bitv1)) binop_div (e_v (v_bit bitv2))) (stacks:stacks) (status:status) =
  case bitv_binop binop_div bitv1 bitv2 of
  | SOME bitv3 => SOME (e_v (v_bit bitv3))
  | NONE => NONE)
  /\
 (e_exec (e_binop (e_v (v_bit bitv1)) binop_mod (e_v (v_bit bitv2))) (stacks:stacks) (status:status) =
  case bitv_binop binop_mod bitv1 bitv2 of
  | SOME bitv3 => SOME (e_v (v_bit bitv3))
  | NONE => NONE)
  /\
 (e_exec (e_binop (e_v (v_bit bitv1)) binop_add (e_v (v_bit bitv2))) (stacks:stacks) (status:status) =
  case bitv_binop binop_add bitv1 bitv2 of
  | SOME bitv3 => SOME (e_v (v_bit bitv3))
  | NONE => NONE)
  /\
 (e_exec (e_binop (e_v (v_bit bitv1)) binop_sub (e_v (v_bit bitv2))) (stacks:stacks) (status:status) =
  case bitv_binop binop_sub bitv1 bitv2 of
  | SOME bitv3 => SOME (e_v (v_bit bitv3))
  | NONE => NONE)
  /\
 (e_exec (e_binop (e_v (v_bit bitv1)) binop_shl (e_v (v_bit bitv2))) (stacks:stacks) (status:status) =
  SOME (e_v (v_bit (bitv_bl_binop shiftl bitv1 ((\(bl, n). (v2n bl, n)) bitv2)) )))
  /\
 (e_exec (e_binop (e_v (v_bit bitv1)) binop_shr (e_v (v_bit bitv2))) (stacks:stacks) (status:status) =
  SOME (e_v (v_bit (bitv_bl_binop shiftr bitv1 ((\(bl, n). (v2n bl, n)) bitv2)) )))
  /\
 (e_exec (e_binop (e_v (v_bit bitv1)) binop_le (e_v (v_bit bitv2))) (stacks:stacks) (status:status) =
  case bitv_binpred binop_le bitv1 bitv2 of
  | SOME b => SOME (e_v (v_bool b))
  | NONE => NONE)
  /\
 (e_exec (e_binop (e_v (v_bit bitv1)) binop_ge (e_v (v_bit bitv2))) (stacks:stacks) (status:status) =
  case bitv_binpred binop_ge bitv1 bitv2 of
  | SOME b => SOME (e_v (v_bool b))
  | NONE => NONE)
  /\
 (e_exec (e_binop (e_v (v_bit bitv1)) binop_lt (e_v (v_bit bitv2))) (stacks:stacks) (status:status) =
  case bitv_binpred binop_lt bitv1 bitv2 of
  | SOME b => SOME (e_v (v_bool b))
  | NONE => NONE)
  /\
 (e_exec (e_binop (e_v (v_bit bitv1)) binop_gt (e_v (v_bit bitv2))) (stacks:stacks) (status:status) =
  case bitv_binpred binop_gt bitv1 bitv2 of
  | SOME b => SOME (e_v (v_bool b))
  | NONE => NONE)
  /\
 (e_exec (e_binop (e_v (v_bit bitv1)) binop_neq (e_v (v_bit bitv2))) (stacks:stacks) (status:status) = SOME (e_v (v_bool (bitv1 <> bitv2))))
  /\
 (e_exec (e_binop (e_v (v_bit bitv1)) binop_eq (e_v (v_bit bitv2))) (stacks:stacks) (status:status) = SOME (e_v (v_bool (bitv1 = bitv2))))
  /\
 (e_exec (e_binop (e_v (v_bit bitv1)) binop_and (e_v (v_bit bitv2))) (stacks:stacks) (status:status) = SOME (e_v (v_bit (bitv_bl_binop band bitv1 bitv2))))
  /\
 (e_exec (e_binop (e_v (v_bit bitv1)) binop_xor (e_v (v_bit bitv2))) (stacks:stacks) (status:status) = SOME (e_v (v_bit (bitv_bl_binop bxor bitv1 bitv2))))
  /\
 (e_exec (e_binop (e_v (v_bit bitv1)) binop_or (e_v (v_bit bitv2))) (stacks:stacks) (status:status) = SOME (e_v (v_bit (bitv_bl_binop bor bitv1 bitv2))))
  /\
 (e_exec (e_binop (e_v (v_bool F)) binop_bin_and (e_v (v_bool b))) (stacks:stacks) (status:status) = SOME (e_v (v_bool F)))
  /\
 (e_exec (e_binop (e_v (v_bool T)) binop_bin_and (e_v (v_bool b))) (stacks:stacks) (status:status) = SOME (e_v (v_bool b)))
  /\
 (e_exec (e_binop (e_v (v_bool T)) binop_bin_or (e_v (v_bool b))) (stacks:stacks) (status:status) = SOME (e_v (v_bool T)))
  /\
 (e_exec (e_binop (e_v (v_bool F)) binop_bin_or (e_v (v_bool b))) (stacks:stacks) (status:status) = SOME (e_v (v_bool b)))
  /\
 (******************************************)
 (* Argument reduction of binary operation *)
 (e_exec (e_binop (e_v v) binop e1) (stacks:stacks) (status:status) =
  case e_exec e1 stacks status of
  | SOME e2 => SOME (e_binop (e_v v) binop e2)
  | NONE => NONE)
  /\
 (e_exec (e_binop e1 binop e2) (stacks:stacks) (status:status) =
  case e_exec e1 stacks status of
  | SOME e3 => SOME (e_binop e3 binop e2)
  | NONE => NONE)
  /\
 (e_exec _ stacks status = NONE)
End

(* Then, some kind of theorem that states equivalence
 * between executable semantics and ott-exported reduction rules.
 * For sketch, only soundness and not completeness *)
(* TODO: Completeness *)
(* TODO: Only running, for now... *)
Theorem e_exec_subset_red:
 !(e:e) (e':e) stacks.
  e_exec e stacks status_running = SOME e' ==>
  e_red e stacks status_running e' stacks status_running
Proof
(* OLD version:
 Cases_on `e` >> Cases_on `e'` >> (
  fs [e_exec]
 ) >>
 Cases_on `u` >> Cases_on `v` >> (
  fs [e_exec]
 ) >| (map (irule o valOf o find_clause_e_red)
  ["e_neg_bool", "e_compl", "e_neg_signed", "e_un_plus"]
 ) >> (
  fs [clause_name_def]
 )
*)
cheat
QED

(* Then, define an executable semantics which performs execution until finished. *)

Definition e_clos_exec:
 (e_clos_exec (e_v v) (stacks:stacks) (status:status) =
  SOME (e_v v))
  /\
 (********************)
 (* Unary arithmetic *)
 (e_clos_exec (e_unop unop_neg (e_v (v_bool b))) (stacks:stacks) (status:status) =
  SOME (e_v (v_bool ~b)))
  /\
 (e_clos_exec (e_unop unop_compl (e_v (v_bit bitv))) stacks status =
  SOME (e_v (v_bit (bitv_bl_unop bnot bitv))))
  /\
 (e_clos_exec (e_unop unop_neg_signed (e_v (v_bit bitv))) stacks status =
  SOME (e_v (v_bit (bitv_unop unop_neg_signed bitv))))
  /\
 (e_clos_exec (e_unop unop_un_plus (e_v (v_bit bitv))) stacks status =
  SOME (e_v (v_bit bitv)))
  /\
 (*****************************************)
 (* Argument reduction of unary operation *)
 (e_clos_exec (e_unop unop e) (stacks:stacks) (status:status) =
  case e_clos_exec e stacks status of
  | SOME e' => e_exec (e_unop unop e') stacks status
  | NONE => NONE)
  /\
 (e_clos_exec _ stacks status = NONE)
End
        
(* Then, define the closure of the small step reduction. *)

val (e_clos_sem_rules, e_clos_sem_ind, e_clos_sem_cases) = Hol_reln`
(* Base clause: *)
(! (e:e) (stacks:stacks) (e':e) (stacks':stacks).
( ( e_red e stacks status_running e' stacks' status_running )) ==> 
( ( e_clos_red e stacks status_running e' stacks' status_running )))
(* Inductive clause: *)
/\ (! (e:e) (stacks:stacks) (e':e) (stacks':stacks) (e'':e) (stacks'':stacks).
(( ( e_red e stacks status_running e' stacks' status_running )) /\ 
( ( e_clos_red e' stacks' status_running e'' stacks'' status_running ))) ==> 
( ( e_clos_red e stacks status_running e'' stacks'' status_running )))
`;

(* Then, prove that the multi-step executable semantics is sound with respect to the
 * closure of the small-step reduction *)

Theorem e_exec_clos_sound_red:
 !(e:e) (e':e) stacks.
  e_exec_clos e stacks status_running = SOME e' ==>
  e_clos_red e stacks status_running e' stacks status_running
Proof
 cheat
QED

(* Then, some kind of (multi-step) CakeML-adjusted executable semantics definition *)
Definition e_exec_cake:
 (e_exec_cake (e_unop unop_neg (e_v (v_bool b))) (stacks:stacks) (status:status) =
   SOME (e_v (v_bool ~b)))
  /\
 (e_exec_cake (e_unop unop_compl (e_v (v_bit bitv))) stacks status =
  SOME (e_v (v_bit (bitv_bl_unop bnot bitv))))
  /\
 (e_exec_cake (e_unop unop_neg_signed (e_v (v_bit bitv))) stacks status =
  SOME (e_v (v_bit (bitv_unop unop_neg_signed bitv))))
  /\
 (e_exec_cake (e_unop unop_un_plus (e_v (v_bit bitv))) stacks status =
  SOME (e_v (v_bit bitv)))
  /\
 (e_exec_cake _ stacks status = NONE)
End

(* TODO: At this point, expect to translate lists to lists and fmaps to mlmaps *)
Theorem sem_expr_exe_cake_eq:
 !e stacks.
  e_exec_cake e stacks status_running = e_exec_clos e stacks status_running
Proof
 cheat
QED

val _ = export_theory ();
