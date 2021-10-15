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

(* Rough sketch of executable semantics plan *)

(* First, some kind of executable semantics definition *)
(* No state modification, for now *)
(* TODO: Write explicit NONE-reducing clauses for operands of wrong types? *)
Definition e_exec:
  (* Concrete unary operations *)
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
 (* Argument reduction of unary operation *)
 (e_exec (e_unop unop e) (stacks:stacks) (status:status) =
  case e_exec e stacks status of
  | SOME e' => SOME (e_unop unop e')
  | NONE => NONE)
  /\
(* TODO: Concrete binary operations

*)
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
QED

(* Then, some kind of CakeML-adjusted executable semantics definition *)
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
  e_exec_cake e stacks status_running = e_exec e stacks status_running
Proof
 cheat
QED

val _ = export_theory ();
