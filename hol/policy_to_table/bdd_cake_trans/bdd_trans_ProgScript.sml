open HolKernel Parse boolLib bossLib;
open optionTheory pairTheory bdd_genTheory policy_specTheory pred_specTheory;     
open preamble basis ml_translatorLib ;

open miscTheory ml_translatorTheory ListProgTheory ;

(*
open ListProgTheory SetProgTheory;

open ml_progLib basisProgTheory mlmapTheory basisFunctionsLib
     astPP comparisonTheory;
*)


     
val _ = new_theory "bdd_trans_Prog";


val _ = intLib.deprecate_int();



        
val r = translate listTheory.MAP;
val r = translate update_internals_def;
val r = translate distrubute_labels_def;
val r = translate bdd_distribute_def;

val r = translate THE_DEF;

(*
r |> hyp |> null
rw [fetch "-" "EqualityType_def"]
*)
    
val r = translate ALOOKUP_def;
val r = translate project_labels_to_def;

val r = translate pairTheory.FST;
val r = translate pairTheory.SND;
val r = translate listTheory.EXISTS_DEF;
val r = translate has_parent_def;
val r = translate eliminable_def;


val r = translate FILTER;
val r = translate ADELKEY_def;
val r = translate merge_edges_def;
val r = translate merge_def;
val r = translate eliminate_safe_def;

val r = translate eliminable_projection_def;
val r = translate eq_vars_in_labels_def;
val r = translate mergable_projection_def;

val r = translate mergable_def;
val r = translate merge_safe_def;
    
val r = translate optimize_node_def;
val r = translate optimize_layer_def;

    
val r = translate project_edges_to_def;
val r = translate optimize_internals_def;

val r = translate optimize_bdd_def;

Theorem optimize_bdd_side_cake_trans:
  optimize_bdd_side v10 v11
Proof
   cheat
QED

val _ = optimize_bdd_side_cake_trans |> update_precondition;
 

(* body_of_mk part*)

val r = translate MEMBER_def;
val r = translate (MEM |> REWRITE_RULE [MEMBER_INTRO]);
val r = translate (nub_def |> REWRITE_RULE [MEMBER_INTRO]);
val r = translate boolTheory.IN_DEF;    
val r = translate FLAT;
val r = translate (get_leaves_list_def |> REWRITE_RULE [MEMBER_INTRO]);
val r = translate getLeaves_def;

val r = translate getLabels_def;
val r = translate extract_nontermn_def;
val r = translate leaves_pred_sub_def;
val r = translate simp_pred_list_def;
val r = translate determine_termn_def;
val r = translate determine_termn_list_def;
val r = translate mk_new_labels_def;
val r = translate mk_new_edges_def;
val r = translate non_term_leaf_updt_def;
val r = translate LENGTH;

val r = translate body_of_mk_def;
val r = translate mk_BDDPred_opt_def;


(* translation of policy structure and related functions*)

val r = translate INDEX_FIND_def;  
val r = translate min_idx_till_def;
val r = translate sem_pred_def;
val r = translate check_sem_pred_def;
val r = translate sem_policy_def;

val r = translate mk_substitute_pred_def;
val r = translate mk_substitute_policy_def;

val r = translate simp_pred_def;
val r = translate simp_policy_def;

val r = translate listTheory.EVERY_DEF;
val r = translate rich_listTheory.SEG;
val r = translate pre_are_fail_def;
val r = translate final_policy_def;


val r = translate fv_pred_def;
val r = translate fv_policy_def;


Theorem final_policy_cake_trans:
  final_policy_side v4
Proof
  rw [fetch "-" "final_policy_side_def"] >>
  rw [fetch "-" "pre_are_fail_side_def"] >>
  rw [Once (fetch "-" "seg_side_def")] >>
  fs[min_idx_till_def] >> cheat
QED

val _ = final_policy_cake_trans |> update_precondition;

    
val r = ml_translatorLib.register_type ``:((pred # 'a) list, 'b) decision_structure``;
val r = translate policy_structure_def;

  
val _ = type_abbrev("action_policy_type", “:((string# num list) action_expr) policy”);

    
Definition mk_BDD_policy_def:
  mk_BDD_policy (var_policy: action_policy_type ) policy_order =
  mk_BDDPred_opt policy_structure (0,[],[(0, non_termn (NONE, var_policy))]) [] policy_order 1n
End


val r = translate mk_BDD_policy_def;
                           

(************* pass arguments this way *****************)

Definition policy_order_test_def:
 policy_order_test = ["x"; "y"]
End

val r = translate policy_order_test_def;

Definition policy_content_test_def:
  policy_content_test =
  [
    (Var "x" , action ("fwd", [1n]));
    (Var "y" , action ("fwd", [2n]))
  ]:action_policy_type
End

val r = translate policy_content_test_def;

        
                           
Definition main_test_def:
  main_test =
  mk_BDD_policy policy_content_test  policy_order_test
End

val r = translate main_test_def;

        
(***************************************)
                                    
(*
val _ = r |> hyp |> null orelse
        failwith ("Unproved side condition in the translation of \
                  \dafny_compilerTheory.main_function_def");
*)
    

(*    
val state = get_ml_prog_state();
(* returns the type ml_progLib.ml_prog_state*)

val prog_tm = ml_progLib.get_prog (ml_progLib.remove_snocs(ml_progLib.clean_state(state)));
(* returns type term*)

val bdd_prog_def = Define ‘out_prog = ^prog_tm’ ;  
val base_compiled = save_thm("out_compiled", ml_progLib.compile_x64 "out" bdd_prog_def);    
*)



(*
val Decls_thm =
  get_ml_prog_state ()
  |> ml_progLib.clean_state
  |> ml_progLib.remove_snocs
  |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def,ml_progTheory.ML_code_env_def];

Theorem evaluate_prog_thm =
  Decls_thm |> REWRITE_RULE [ml_progTheory.Decls_def]



val env = get_ml_prog_state() |> ml_progLib.get_env
val st = get_ml_prog_state () |> ml_progLib.get_state                                               
ml_progLib.get_Decls_thm (get_ml_prog_state())
*)


(* to get an sexp file*)
open fromSexpTheory; 

val state = get_ml_prog_state();
val prog_tm = ml_progLib.get_prog (ml_progLib.remove_snocs(ml_progLib.clean_state(state)));


val _ = astToSexprLib.write_ast_to_file "test_new.sexp" prog_tm;



    
(****************************************************)


  (*  (* to pretty print*)
val current_prog =
Decls_thm |> concl |> strip_comb |> #2 |> el 3

val _ = astPP.enable_astPP ();
print_term (current_prog);
val _ = astPP.disable_astPP();
*)


(*
(* to get the binary *)
open eval_cake_compile_x64Lib;
(*val state = get_ml_prog_state();
val prog_tm = ml_progLib.get_prog (ml_progLib.remove_snocs(ml_progLib.clean_state(state))); *)
val bdd_prog_def = Define ‘out_prog = ^prog_tm’ ;  

Theorem blah_compiled =
  eval_cake_compile_x64 "" bdd_prog_def "bew_bdd.S";
*)


(*
val Decls_thm =
  get_ml_prog_state ()
  |> ml_progLib.clean_state
  |> ml_progLib.remove_snocs
  |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def,ml_progTheory.ML_code_env_def];

(* the mk_BDD_policy program successfully evaluates to an env, called auto_env3 *)
Theorem evaluate_prog_thm =
  Decls_thm |> REWRITE_RULE [ml_progTheory.Decls_def]

(* looking up "mk_BDD_policy" in this env finds the qsort value (bdd_distribute_v) *)
Theorem lookup_mk_BDD_policy =
  EVAL ``nsLookup  ^(concl Decls_thm |> rator |> rand).v (Short "bdd_distribute")``

*)




(*
val r = ml_translatorLib.register_type ``: 'a option``;

val r = translate (INST_TYPE [“:'a” |-> “:num”] INDEX_FIND_def);

Definition number_list_test_def:
   number_list_test = [5n;0]
End

val r = translate number_list_test_def;
    

Definition main_hol4_def:
  main_hol4 =
  INDEX_FIND 0 (\n . n = 0)  number_list_test
End

val r = translate main_hol4_def; 
*)
    
                                                
        
(*

val res = append_prog o process_topdecs $ `
fun main () =
let
val args = CommandLine.arguments()
in
TextIO.print "finallllllllllllyy"
end;
 `;



val prog =
  ``SNOC
    (Dlet unknown_loc (Pcon NONE [])
      (App Opapp [Var (Short "main"); Con NONE []]))
    ^(get_ml_prog_state() |> get_prog)
  `` |> EVAL |> concl |> rhs


val _ = astToSexprLib.write_ast_to_file "revProg.sexp" prog;

 *)

      

val _ = export_theory();


