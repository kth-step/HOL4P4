open HolKernel boolLib liteLib simpLib Parse bossLib;
open arithmeticTheory stringTheory containerTheory pred_setTheory
     listTheory finite_mapTheory;
open bitstringTheory;
open wordsTheory;
open optionTheory;
open sumTheory;
open ottTheory;
open pairTheory;
open rich_listTheory;
open alistTheory;
open numeralTheory;
open set_relationTheory;
open pred_setLib;

open p4_auxTheory;
open bdd_genTheory;
open bdd_gen_newTheory;
open numeralTheory;
open alistTheory;


open pred_specTheory;


open bdd_genTheory;
open policy_arith_to_varTheory;

open bdd_utilsLib;
open fwd_proofLib;   


val _ = new_theory "profiling";

(*

        fun take_first_three tuple_term =
    let val (a, bc_d) = pairSyntax.dest_pair tuple_term
        val (b, c_d) = pairSyntax.dest_pair bc_d
        val (c, _) = pairSyntax.dest_pair c_d
    in pairSyntax.mk_pair (a, pairSyntax.mk_pair (b, c)) end;

                          

fun take_fourth tuple_term =
    let val (a, bc_d) = pairSyntax.dest_pair tuple_term
        val (b, c_d) = pairSyntax.dest_pair bc_d
        val (c, d) = pairSyntax.dest_pair c_d
    in d end;


         
fun bdd_mini_components thm =
    let val tuple_term = optionSyntax.dest_some (rhs (concl thm))
    in take_first_three tuple_term end;

fun bdd_content_components thm =
    let val tuple_term = optionSyntax.dest_some (rhs (concl thm))
    in take_fourth tuple_term end;


    
fun add_fourth_component triple_term fourth_component =
    let val (a, b_c) = pairSyntax.dest_pair triple_term
        val (b, c) = pairSyntax.dest_pair b_c
    in
        pairSyntax.mk_pair (a, 
            pairSyntax.mk_pair (b, 
                pairSyntax.mk_pair (c, fourth_component)))
    end;


val eval_table_full_layer1 = time EVAL
      “mk_BDDPred_new pred_structure (0n,[],[(0n, id_non_termn (NONE), 0n)], [(0n, Var "x")]) [] ["x"] 1n”;
val eval_table_full_layer1_rhs = bdd_mini_components eval_table_full_layer1;
val eval_table_full_layer1_rhs_fourth = bdd_content_components eval_table_full_layer1;

val eval_table_full_opt_layer1 = EVAL
      “ optimize_bdd_new ^eval_table_full_layer1_rhs ^policy_order”;
val eval_table_full_opt_layer1_rhs = add_fourth_component (rhs (concl eval_table_full_opt_layer1)) eval_table_full_layer1_rhs_fourth;



val eval_policy_full_opt = EVAL “mk_BDDPred_opt policy_structure (0,[],[(0, non_termn (NONE, ^var_policy))]) [] ^policy_order 1”;
val eval_policy_full_opt_rhs = optionSyntax.dest_some (rhs (concl eval_policy_full_opt));
    



val eval_policy_full_opt = EVAL “mk_BDDPred_opt_new policy_structure (0n,[],[(0n, id_non_termn NONE, 0n)], [0n, ^var_policy]) [] ^policy_order 1n”;
val eval_policy_full_opt_rhs = optionSyntax.dest_some (rhs (concl eval_policy_full_opt));
    
mk_BDDPred_opt_new_def


    
  *)  




    
fun mk_BDDPred_opt_new_sml rec_flag bdd_sep l xs c =
    case xs of
        [] => SOME bdd_sep
      | x::xs' =>
            let
                val result_thm = EVAL ``body_of_mk_new ^rec_flag ^bdd_sep ^x ^c``
                val result_term = rhs (concl result_thm)
            in
                if optionSyntax.is_none result_term then
                    NONE
                else
                    let
                        (* Extract the components step by step with debugging *)
                        val the_content = optionSyntax.dest_some result_term
                        val (bdd_quad, c') = pairSyntax.dest_pair the_content
                        
                        (* bdd_quad should be: (r, edges, labels_id, labels_content) *)
                        val (r, rest1) = pairSyntax.dest_pair bdd_quad
                        val (edges, rest2) = pairSyntax.dest_pair rest1  
                        val (labels_id, labels_content) = pairSyntax.dest_pair rest2
                        
                        val optimize_input = pairSyntax.mk_pair(r, 
                                            pairSyntax.mk_pair(edges, labels_id))
                        
                        val var_list_term = listSyntax.mk_list(x::l, ``:string``)                        
                        val optimized_thm = EVAL ``optimize_bdd_new ^optimize_input ^var_list_term``
                        val optimized_result = rhs (concl optimized_thm )
                        (*val _ = print ("Optimized result: " ^ term_to_string optimized_result ^ "\n") *)
                        
                        (* Extract from the optimized triple *)
                        val (r', opt_rest1) = pairSyntax.dest_pair optimized_result
                        val (edges', labels_id') = pairSyntax.dest_pair opt_rest1
                        
                        (* Build new quadruple *)
                        val new_bdd_sep = pairSyntax.mk_pair(r',
                                        pairSyntax.mk_pair(edges',
                                        pairSyntax.mk_pair(labels_id', labels_content)))
                    in
                        mk_BDDPred_opt_new_sml rec_flag new_bdd_sep (x::l) xs' c'
                    end
            end

(*
val result = mk_BDDPred_opt_new_sml “pred_structure”
                               “(0n,[]:edges,[(0n, id_non_termn NONE, 0n)] : (bool label_id), [0n, And (Var "x") (Var "y")])”
                               [] [“"x"”, “"y"”] “1n”



EVAL “mk_BDDPred_opt_new pred_structure (0n,[]:edges,[(0n, id_non_termn NONE, 0n)] : (bool label_id), [0n, And (Var "x") (Var "y")]) [] ["x"; "y"] 1n”
*)



fun mk_BDDPred_opt_new_thm rec_flag bdd_sep xs =
    let
        val result = mk_BDDPred_opt_new_sml rec_flag bdd_sep [] xs “1n”
        val l_term = listSyntax.mk_list([], ``:string``)
        val xs_term = listSyntax.mk_list(xs, ``:string``)
    in
        case result of
            NONE => mk_thm([], ``mk_BDDPred_opt_new ^rec_flag ^bdd_sep ^l_term ^xs_term 1n = NONE``)
          | SOME res => mk_thm([], ``mk_BDDPred_opt_new ^rec_flag ^bdd_sep ^l_term ^xs_term 1n = SOME ^res``)
    end;



(*
val a = mk_BDDPred_opt_new_thm “pred_structure”
                               “(0n,[]:edges,[(0n, id_non_termn NONE, 0n)] : (bool label_id), [0n, And (Var "x") (Var "y")])”
                               [“"x"”, “"y"”] 
*)

val rec_flag = ``policy_structure : ((pred # (string # num list) action_expr) list, (string # num list) action_expr) decision_structure``
val rec_flag_table = ``table_structure : ((( atom_var list # num # (string# num list) action_expr) list list # num,
                                          (string# num list) action_expr) decision_structure)``        
  





  
val policy_order_list = listSyntax.dest_list policy_order |> #1


(*convert arith policy to var policy*)

val arith_policy_eval = EVAL “convert_arith_to_var_policy ^arith_policy ^policy_me”;
val var_policy = optionSyntax.dest_some (rhs (concl arith_policy_eval));



(***********************************************)
    
(* eval policy, OLD BDD*)
    
val old_eval_policy_full_opt = EVAL “mk_BDDPred_opt policy_structure (0,[],[(0, non_termn (NONE, ^var_policy))]) [] ^policy_order 1”;
val old_eval_policy_full_opt_rhs = optionSyntax.dest_some (rhs (concl old_eval_policy_full_opt));
    
(* eval policy, new BDD*)

val new_eval_policy_full_opt = EVAL “mk_BDDPred_opt_new policy_structure (0,[],[(0, id_non_termn (NONE), 0)], [(0,^var_policy)]) [] ^policy_order 1”;
    
(* sml procedure policy, new BDD*)

val new_procedure_full_opt = mk_BDDPred_opt_new_thm rec_flag “(0n,[]:edges,[(0n, (id_non_termn NONE):(string # num list) action_expr id, 0n)], [(0n,^var_policy)])” policy_order_list 
   

    
(**** generate a var table *****)
val test_groupings = rhs(concl(EVAL policy_full_order));
val gen_var_table_auto =  bdd_utilsLib.bdd_to_tables_iterative old_eval_policy_full_opt_rhs test_groupings;


(* eval TABLE, OLD BDD*)

val old_eval_table_full_opt = EVAL “mk_BDDPred_opt table_structure (0,[],[(0, non_termn (NONE, ^gen_var_table_auto))]) [] ^policy_order 1”;
val old_eval_table_full_opt_rhs = optionSyntax.dest_some (rhs (concl old_eval_table_full_opt));
    
(* eval TABLE, new BDD*)

val new_eval_table_full_opt = EVAL “mk_BDDPred_opt_new table_structure (0,[],[(0, id_non_termn (NONE), 0)], [(0,^gen_var_table_auto)]) [] ^policy_order 1”;
    
(* sml procedure TABLE, new BDD*)

val new_procedure_table_full_opt = mk_BDDPred_opt_new_thm rec_flag_table “(0n,[]:edges,[(0n, (id_non_termn NONE):(string # num list) action_expr id, 0n)], [(0n,^gen_var_table_auto)])” policy_order_list 
   






    



val _ = export_theory ();


(*
                               
(* Theorem for body_of_mk_new with first variable *)
val body_thm1 = 
    EVAL ``body_of_mk_new pred_structure
             (0,[],[(0,id_non_termn NONE,0)],[(0,And (Var "x") (Var "y"))]) "x" 1``;

(* Theorem for optimize_bdd_new on first step *)
val optimize_thm1 =
    EVAL ``optimize_bdd_new (0,[(0,1,2)],
         [(0,id_non_termn (SOME "x"),0); (1,id_non_termn NONE,0);
          (2,id_termn F,1)]) ["x"]``;

(* Theorem for body_of_mk_new with second variable *)
val body_thm2 =
    EVAL ``body_of_mk_new pred_structure
             (0,[(0,1,2)],
         [(0,id_non_termn (SOME "x"),0); (1,id_non_termn NONE,0);
          (2,id_termn F,1)],[(0,Var "y"); (1,False)]) "y" 3``;

(* Theorem for optimize_bdd_new on second step *)
val optimize_thm2 =
    EVAL ``optimize_bdd_new (0,[(0,1,2); (1,3,4)],
         [(0,id_non_termn (SOME "x"),0); (1,id_non_termn (SOME "y"),0);
          (2,id_termn F,1); (3,id_termn T,0); (4,id_termn F,1)]) ["y"; "x"]``;


(* Now prove the final theorem with all the reductions *)

val final_thm =
    SIMP_CONV (bool_ss) 
      [Once mk_BDDPred_opt_new_def, 
       body_thm1, optimize_thm1, body_thm2, optimize_thm2,
       optionTheory.option_case_def,    (* The actual option case theorem *)
       pairTheory.pair_case_thm]        (* The actual pair case theorem *)
      ``mk_BDDPred_opt_new pred_structure
          (0,[],[(0,id_non_termn NONE,0)],[(0,And (Var "x") (Var "y"))]) []
          ["x"; "y"] 1``;

val final_thm_clean =
    SIMP_RULE (bool_ss) [LET_THM, FST, SND] final_thm;

    
val triple_reduction = prove(
  ``(λ(r',edges',labels_id'). f r' edges' labels_id') (a,b,c) = f a b c``,
  rw []);

val final_thm_beta =
    SIMP_RULE std_ss [triple_reduction] final_thm_clean;



----------------------------------------------------
val reduced = 
    REWRITE_CONV [Once mk_BDDPred_opt_new_def, body_thm1] 
      ``mk_BDDPred_opt_new pred_structure
          (0,[],[(0,id_non_termn NONE,0)],[(0,And (Var "x") (Var "y"))]) []
          ["x"; "y"] 1``;

(* Now manually substitute the known values *)
val manual_thm = prove(
  ``(case SOME ((0,[(0,1,2)],
                [(0,id_non_termn (SOME "x"),0); (1,id_non_termn NONE,0);
                 (2,id_termn F,1)],[(0,Var "y"); (1,False)]),3) of
      NONE => NONE
    | SOME ((r,edges,labels_id,labels_content),c') =>
        (let (r',edges',labels_id') = optimize_bdd_new (r,edges,labels_id) ["x"] in
         mk_BDDPred_opt_new pred_structure (r',edges',labels_id',labels_content) ["x"] ["y"] c')) =
    mk_BDDPred_opt_new pred_structure
      (0,[(0,1,2)],
       [(0,id_non_termn (SOME "x"),0); (1,id_non_termn NONE,0);
        (2,id_termn F,1)],[(0,Var "y"); (1,False)]) ["x"] ["y"] 3``,
  rw [optimize_thm1]);

val final_thm_step1 = TRANS reduced manual_thm;

(* Continue with the recursive call *)
val final_thm_step2 = 
    REWRITE_RULE [Once mk_BDDPred_opt_new_def, body_thm2, optimize_thm2, mk_BDDPred_opt_new_def] 
                 final_thm_step1;


val case_reduction = prove(
  ``(case SOME x of NONE => a | SOME y => b y) = b x``,
  rw []);

val final_thm_step3 = SIMP_RULE std_ss [case_reduction] final_thm_step2;

(* Now we should have the final result *)
val final_thm = final_thm_step3;


val final_thm =
    REWRITE_RULE 
      [case_reduction,
       pairTheory.pair_case_def,
       BETA_THM,
       optimize_thm2] 
      final_thm_step2;

*)
