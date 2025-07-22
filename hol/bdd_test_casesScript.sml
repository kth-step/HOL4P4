open HolKernel boolLib liteLib simpLib Parse bossLib;
open arithmeticTheory stringTheory containerTheory pred_setTheory
     listTheory finite_mapTheory;

open bitstringTheory;
open wordsTheory;
open optionTheory;
open sumTheory;
open stringTheory;
open ottTheory;
open pairTheory;
open rich_listTheory;
open arithmeticTheory;
open alistTheory;
open numeralTheory;
open alistTheory;

open bdd_genTheory;     
open pred_specTheory;     
open policy_specTheory;   
open tables_specTheory;
open bdd_isomorphTheory;



val _ = load "bdd_utils";   

val _ = new_theory "bdd_test_cases";




(* a few types abbreviations *)
val _ = type_abbrev("BDD_tbl_type", “:(( (string# num list) table_list, (string# num list) action_expr) BDD)”);

val _ = type_abbrev("struc_tbl_type", “:(((
         atom_var list # num # (string# num list) action_expr) list list # num,
                 (string# num list) action_expr) decision_structure)”);

val _ = type_abbrev("action_rule_type", “:((string# num list) action_expr) rule”);
val _ = type_abbrev("action_policy_type", “:((string# num list) action_expr) policy”);




    
(****************************************************************)
(****************************************************************)
(*                            POLICY 1                          *)
(****************************************************************)
(****************************************************************)
   
(* 
      x ∧ y : fwd(1)
          z : fwd(2)
          T : drop()
*)


        
(* policy 1: var POLICY representation *)
   
val var_policy1_rule1 = ``(And (Var "x") (Var "y"), action ("fwd",[1])): action_rule_type``;
val var_policy1_rule2 = ``(Var "z", action ("fwd",[2])): action_rule_type``;
val var_policy1_rule3 = ``(True, action ("drop",[])): action_rule_type``;

val var_policy1 = ``[^var_policy1_rule1; ^var_policy1_rule2; ^var_policy1_rule3 ] : action_policy_type``;

val eval_policy1_full_opt = EVAL ``mk_BDDPred_opt policy_structure (0,[],[(0, non_termn (NONE, ^var_policy1))]) [] ["x";"y";"z"] 1``;
val eval_policy1_full_opt_rhs = optionSyntax.dest_some (rhs (concl eval_policy1_full_opt));

                                                                                        
                     
(* policy 1: var TABLE representation *)


(* manual table generation by user*)   
val var_tbl1_line1 = ``([(Var "x"); (Var "y")]     , 0, state 2): (string# num list) line``;
val var_tbl1_line2 = ``([(Var "x"); Not (Var "y")] , 0, state 3): (string# num list) line``;
val var_tbl1_line3 = ``([Not (Var "x")]            , 0, state 3): (string# num list) line``;
val var_tbl1 = ``[^var_tbl1_line1; ^var_tbl1_line2; ^var_tbl1_line3] : (string# num list) table``;
    
val var_tbl2_line1 = ``([(Var "z")]     , 3, state 4): (string# num list) line``;
val var_tbl2_line2 = ``([Not (Var "z")] , 3, state 5): (string# num list) line``;
val var_tbl2_line3 = ``([True]          , 2, state 2): (string# num list) line``;
val var_tbl2 = ``[^var_tbl2_line1; ^var_tbl2_line2; ^var_tbl2_line3] : (string# num list) table``;

val var_tbl3_line1 = ``([True] , 2, action ("fwd",[1])): (string# num list) line``;
val var_tbl3_line2 = ``([True] , 4, action ("fwd",[2])): (string# num list) line``;
val var_tbl3_line3 = ``([True] , 5, action ("drop",[])): (string# num list) line``;
val var_tbl3 = ``[^var_tbl3_line1; ^var_tbl3_line2; ^var_tbl3_line3] : (string# num list) table``;

val var_tbls1 = ``[^var_tbl1; ^var_tbl2; ^var_tbl3] : ((string# num list) table_list) ``;
val var_tbls1_start = ``([^var_tbl1; ^var_tbl2; ^var_tbl3] : ((string# num list) table_list),(0:num)) ``;


(* (* automatically generated, need to fox something in the types?*)
val test_groupings1 = rhs(concl(EVAL “[("a",["x";"y"]);("b",["z"])]”));
val test_action_table1_auto = BDDUtils.bdd_to_tables_iterative eval_policy1_full_opt_rhs test_groupings1;
val test_action_table1_auto_rhs = rhs (concl (EVAL test_action_table1_auto));

           
val test_action_table1_auto_num = 
  CONV_RULE (REWR_CONV (GSYM (Thm.INST_TYPE [alpha |-> ``:num``] INT_NUM_CONV))) 
  test_action_table1_auto_rhs;

    
val eval_table1_full_opt_auto =
EVAL “mk_BDDPred_opt table_structure
       ((0:num),[],[((0:num), non_termn (NONE, ^test_action_table1_auto_rhs))])
       [] ["x";"y";"z"] (1:num)”;
*)

    
val eval_table1_full_opt = EVAL “mk_BDDPred_opt table_structure (0,[],[(0, non_termn (NONE, ^var_tbls1_start))]) [] ["x";"y";"z"] 1”;
val eval_table1_full_opt_rhs = optionSyntax.dest_some (rhs (concl eval_table1_full_opt));


val get_i_policy1 = BDDUtils.pairBDDs (eval_policy1_full_opt_rhs , eval_table1_full_opt_rhs);
val is_tbl_policy1_iso = EVAL “isIsomorph_exec ^get_i_policy1 ^eval_policy1_full_opt_rhs ^eval_table1_full_opt_rhs”;

(*********************)



   (*   
(* this simplifies too much, do not use it*)
SIMP_CONV bool_ss [correct_var_policy_var_tables_exec_def, mk_BDDPred_opt_def, body_of_mk_def]
          “correct_var_policy_var_tables_exec ^var_policy1 ^var_tbls1_start ["x";"y";"z"] ^get_i_policy1 ”


(* this restricts EVAL to not to take the sefs of sem_tables ... since we wan't them in the theorem*)
val this_is_a_thm = computeLib.RESTR_EVAL_CONV [“sem_tables”,“sem_policy”, “mv_dom_vars”] “correct_var_policy_var_tables_exec ^var_policy1 ^var_tbls1_start ["x";"y";"z"] ^get_i_policy1 ”

(* if it is a fail case, we just return T, nothing, no theorem*)    
val this_is_a_thm_fail = computeLib.RESTR_EVAL_CONV [“sem_tables”,“sem_policy”, “mv_dom_vars”] “correct_var_policy_var_tables_exec ^var_policy1 ^var_tbls1_start ["x";"y";"z"] [((0:num),0)] ”

(* at this point, we want to show that correct_var_policy_var_tables_exec is always true, thus the theorem hold*)                       
SIMP_RULE bool_ss [correct_var_policy_var_tables_exec_thm1] this_is_a_thm
*)
    
    
(*


val bdd_correct_init_thm = REWRITE_RULE [all_distinct_vars_thm, simp_fv_thm, GSYM eval_policy]
(ISPECL[var_policy1, “["x";"y";"z"]”, eval_result] correct_var_policy_var_tables_thm1)


    
val vars_policy1 = EVAL “["x";"y";"z"]”;
val all_distinct_vars_thm = EVAL “ ALL_DISTINCT ["x";"y";"z"]”;



val eval_policy = EVAL “mk_BDDPred policy_structure (0,[],[(0, non_termn (NONE, ^var_policy1))]) [] ["x";"y";"z"] 1”;
val eval_result = optionSyntax.dest_some (rhs (concl eval_policy ));
val opt_res1 = EVAL “ bdd_full_optimize ^eval_result ”;
val opt_res_dest1 = (rhs (concl opt_res1));

    
val simp_fv_thm = EVAL “fv_in_vars policy_structure
                        [(And (Var "x") (Var "y"),action ("fwd",[1]));
                         (Var "z",action ("fwd",[(2:num)])); (True,action ("drop",[]))]
                        ["x"; "y"; "z"]”;

         
(* forward proof *)
REWRITE_RULE [all_distinct_vars_thm, simp_fv_thm]
(ISPECL[var_policy1, “["x";"y";"z"]”] policy_mk_bdd_correct_thm)



val opt_res1 = EVAL “ BDD_opt ^eval_result ”;

val bdd_correct_init_thm = REWRITE_RULE [all_distinct_vars_thm, simp_fv_thm, GSYM eval_policy]
(ISPECL[var_policy1, “["x";"y";"z"]”, eval_result] policy_mk_bdd_correct_thm)
    
  

(*
TODO : add the optimisation proof
cheat for now
*)


prove( “! vars. BDD1 .BDD2. (BDD2 =  BDD_opt BDD1) ==> 
correct_sem policy_structure BDD1 (REVERSE vars) ==>
correct_sem policy_structure BDD2 (REVERSE vars)” , cheat)

(* apply to mkBDD should be the equal to opt_res1*)

*)


            
    




    


                                
(****************************************************************)
(****************************************************************)
(*                            POLICY 2                          *)
(****************************************************************)
(****************************************************************)
   
(*    This is the camus paper example
          x     : fwd(1)
          x ∧ z : fwd(2)
          y ∧ w : fwd(3)  
          T     : drop()
*)


                                                        
(* policy 2: var policy representation *)
val var_policy2_rule1 = ``(Var "x", action ("fwd",[1])): action_rule_type``;
val var_policy2_rule2 = ``(And (Var "x") (Var "z"), action ("fwd",[2])): action_rule_type``;
val var_policy2_rule3 = ``(And (Var "y") (Var "w"), action ("fwd",[3])): action_rule_type``;
val var_policy2_rule4 = ``(True, action ("drop",[])): action_rule_type``;

val var_policy2 = ``[ ^var_policy2_rule1; ^var_policy2_rule2; ^var_policy2_rule3; ^var_policy2_rule4 ] : action_policy_type``;

val eval_policy2_full_opt = EVAL “mk_BDDPred_opt policy_structure (0,[],[(0, non_termn (NONE, ^var_policy2))]) [] ["x";"y";"z";"w"] 1”;
val eval_policy2_full_opt_rhs = optionSyntax.dest_some (rhs (concl eval_policy2_full_opt));


(* policy 2: var table representation *)
val var_tbl1_line1 = ``([(Var "x")]                     , 0, state 1): (string# num list) line``;
val var_tbl1_line2 = ``([Not (Var "x"); (Var "y")]      , 0, state 3): (string# num list) line``;
val var_tbl1_line3 = ``([Not (Var "x"); Not (Var "y")]  , 0, state 4): (string# num list) line``;

val var_tbl1 = ``[^var_tbl1_line1; ^var_tbl1_line2; ^var_tbl1_line3] : (string# num list) table``;
     

val var_tbl2_line1 = ``([(Var "z"); (Var "w")]     , 3, state 7): (string# num list) line``;
val var_tbl2_line2 = ``([(Var "z"); Not (Var "w")] , 3, state 8): (string# num list) line``;
val var_tbl2_line3 = ``([Not (Var "z"); (Var "w")] , 3, state 9): (string# num list) line``;
val var_tbl2_line4 = ``([Not (Var "z"); Not (Var "w")] , 3, state 10): (string# num list) line``;
val var_tbl2_line5 = ``([True]                         , 1, state 1): (string# num list) line``;
val var_tbl2_line6 = ``([True]                         , 4, state 4): (string# num list) line``;


val var_tbl2 = ``[^var_tbl2_line1; ^var_tbl2_line2; ^var_tbl2_line3;
                  ^var_tbl2_line4; ^var_tbl2_line5; ^var_tbl2_line6] : (string# num list) table``;


val var_tbl3_line1 = ``([True] , 1, action ("fwd",[1])): (string# num list) line``;
val var_tbl3_line2 = ``([True] , 4, action ("drop",[])): (string# num list) line``;
val var_tbl3_line3 = ``([True] , 7, action ("fwd",[3])): (string# num list) line``;
val var_tbl3_line4 = ``([True] , 8, action ("drop",[])): (string# num list) line``;
val var_tbl3_line5 = ``([True] , 9, action ("fwd",[3])): (string# num list) line``;
val var_tbl3_line6 = ``([True] , 10, action ("drop",[])): (string# num list) line``;

val var_tbl3 = ``[^var_tbl3_line1; ^var_tbl3_line2; ^var_tbl3_line3;
                 ^var_tbl3_line4; ^var_tbl3_line5; ^var_tbl3_line6] : (string# num list) table``;

val var_tbls2 = ``[^var_tbl1; ^var_tbl2; ^var_tbl3] : ((string# num list) table_list) ``;
val var_tbls2_start = ``([^var_tbl1; ^var_tbl2; ^var_tbl3] : ((string# num list) table_list),(0:num)) ``;


val eval_table2_full_opt = EVAL “mk_BDDPred_opt table_structure (0,[],[(0, non_termn (NONE, ^var_tbls2_start))]) [] ["x";"y";"z";"w"] 1”;
val eval_table1_full_opt_rhs = optionSyntax.dest_some (rhs (concl eval_table2_full_opt));

val get_i_policy2 = BDDUtils.pairBDDs (eval_policy2_full_opt_rhs, eval_table1_full_opt_rhs);
val is_tbl_policy2_iso = EVAL “isIsomorph_exec ^get_i_policy2 ^eval_policy2_full_opt_rhs ^eval_table1_full_opt_rhs”;





val _ = export_theory ();




