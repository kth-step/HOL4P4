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


open p4Lib;
open blastLib bitstringLib;
open p4Theory;
open p4_auxTheory;
open p4_coreTheory;
     
open bdd_genTheory;     
open pred_specTheory;     
open policy_specTheory;   
open tables_specTheory;
open bdd_isomorphTheory;
open bdd_end_to_endTheory;     

open policy_arith_to_varTheory;
open table_var_to_arithTheory;
open table_arith_to_intervalTheory;

open bdd_auxTheory;
open table_bs_propertiesTheory;
     


val _ = load "bdd_utils";   

val _ = new_theory "bdd_test_cases";


    
(* a few types abbreviations *)
val _ = type_abbrev("BDD_tbl_type", “:(( (string# num list) var_table_list, (string# num list) action_expr) BDD)”);

val _ = type_abbrev("struc_tbl_type", “:((( atom_var list # num # (string# num list) action_expr) list list # num,
                                          (string# num list) action_expr) decision_structure)”);

val _ = type_abbrev("action_rule_type", “:((string# num list) action_expr) rule”);
val _ = type_abbrev("action_policy_type", “:((string# num list) action_expr) policy”);

(*
val _ = type_abbrev("arith_rule_typ", “:((string# num list) action_expr) arith_rule”);
val _ = type_abbrev("arith_policy_typ", “:((string# num list) action_expr) arith_policy”);
*)





        
    
(****************************************************************)
(****************************************************************)
(*                            POLICY 1                          *)
(****************************************************************)
(****************************************************************)
   

(* policy 1: arith POLICY representation *)

val test_pd_type1 = “[("h" , type_record [("ttl", type_length 8);
                                          ("flag", type_length 4)])]”;

                                          
val is_high_ttl = “(arithm_le (lv_acc (lv_x "h") "ttl") ^(BDDUtils.make_bv 100 8) )”;
val is_low_ttl = “(arithm_ge (lv_acc (lv_x "h") "ttl") ^(BDDUtils.make_bv 1 8) )”;
val is_flag_ok = “(arithm_le (lv_acc (lv_x "h") "flag") ^(BDDUtils.make_bv 3 4) )”;

        
val policy1_me1 =   “[("x", ^is_high_ttl);
                      ("y", ^is_low_ttl );
                      ("z", ^is_flag_ok)]”;

val policy1_full_order = “[("a",["x";"y"]);("b",["z"])]”;                      

val policy1_order = “["x";"y";"z"]”;                      

    
val arith_policy1_rule1 = “(arith_and (arith_a ^is_high_ttl) ( arith_a ^is_low_ttl) ,
                            action ("fwd",[(1:num)])):((string# num list) action_expr) arith_rule”;
                            
val arith_policy1_rule2 = “(arith_a (^is_flag_ok) , action ("fwd",[2]))
                           :((string# num list) action_expr) arith_rule”;
                           
val arith_policy1_rule3 = “(arith_a a_True, action ("drop",[])):((string# num list) action_expr) arith_rule”;
                    

val arith_policy1 =   “[^arith_policy1_rule1 ;
                        ^arith_policy1_rule2 ;
                        ^arith_policy1_rule3]:((string# num list) action_expr) arith_policy”;





(********************************)

        
(*convert arith policy to var policy*)        
val arith_policy1_eval = EVAL “convert_arith_to_var_policy ^arith_policy1 ^policy1_me1”;
val var_policy1 = optionSyntax.dest_some (rhs (concl arith_policy1_eval));

    
(* first establish distinction of domain and range of me*)
val policy1_me1_fst_distinct = EVAL “ALL_DISTINCT (MAP FST ^policy1_me1)”;
val policy1_me1_snd_distinct = EVAL “ALL_DISTINCT (MAP SND ^policy1_me1)”;

val all_distinct_conj = CONJ policy1_me1_fst_distinct policy1_me1_snd_distinct;

    
(* Theorem of correctness for conversion from arith policy to var policy *)
val arith_policy1_var_policy1_thm = REWRITE_RULE[all_distinct_conj, arith_policy1_eval]
(ISPECL[arith_policy1, var_policy1, policy1_me1] policy_airth_to_var_sem_conversion_correct);  

                       
(* create BDD of var policy  *)
val eval_policy1_full_opt = EVAL “mk_BDDPred_opt policy_structure (0,[],[(0, non_termn (NONE, ^var_policy1))]) [] ^policy1_order 1”;
val eval_policy1_full_opt_rhs = optionSyntax.dest_some (rhs (concl eval_policy1_full_opt));


(* automatically generate a var table from the var policy's BDD via sml*)
val test_groupings1 = rhs(concl(EVAL policy1_full_order));
val test_action_table1_auto = BDDUtils.bdd_to_tables_iterative eval_policy1_full_opt_rhs test_groupings1;

    
(* now create a BDD for the table*)    
val eval_table1_full_opt_auto = EVAL “mk_BDDPred_opt table_structure (0,[],[(0, non_termn (NONE, ^test_action_table1_auto))]) [] ^policy1_order 1”;
val eval_table1_full_opt_auto_rhs = optionSyntax.dest_some (rhs (concl eval_table1_full_opt_auto));

    
(* get I (pairs isomorphic in the graph), and check if isisIsomorph *)
val get_i_policy1 = BDDUtils.pairBDDs (eval_table1_full_opt_auto_rhs , eval_table1_full_opt_auto_rhs);
val is_tbl_policy1_iso = EVAL “isIsomorph_exec ^get_i_policy1 ^eval_table1_full_opt_auto_rhs ^eval_table1_full_opt_auto_rhs”;

    
(* Theorem of correctness for conversion from var policy to var table *)
val policy1_thm_init = computeLib.RESTR_EVAL_CONV [“sem_tables”,“sem_policy”, “mv_dom_vars”] “correct_var_policy_var_tables_exec ^var_policy1 ^test_action_table1_auto ^policy1_order ^get_i_policy1 ”;     
val policy1_thm = SIMP_RULE bool_ss [correct_var_policy_var_tables_exec_thm1] policy1_thm_init;    


(* covert var table to interval table *)
val only_var_table1 = fst (dest_pair test_action_table1_auto);
val convert_to_interval1 = EVAL “convert_var_to_sinterval_tables ^only_var_table1 ^policy1_me1  ^test_pd_type1”;   
val only_interval_table1 = optionSyntax.dest_some(rhs (concl convert_to_interval1));

    
(* Theorem of correctness for conversion from var table to inteval table *)
val final_table1_thm =
REWRITE_RULE [convert_to_interval1] (ISPECL[only_var_table1, only_interval_table1, “0:num”, policy1_me1, test_pd_type1 ] correct_tables_from_var_to_sinterval_thm);        


             
(* to glue the theorems we need to take care of the conditions/ assumptions *)
             
(* condition1 *)                             
val every_lval_in_me_in_type_thm = EVAL “every_lval_in_me_in_type ^test_pd_type1 ^policy1_me1”;
val cond1_thm = REWRITE_RULE [every_lval_in_me_in_type_thm, policy1_me1_fst_distinct] (ISPECL[policy1_me1, test_pd_type1 ] lval_in_me_distinct_imp_cond1);

    
(* condition2 *)         
val in_order_then_in_me_thm = EVAL “in_order_then_in_me ^policy1_order ^policy1_me1”;
val ops_in_me_length_format_thm = EVAL “ops_in_me_length_format ^test_pd_type1 ^policy1_me1”;

val cond2_thm = REWRITE_RULE [every_lval_in_me_in_type_thm, policy1_me1_fst_distinct,
                             in_order_then_in_me_thm, ops_in_me_length_format_thm]
                             (ISPECL[policy1_me1, test_pd_type1, policy1_order ]
                                    wf_format_imp_cond2);   
                                      
(* condition3 *)     
val cond3_thm = REWRITE_RULE [every_lval_in_me_in_type_thm, policy1_me1_fst_distinct,
                             in_order_then_in_me_thm, ops_in_me_length_format_thm]
                             (ISPECL[policy1_me1, test_pd_type1]
                                    wf_format_imp_cond3);   

                                    
val final_thm = prove(
  “! packet_input .
     wf_packet ^test_pd_type1 packet_input ⇒ 
     sem_arith_policy ^arith_policy1 packet_input = 
     sem_sinterval_tables (^only_interval_table1,0) packet_input”
  ,
  
  rpt strip_tac >>
      
  assume_tac arith_policy1_var_policy1_thm >>
  first_x_assum (strip_assume_tac o (Q.SPECL [‘packet_input’,‘(create_mv ^policy1_me1 packet_input)’])) >>
  
  assume_tac policy1_thm >>
  first_x_assum (strip_assume_tac o (Q.SPECL [‘(create_mv ^policy1_me1 packet_input)’])) >>

  
  assume_tac final_table1_thm >>
  first_x_assum (strip_assume_tac o (Q.SPECL [‘packet_input’,‘(create_mv ^policy1_me1 packet_input)’])) >>
      
  fs[cond1_thm, cond2_thm, cond3_thm]
);








(*
TODO:
1. sota review: why is this work more complete than anything we have found
2. complexity: stage2 complexity. [stage1 and 3 are linear wrt. size of input probably?]
3. Can we handle practical tables, and deploy them?
4. performance and scalability (WCET) + synthetic examples that reflects the complexity of the three stages of the pipeline
*)




             
    
(*
                                
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



(* automatically generate a table*)
val test_groupings2 = rhs(concl(EVAL “[("a",["x";"y"]);("b",["z";"w"])]”));
val test_action_table2_auto =BDDUtils.bdd_to_tables_iterative eval_policy2_full_opt_rhs test_groupings2;

(* now create a BDD for the table*)    
val eval_table2_full_opt_auto = EVAL “mk_BDDPred_opt table_structure (0,[],[(0, non_termn (NONE, ^test_action_table2_auto))]) [] ["x";"y";"z";"w"] 1”;
val eval_table2_full_opt_auto_rhs = optionSyntax.dest_some (rhs (concl eval_table2_full_opt_auto));

(* get I, and check if isisIsomorph *)
val get_i_policy2 = BDDUtils.pairBDDs (eval_table2_full_opt_auto_rhs , eval_table2_full_opt_auto_rhs);
val is_tbl_policy2_iso = EVAL “isIsomorph_exec ^get_i_policy2 ^eval_table2_full_opt_auto_rhs ^eval_table2_full_opt_auto_rhs”;

(* get a theorem out*)
val policy2_thm_init = computeLib.RESTR_EVAL_CONV [“sem_tables”,“sem_policy”, “mv_dom_vars”] “correct_var_policy_var_tables_exec ^var_policy2 ^test_action_table2_auto ["x";"y";"z";"w"] ^get_i_policy2 ”;     
val policy2_thm = SIMP_RULE bool_ss [correct_var_policy_var_tables_exec_thm1] policy2_thm_init;     


*)



    
(*  (* Manual effort*)
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

val var_tbls2 = ``[^var_tbl1; ^var_tbl2; ^var_tbl3] : ((string# num list) var_table_list) ``;
val var_tbls2_start = ``([^var_tbl1; ^var_tbl2; ^var_tbl3] : ((string# num list) var_table_list),(0:num)) ``;


val eval_table2_full_opt = EVAL “mk_BDDPred_opt table_structure (0,[],[(0, non_termn (NONE, ^var_tbls2_start))]) [] ["x";"y";"z";"w"] 1”;
val eval_table1_full_opt_rhs = optionSyntax.dest_some (rhs (concl eval_table2_full_opt));

val get_i_policy2 = BDDUtils.pairBDDs (eval_policy2_full_opt_rhs, eval_table1_full_opt_rhs);
val is_tbl_policy2_iso = EVAL “isIsomorph_exec ^get_i_policy2 ^eval_policy2_full_opt_rhs ^eval_table1_full_opt_rhs”;
*)





(***************************************************)

(*
val AND = ``λ(p1,a1) (p2,a2). (arith_and p1 p2, a2)``;
val OR  = ``λ(p1,a1) (p2,a2). (arith_or p1 p2, a1)``; 
val NOT = ``λ(p,a). (arith_not p, a)``;
*)

(*
val test_packet = “[
  ("h", val_record [
    ("ip", val_record [
      ("ttl", val_num 64);
      ("proto", val_num 6);
      ("version", val_num 4)
    ]);
    ("src_zone", val_num 1);
    ("threat_score", val_num 30);
    ("auth_status", val_num 1)
  ])
  ]”;

  
val is_tcp =      “arith_a (arithm_le (lv_acc (lv_acc (lv_x "h") "ip") "proto") 6)”;
val is_high_ttl = “arith_a (arithm_ge (lv_acc (lv_acc (lv_x "h") "ip") "ttl") 60)”;
val is_internal = “arith_a (arithm_le (lv_acc (lv_x "h") "src_zone") 1)”;
val is_malicious = “arith_a (arithm_ge (lv_acc (lv_x "h") "threat_score") 80)”;


val policy3_me1 = “[
  ("is_tcp", (arithm_eq (lv_acc (lv_acc (lv_x "h") "ip") "proto") 6));
  ("is_high_ttl", (arithm_gt (lv_acc (lv_acc (lv_x "h") "ip") "ttl") 60));
  ("is_internal",  (arithm_eq (lv_acc (lv_x "h") "src_zone") 1));
  ("is_malicious",  (arithm_gt (lv_acc (lv_x "h") "threat_score") 80))
]”;

val arith_policy3_rule1 = “(arith_and ^is_tcp ^is_high_ttl , action ("fwd",[(1:num)])):((string# num list) action_expr) arith_rule”;
val arith_policy3_rule2 = “(arith_or (arith_not ^is_tcp) (^is_high_ttl), action ("fwd",[2])) :((string# num list) action_expr) arith_rule”;
val arith_policy3_rule3 = “(arith_a a_True, action ("drop",[])):((string# num list) action_expr) arith_rule”;
                    

val arith_policy3 =   “[ ^arith_policy3_rule1 ;
                        ^arith_policy3_rule2 ;
                        ^arith_policy3_rule3]:((string# num list) action_expr) arith_policy”;


val arith_policy3_eval = EVAL convert_arith_to_var_policy ^arith_policy3 ^policy3_me1”;

val var_policy3 = optionSyntax.dest_some (rhs (concl arith_policy3_eval));


(* first establish distinction *)
val policy3_me1_fst_distinct = EVAL ``ALL_DISTINCT (MAP FST ^policy3_me1)``;
val policy3_me1_snd_distinct = EVAL ``ALL_DISTINCT (MAP SND ^policy3_me1)``;

(*second, combine them  *)
val all_distinct_conj = CONJ policy3_me1_fst_distinct policy3_me1_snd_distinct;

val alookup_cond_thm = EVAL “∀var atom. ALOOKUP ^policy3_me1 var = SOME atom ⇒ ALOOKUP m_v var = eval_arithm_atom packet_input atom”;

                
val arith_policy3_var_policy3_thm = REWRITE_RULE[all_distinct_conj, arith_policy3_eval]
(ISPECL[arith_policy3, var_policy3, policy3_me1] policy_airth_to_var_sem_conversion_correct);        

*)

                      
val _ = export_theory ();







