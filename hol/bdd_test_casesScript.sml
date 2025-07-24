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
open bdd_end_to_endTheory;

     

open policy_arith_to_varTheory;



val _ = load "bdd_utils";   

val _ = new_theory "bdd_test_cases";




(* a few types abbreviations *)
val _ = type_abbrev("BDD_tbl_type", “:(( (string# num list) table_list, (string# num list) action_expr) BDD)”);

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


(* automatically generate a table*)
val test_groupings1 = rhs(concl(EVAL “[("a",["x";"y"]);("b",["z"])]”));
val test_action_table1_auto =BDDUtils.bdd_to_tables_iterative eval_policy1_full_opt_rhs test_groupings1;

(* now create a BDD for the table*)    
val eval_table1_full_opt_auto = EVAL “mk_BDDPred_opt table_structure (0,[],[(0, non_termn (NONE, ^test_action_table1_auto))]) [] ["x";"y";"z"] 1”;
val eval_table1_full_opt_auto_rhs = optionSyntax.dest_some (rhs (concl eval_table1_full_opt_auto));

(* get I, and check if isisIsomorph *)
val get_i_policy1 = BDDUtils.pairBDDs (eval_table1_full_opt_auto_rhs , eval_table1_full_opt_auto_rhs);
val is_tbl_policy1_iso = EVAL “isIsomorph_exec ^get_i_policy1 ^eval_table1_full_opt_auto_rhs ^eval_table1_full_opt_auto_rhs”;

(* get a theorem out*)
val policy1_thm_init = computeLib.RESTR_EVAL_CONV [“sem_tables”,“sem_policy”, “mv_dom_vars”] “correct_var_policy_var_tables_exec ^var_policy1 ^test_action_table1_auto ["x";"y";"z"] ^get_i_policy1 ”;     
val policy1_thm = SIMP_RULE bool_ss [correct_var_policy_var_tables_exec_thm1] policy1_thm_init;    


(*    
(* policy 1: var TABLE representation *)

(* manual table generation by user*)
(*
val var_tbl1_line1 = ``([(Var "x"); (Var "y")]     , 0, state 3): (string# num list) line``;
val var_tbl1_line2 = ``([(Var "x"); Not (Var "y")] , 0, state 4): (string# num list) line``;
val var_tbl1_line3 = ``([Not (Var "x")]            , 0, state 4): (string# num list) line``;
val var_tbl1 = ``[^var_tbl1_line1; ^var_tbl1_line2; ^var_tbl1_line3] : (string# num list) table``;
    
val var_tbl2_line1 = ``([(Var "z")]     , 4, state 7): (string# num list) line``;
val var_tbl2_line2 = ``([Not (Var "z")] , 4, state 8): (string# num list) line``;
val var_tbl2_line3 = ``([True]          , 3, state 3): (string# num list) line``;
val var_tbl2 = ``[^var_tbl2_line1; ^var_tbl2_line2; ^var_tbl2_line3] : (string# num list) table``;

val var_tbl3_line1 = ``([True] , 3, action ("fwd",[1])): (string# num list) line``;
val var_tbl3_line2 = ``([True] , 7, action ("fwd",[2])): (string# num list) line``;
val var_tbl3_line3 = ``([True] , 8, action ("drop",[])): (string# num list) line``;
val var_tbl3 = ``[^var_tbl3_line1; ^var_tbl3_line2; ^var_tbl3_line3] : (string# num list) table``;

val var_tbls1 = ``[^var_tbl1; ^var_tbl2; ^var_tbl3] : ((string# num list) table_list) ``;
val var_tbls1_start = ``([^var_tbl1; ^var_tbl2; ^var_tbl3] : ((string# num list) table_list),(0:num)) ``;

     
val eval_table1_full_opt = EVAL “mk_BDDPred_opt table_structure (0,[],[(0, non_termn (NONE, ^var_tbls1_start))]) [] ["x";"y";"z"] 1”;
val eval_table1_full_opt_rhs = optionSyntax.dest_some (rhs (concl eval_table1_full_opt));


(* this restricts EVAL to not to take the sefs of sem_tables ... since we wan't them in the theorem*)
val policy1_thm_init = computeLib.RESTR_EVAL_CONV [“sem_tables”,“sem_policy”, “mv_dom_vars”] “correct_var_policy_var_tables_exec ^var_policy1 ^var_tbls1_start ["x";"y";"z"] ^get_i_policy1 ”;

(* at this point, we want to show that correct_var_policy_var_tables_exec is always true, thus the theorem hold*)                       
val policy1_thm = SIMP_RULE bool_ss [correct_var_policy_var_tables_exec_thm1] policy1_thm_init;
*)

    
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

val var_tbls2 = ``[^var_tbl1; ^var_tbl2; ^var_tbl3] : ((string# num list) table_list) ``;
val var_tbls2_start = ``([^var_tbl1; ^var_tbl2; ^var_tbl3] : ((string# num list) table_list),(0:num)) ``;


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


val test_packet = “[
  ("pkt", val_record [
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

  
val is_tcp =      “arith_a (arithm_eq (lv_acc (lv_acc (lv_x "h") "ip") "proto") 6)”;
val is_high_ttl = “arith_a (arithm_gt (lv_acc (lv_acc (lv_x "h") "ip") "ttl") 60)”;
val is_internal = “arith_a (arithm_eq (lv_acc (lv_x "h") "src_zone") 1)”;
val is_malicious = “arith_a (arithm_gt (lv_acc (lv_x "h") "threat_score") 80)”;


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


val arith_policy3_eval = EVAL “convert ^arith_policy3 ^policy3_me1”;

val var_policy3 = optionSyntax.dest_some (rhs (concl arith_policy3_eval));


(* first establish distinction *)
val policy3_me1_fst_distinct = EVAL ``ALL_DISTINCT (MAP FST ^policy3_me1)``;
val policy3_me1_snd_distinct = EVAL ``ALL_DISTINCT (MAP SND ^policy3_me1)``;

(*second, combine them  *)
val all_distinct_conj = CONJ policy3_me1_fst_distinct policy3_me1_snd_distinct;

val alookup_cond_thm = EVAL “∀var atom. ALOOKUP ^policy3_me1 var = SOME atom ⇒ ALOOKUP m_v var = eval_arithm_atom packet_input atom”;

                
val arith_policy3_var_policy3_thm = REWRITE_RULE[all_distinct_conj, arith_policy3_eval]
(ISPECL[arith_policy3, var_policy3, policy3_me1] policy_airth_to_var_sem_conversion_correct);        



                       
val _ = export_theory ();








