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







        
    
(****************************************************************)
(****************************************************************)
(*                            POLICY 1                          *)
(****************************************************************)
(****************************************************************)
   

(* policy 1: arith POLICY representation *)


 
val test_pd_type1 = “[("ip", type_record [("priority", type_length 3);
                                         ("size", type_length 16);
                                         ("age", type_length 8);
                                         ("type", type_length 4)])]”;

val is_high_priority = “(arithm_le (lv_acc (lv_x "ip") "priority") ^(BDDUtils.make_bv 2 3))”;
val is_medium_priority = “(arithm_ge (lv_acc (lv_x "ip") "priority") ^(BDDUtils.make_bv 4 3))”;
val is_small_packet = “(arithm_le (lv_acc (lv_x "ip") "size") ^(BDDUtils.make_bv 500 16))”;
val is_young_packet = “(arithm_ge (lv_acc (lv_x "ip") "age") ^(BDDUtils.make_bv 200 8))”;
val is_control_type = “(arithm_le (lv_acc (lv_x "ip") "type") ^(BDDUtils.make_bv 3 4))”;
val is_data_type = “(arithm_ge (lv_acc (lv_x "ip") "type") ^(BDDUtils.make_bv 8 4))”;

val policy1_me1 =   “[("x", ^is_high_priority);
                      ("y", ^is_medium_priority);
                      ("z", ^is_small_packet);
                      ("w", ^is_young_packet);
                      ("q", ^is_control_type);
                      ("r", ^is_data_type)]”;

val policy1_full_order = “[("a",["x";"y"]);
                          ("b",["z"]);
                          ("c",["w"]);
                          ("d",["q";"r"])]”;

val policy1_order = “["x";"y";"z";"w";"q";"r"]”;

(* Rule 1: High priority small control packets - expedited forwarding *)
val arith_policy1_rule1 = “(arith_and (arith_a ^is_high_priority) 
                            (arith_and (arith_a ^is_small_packet) (arith_a ^is_control_type)),
                            action ("fwd_priority",[1; 255])):((string# num list) action_expr) arith_rule”;

(* Rule 2: High priority data packets *)
val arith_policy1_rule2 = “(arith_and (arith_a ^is_high_priority) (arith_a ^is_data_type),
                            action ("fwd",[1])):((string# num list) action_expr) arith_rule”;

(* Rule 3: Medium priority young packets *)
val arith_policy1_rule3 = “(arith_and (arith_a ^is_medium_priority) (arith_a ^is_young_packet),
                            action ("fwd",[2])):((string# num list) action_expr) arith_rule”;

(* Rule 7: Default forward rule *)
val arith_policy1_rule7 = “(arith_a a_True,
                            action ("fwd",[5])):((string# num list) action_expr) arith_rule”;

val arith_policy1 =   “[^arith_policy1_rule1;
                        ^arith_policy1_rule2;
                        ^arith_policy1_rule3;
                        ^arith_policy1_rule7]:((string# num list) action_expr) arith_policy”;


(********************************)



(***********************)
(*       STAGE 1       *)
(***********************)

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


(***********************)
(*       STAGE 2       *)
(***********************)
                       
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
val get_i_policy1 = BDDUtils.pairBDDs (eval_policy1_full_opt_rhs, eval_table1_full_opt_auto_rhs);
(*val is_tbl_policy1_iso = EVAL “isIsomorph_exec ^get_i_policy1 ^eval_policy1_full_opt_rhs
                                                              ^eval_table1_full_opt_auto_rhs”;
 *)

    
(* Theorem of correctness for conversion from var policy to var table *)

(* we can do it in two methods, this is: *)
(* method 1 *)
val policy1_thm_init = computeLib.RESTR_EVAL_CONV [“sem_tables”,“sem_policy”, “mv_dom_vars”] “correct_var_policy_var_tables_exec ^var_policy1 ^test_action_table1_auto ^policy1_order ^get_i_policy1 ”;     
val policy1_thm = SIMP_RULE bool_ss [correct_var_policy_var_tables_exec_thm1] policy1_thm_init;    



(***********************)
(*       STAGE 3       *)
(***********************)   

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





                      
val _ = export_theory ();





             
