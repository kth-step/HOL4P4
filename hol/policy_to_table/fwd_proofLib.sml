structure fwd_proofLib :> fwd_proofLib = struct


open HolKernel boolLib liteLib simpLib Parse bossLib pairLib;
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
     
open bdd_utilsLib;   



(* a few types abbreviations *)
(*
val _ = type_abbrev("BDD_tbl_type", “:(( (string# num list) var_table_list, (string# num list) action_expr) BDD)”);

val _ = type_abbrev("struc_tbl_type", “:((( atom_var list # num # (string# num list) action_expr) list list # num,
                                          (string# num list) action_expr) decision_structure)”);

val _ = type_abbrev("action_rule_type", “:((string# num list) action_expr) rule”);
val _ = type_abbrev("action_policy_type", “:((string# num list) action_expr) policy”);
*)
        


    fun convert_arith_policy_to_interval_tables (arith_policy, policy_me, test_pd_type, policy_full_order, policy_order) =

    let
            
        (***********************)
        (*       STAGE 1       *)
        (***********************)

        (*convert arith policy to var policy*)        
        val arith_policy_eval = EVAL “convert_arith_to_var_policy ^arith_policy ^policy_me”;
        val var_policy = optionSyntax.dest_some (rhs (concl arith_policy_eval));

            
        (* first establish distinction of domain and range of me*)
        val policy_me_fst_distinct = EVAL “ALL_DISTINCT (MAP FST ^policy_me)”;
        val policy_me_snd_distinct = EVAL “ALL_DISTINCT (MAP SND ^policy_me)”;

        val all_distinct_conj = CONJ policy_me_fst_distinct policy_me_snd_distinct;

            
        (* Theorem of correctness for conversion from arith policy to var policy *)
        val arith_policy_var_policy_thm = REWRITE_RULE[all_distinct_conj, arith_policy_eval]
        (ISPECL[arith_policy, var_policy, policy_me] policy_airth_to_var_sem_conversion_correct);  


        (***********************)
        (*       STAGE 2       *)
        (***********************)
                              
        (* create BDD of var policy  *)
        val eval_policy_full_opt = EVAL “mk_BDDPred_opt policy_structure (0,[],[(0, non_termn (NONE, ^var_policy))]) [] ^policy_order 1”;
        val eval_policy_full_opt_rhs = optionSyntax.dest_some (rhs (concl eval_policy_full_opt));


        (* automatically generate a var table from the var policy's BDD via sml*)
        val test_groupings = rhs(concl(EVAL policy_full_order));
        val gen_var_table_auto = bdd_utilsLib.bdd_to_tables_iterative eval_policy_full_opt_rhs test_groupings;

            
        (* now create a BDD for the table*)    
        val eval_table_full_opt_auto = EVAL “mk_BDDPred_opt table_structure (0,[],[(0, non_termn (NONE, ^gen_var_table_auto))]) [] ^policy_order 1”;
        val eval_table_full_opt_auto_rhs = optionSyntax.dest_some (rhs (concl eval_table_full_opt_auto));

            
        (* get I (pairs isomorphic in the graph), and check if isisIsomorph *)
        val get_i_policy = bdd_utilsLib.pairBDDs (eval_policy_full_opt_rhs, eval_table_full_opt_auto_rhs);
        (*val is_tbl_policy1_iso = EVAL “isIsomorph_exec ^get_i_policy ^eval_policy_full_opt_rhs
                                                                      ^eval_table_full_opt_auto_rhs”;
        *)

            
        (* Theorem of correctness for conversion from var policy to var table *)

        (* method 1 *)
        val policy_thm_init = computeLib.RESTR_EVAL_CONV [“sem_tables”,“sem_policy”, “mv_dom_vars”] “correct_var_policy_var_tables_exec ^var_policy ^gen_var_table_auto ^policy_order ^get_i_policy ”;     
        val var_policy_var_table_thm = SIMP_RULE bool_ss [correct_var_policy_var_tables_exec_thm1] policy_thm_init;    



        (***********************)
        (*       STAGE 3       *)
        (***********************)   

        (* covert var table to interval table *)
        val only_var_table = fst (dest_pair gen_var_table_auto);
        val convert_to_interval = EVAL “convert_var_to_sinterval_tables ^only_var_table ^policy_me  ^test_pd_type”;   
        val only_interval_table1 = optionSyntax.dest_some(rhs (concl convert_to_interval));

            
        (* Theorem of correctness for conversion from var table to inteval table *)
        val var_table_sinterval_tbl_thm =
        REWRITE_RULE [convert_to_interval] (ISPECL[only_var_table, only_interval_table1, “0:num”, policy_me, test_pd_type ] correct_tables_from_var_to_sinterval_thm);        


                    
        (* to glue the theorems we need to take care of the conditions/ assumptions *)
                    
        (* condition1 *)                             
        val every_lval_in_me_in_type_thm = EVAL “every_lval_in_me_in_type ^test_pd_type ^policy_me”;
        val cond1_thm = REWRITE_RULE [every_lval_in_me_in_type_thm, policy_me_fst_distinct] (ISPECL[policy_me, test_pd_type ] lval_in_me_distinct_imp_cond1);

            
        (* condition2 *)         
        val in_order_then_in_me_thm = EVAL “in_order_then_in_me ^policy_order ^policy_me”;
        val ops_in_me_length_format_thm = EVAL “ops_in_me_length_format ^test_pd_type ^policy_me”;

        val cond2_thm = REWRITE_RULE [every_lval_in_me_in_type_thm, policy_me_fst_distinct,
                                    in_order_then_in_me_thm, ops_in_me_length_format_thm]
                                    (ISPECL[policy_me, test_pd_type, policy_order ]
                                            wf_format_imp_cond2);   
                                              
        (* condition3 *)     
        val cond3_thm = REWRITE_RULE [every_lval_in_me_in_type_thm, policy_me_fst_distinct,
                                    in_order_then_in_me_thm, ops_in_me_length_format_thm]
                                    (ISPECL[policy_me, test_pd_type]
                                            wf_format_imp_cond3);   

                                            
        val final_thm = prove(
          “! packet_input .
            wf_packet ^test_pd_type packet_input ⇒ 
            sem_arith_policy ^arith_policy packet_input = 
            sem_sinterval_tables (^only_interval_table1,0) packet_input”
          ,
          
          rpt strip_tac >>
              
          assume_tac arith_policy_var_policy_thm >>
          first_x_assum (strip_assume_tac o (Q.SPECL [‘packet_input’,‘(create_mv ^policy_me packet_input)’])) >>
          
          assume_tac var_policy_var_table_thm >>
          first_x_assum (strip_assume_tac o (Q.SPECL [‘(create_mv ^policy_me packet_input)’])) >>

          
          assume_tac var_table_sinterval_tbl_thm >>
          first_x_assum (strip_assume_tac o (Q.SPECL [‘packet_input’,‘(create_mv ^policy_me packet_input)’])) >>
              
          fs[cond1_thm, cond2_thm, cond3_thm]
        );

    in
    final_thm
    end;

end;


             
