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

        

    fun time_stage (stage_name, timer_cpu, timer_real) = 
        let
            val cpu_time = Timer.checkCPUTimer timer_cpu
            val real_time = Timer.checkRealTimer timer_real
            val _ = HOL_MESG (stage_name ^ " completed in: " ^ 
                          Time.toString (#usr cpu_time) ^ " user, " ^ 
                          Time.toString (#sys cpu_time) ^ " system, " ^ 
                          Time.toString real_time ^ " real\n")
        in
            (cpu_time, real_time)
        end



    fun convert_arith_policy_to_interval_tables (arith_policy, policy_me, test_pd_type, policy_full_order, policy_order) =

    let
            
    val start_cpu_total = Timer.startCPUTimer ();
    val start_real_total = Timer.startRealTimer ();


        (***********************)
        (*       STAGE 1       *)
        (***********************)

        val start_cpu_stage1 = Timer.startCPUTimer ();
        val start_real_stage1 = Timer.startRealTimer ();


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


        val _ = time_stage ("Stage 1", start_cpu_stage1, start_real_stage1)


        (***********************)
        (*       STAGE 2       *)
        (***********************)
                              

        val start_cpu_stage2 = Timer.startCPUTimer ();
        val start_real_stage2 = Timer.startRealTimer ();


        (* create BDD of var policy  *)
        val eval_policy_full_opt = EVAL “mk_BDDPred_opt_new policy_structure (0,[],[(0, non_termn (NONE, ^var_policy))]) [] ^policy_order 1”;
        val eval_policy_full_opt_rhs = optionSyntax.dest_some (rhs (concl eval_policy_full_opt));

        val _ = time_stage ("Stage 2 from var policy to BDD", start_cpu_stage2, start_real_stage2);
        val start_cpu_stage2_vbdd = Timer.startCPUTimer ();
        val start_real_stage2_vbdd = Timer.startRealTimer ();

        (* automatically generate a var table from the var policy's BDD via sml*)
        val test_groupings = rhs(concl(EVAL policy_full_order));
        val gen_var_table_auto = bdd_utilsLib.bdd_to_tables_iterative eval_policy_full_opt_rhs test_groupings;

            
        val _ = time_stage ("Stage 2 from var BDD to table", start_cpu_stage2_vbdd, start_real_stage2_vbdd);
        val start_cpu_stage2_tbl = Timer.startCPUTimer ();
        val start_real_stage2_tbl = Timer.startRealTimer ();

        (* now create a BDD for the table*)    
        (*val eval_table_full_opt_auto = EVAL “mk_BDDPred_opt table_structure (0,[],[(0, non_termn (NONE, ^gen_var_table_auto))]) [] ^policy_order 1”;
        val eval_table_full_opt_auto_rhs = optionSyntax.dest_some (rhs (concl eval_table_full_opt_auto));
*)

        val eval_table_full_opt_auto = EVAL “mk_BDDPred_opt_new table_structure_new (0,[],[(0, non_termn (NONE, ^gen_var_table_auto))]) [] ^policy_order 1”;
        val eval_table_full_opt_auto_rhs = optionSyntax.dest_some (rhs (concl eval_table_full_opt_auto));
            
        val _ = time_stage ("Stage 2 from table to table BDD", start_cpu_stage2_tbl, start_real_stage2_tbl);
        val start_cpu_stage2_tbdd = Timer.startCPUTimer ();
        val start_real_stage2_tbdd = Timer.startRealTimer ();

        (* get I (pairs isomorphic in the graph), and check if isisIsomorph *)
        val get_i_policy = bdd_utilsLib.pairBDDs (eval_policy_full_opt_rhs, eval_table_full_opt_auto_rhs);
        (*val is_tbl_policy1_iso = EVAL “isIsomorph_exec ^get_i_policy ^eval_policy_full_opt_rhs
                                                                      ^eval_table_full_opt_auto_rhs”;
        *)


            
        (* Theorem of correctness for conversion from var policy to var table *)
(*
        val policy_thm_init = computeLib.RESTR_EVAL_CONV [“sem_tables”,“sem_policy”, “mv_dom_vars”] “correct_var_policy_var_tables_exec ^var_policy ^gen_var_table_auto ^policy_order ^get_i_policy ”;     
        val var_policy_var_table_thm = SIMP_RULE bool_ss [correct_var_policy_var_tables_exec_thm1] policy_thm_init;    
*)
       
(*
        val policy_thm_init = computeLib.RESTR_EVAL_CONV [“sem_tables”,“sem_policy”, “mv_dom_vars”] “correct_var_policy_var_tables_exec2 ^var_policy ^gen_var_table_auto ^policy_order ^get_i_policy ”;     
        val var_policy_var_table_thm = SIMP_RULE bool_ss [correct_var_policy_var_tables_exec2_thm1] policy_thm_init;
*)


        val isIsomorph_exec_thm = EVAL “isIsomorph_exec ^get_i_policy ^eval_policy_full_opt_rhs
                                                              ^eval_table_full_opt_auto_rhs”;
        val assumption1 = EVAL “ALOOKUP ^get_i_policy 0 = SOME 0”;    
        val assumption2 = EVAL “node_in_BDD 0 ^eval_policy_full_opt_rhs”;
        val assumption3 = EVAL “node_in_BDD 0 ^eval_table_full_opt_auto_rhs”;
        val assumption4 = EVAL “prop_in_BDD 0 ^eval_policy_full_opt_rhs = SOME ^var_policy”;
        val assumption5 = EVAL “prop_in_BDD 0 ^eval_table_full_opt_auto_rhs = SOME ^gen_var_table_auto”;
        val assumption6 = EVAL “fv_in_vars_exec table_structure_new ^gen_var_table_auto ^policy_order”;
        val assumption7 = EVAL “fv_in_vars_exec policy_structure ^var_policy ^policy_order”;
        val assumption8 = EVAL “ALL_DISTINCT ^var_policy”;
        val assumption9 = EVAL “^var_policy ≠ []”;


        val var_policy_var_table_thm = prove (“ ∀mv.
                                        mv_dom_vars mv ^policy_order  ⇒
                                        sem_policy ^var_policy  mv = sem_tables ^gen_var_table_auto mv ”,
        assume_tac (INST_TYPE [“:'a” |-> “:(string#num list)”] correct_var_policy_var_tables_exec2_thm1)  >>
        first_x_assum (strip_assume_tac o (SPECL [var_policy, gen_var_table_auto, policy_order, get_i_policy])) >>

        gvs[correct_var_policy_var_tables_exec2_def, eval_policy_full_opt, eval_table_full_opt_auto] >>
        gvs[assumption1, assumption2, assumption3, assumption4, assumption5, assumption6,
            assumption7, assumption8, assumption9, isIsomorph_exec_thm]
        );




        val _ = time_stage ("Stage 2 proof", start_cpu_stage2_tbdd, start_real_stage2_tbdd);

        val _ = time_stage ("Stage 2 total", start_cpu_stage2, start_real_stage2);



        (***********************)
        (*       STAGE 3       *)
        (***********************)   

        val start_cpu_stage3 = Timer.startCPUTimer ();
        val start_real_stage3 = Timer.startRealTimer ();


        (* covert var table to interval table *)
        val only_var_table = fst (dest_pair gen_var_table_auto);
        val convert_to_interval = EVAL “convert_var_to_sinterval_tables ^only_var_table ^policy_me  ^test_pd_type”;   
        val only_interval_table1 = optionSyntax.dest_some(rhs (concl convert_to_interval));

            
        (* Theorem of correctness for conversion from var table to inteval table *)
        val var_table_sinterval_tbl_thm =
        REWRITE_RULE [convert_to_interval] (ISPECL[only_var_table, only_interval_table1, “0:num”, policy_me, test_pd_type ] correct_tables_from_var_to_sinterval_thm);        

        val _ = time_stage ("Stage 3", start_cpu_stage3, start_real_stage3);




        (***********************)
        (*       FINAL PROOF   *)
        (***********************)
        val start_cpu_final = Timer.startCPUTimer ();
        val start_real_final = Timer.startRealTimer ();

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


        val _ = time_stage ("Final glue proof", start_cpu_final, start_real_final);

        val _ = time_stage ("Total time of everything", start_cpu_total, start_real_total);



    in
    final_thm
    end;

end;


             
