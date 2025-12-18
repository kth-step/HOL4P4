structure sptrees_fwd_proofLib :> sptrees_fwd_proofLib = struct


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
open apply_trans_to_IOLib;
 

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



    fun sptrees_convert_arith_policy_to_interval_tables (arith_policy, policy_me, test_pd_type, policy_full_order, policy_order) =

        let
            
            val start_cpu_total = Timer.startCPUTimer ();
            val start_real_total = Timer.startRealTimer (); 

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

            val _ = time_stage ("Stage 1", start_cpu_total, start_real_total) 

            (***********************)
            (*       STAGE 2       *)
            (***********************)


            val start_cpu_total_stage2 = Timer.startCPUTimer ();
            val start_real_total_stage2 = Timer.startRealTimer (); 

            val (final_policy_bdd, tbl, final_table_bdd) =
            apply_trans_to_IOLib.sptrees_gen_bdds_policy_and_table (var_policy, policy_order, policy_full_order);



            val get_i_policy = bdd_utilsLib.pairBDDs (final_policy_bdd, final_table_bdd);


            val eval_policy_full_opt = mk_thm ( [], “mk_BDDPred_opt policy_structure (0,[],[(0, non_termn (NONE, ^var_policy))]) [] ^policy_order 1 = SOME ^final_policy_bdd”);
            val eval_table_full_opt_auto = mk_thm ( [], “mk_BDDPred_opt table_structure (0,[],[(0, non_termn (NONE, ^tbl))]) [] ^policy_order 1 = SOME ^final_table_bdd ”);

            val start_cpu_total_stage2_proof = Timer.startCPUTimer ();
            val start_real_total_stage2_proof = Timer.startRealTimer (); 

            val var_eq_thm_extract = REWRITE_CONV [correct_var_policy_var_tables_exec_def, eval_policy_full_opt , eval_table_full_opt_auto] “correct_var_policy_var_tables_exec ^var_policy ^tbl ^policy_order ^get_i_policy”;
            val var_eq_thm_extract_red = computeLib.RESTR_EVAL_RULE  [“correct_var_policy_var_tables_exec”, “sem_tables”,“sem_policy”, “mv_dom_vars”]  var_eq_thm_extract;
            val var_policy_var_table_thm = SIMP_RULE bool_ss [correct_var_policy_var_tables_exec_thm1] var_eq_thm_extract_red;

            val _ = time_stage ("Stage 2 proof", start_cpu_total_stage2_proof, start_real_total_stage2_proof) 
            val _ = time_stage ("Stage 2 total", start_cpu_total_stage2, start_real_total_stage2) 

            val start_cpu_total_stage3 = Timer.startCPUTimer ();
            val start_real_total_stage3 = Timer.startRealTimer (); 

            (***********************)
            (*       STAGE 3       *)
            (***********************)

            (* covert var table to interval table *)
            val only_var_table = fst (dest_pair tbl);
            val convert_to_interval = EVAL “convert_var_to_sinterval_tables ^only_var_table ^policy_me  ^test_pd_type”;
            val only_interval_table1 = optionSyntax.dest_some(rhs (concl convert_to_interval));


            (* Theorem of correctness for conversion from var table to inteval table *)
            val var_table_sinterval_tbl_thm =
            REWRITE_RULE [convert_to_interval] (ISPECL[only_var_table, only_interval_table1, “0:num”, policy_me, test_pd_type ] correct_tables_from_var_to_sinterval_thm);

            val _ = time_stage ("Stage 3 total", start_cpu_total_stage3, start_real_total_stage3) 





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

            val _ = time_stage ("FINAL CORRECTNESS PROOF", start_cpu_final, start_real_final) 

    in
    eval_table_full_opt_auto (*final_thm*)
    end;

end;