structure fwd_proof_polcies_cakeLib :> fwd_proof_polcies_cakeLib = struct


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

    val _ = type_abbrev("action_policy_type", “:((string# num list) action_expr) policy”);
    val _ = type_abbrev("action_table_type", “:((string# num list) var_table_list # num)”);


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


    fun write_term_to_file (filename, term_string) =
       let
            val content = term_to_string term_string
            val outstream = TextIO.openOut filename
            val _ = TextIO.output(outstream, content)
            val _ = TextIO.closeOut outstream
        in
            ()
    end;


    fun check_two_polcies_eq (arith_policy1, arith_policy2, policy_me, test_pd_type, policy_order, file_name) =

        (* this function generates a proof that two policies are equivalent or not after deletion *)

        let

            val start_cpu_total = Timer.startCPUTimer ();
            val start_real_total = Timer.startRealTimer ();

            (***********************)
            (*       STAGE 1       *)
            (***********************)

            (*convert arith policy1 to var policy1 *)
            val arith_policy_eval1 = EVAL “convert_arith_to_var_policy ^arith_policy1 ^policy_me”;
            val var_policy1 = optionSyntax.dest_some (rhs (concl arith_policy_eval1));

            (*convert arith policy2 to var policy2 *)
            val arith_policy_eval2 = EVAL “convert_arith_to_var_policy ^arith_policy2 ^policy_me”;
            val var_policy2 = optionSyntax.dest_some (rhs (concl arith_policy_eval2));


            (* first establish distinction of domain and range of me*)
            val policy_me_fst_distinct = EVAL “ALL_DISTINCT (MAP FST ^policy_me)”;
            val policy_me_snd_distinct = EVAL “ALL_DISTINCT (MAP SND ^policy_me)”;

            val all_distinct_conj = CONJ policy_me_fst_distinct policy_me_snd_distinct;


            (* Theorem of correctness for conversion from arith policy to var policy *)

            (* thm for policy 1 *)
            val arith_policy_var_policy_thm1 = REWRITE_RULE[all_distinct_conj, arith_policy_eval1]
            (ISPECL[arith_policy1, var_policy1, policy_me] policy_airth_to_var_sem_conversion_correct);

            (* thm for policy 2 *)
            val arith_policy_var_policy_thm2 = REWRITE_RULE[all_distinct_conj, arith_policy_eval2]
            (ISPECL[arith_policy2, var_policy2, policy_me] policy_airth_to_var_sem_conversion_correct);

            val _ = time_stage ("Stage 1", start_cpu_total, start_real_total)

            (***********************)
            (*       STAGE 2       *)
            (***********************)

            val start_cpu_total_stage2_bdd = Timer.startCPUTimer ();
            val start_real_total_stage2_bdd = Timer.startRealTimer ();


            (************************************************************)
            (*       Fetch policy's BDD from the output text file       *)
            (************************************************************)
            (* 
            val _ = write_term_to_file ("../bdd_cake_test/policy_out_test.txt", var_policy);
            val _ = write_term_to_file ("../bdd_cake_test/order_out_test.txt", policy_order);
            *)

            val _ = write_term_to_file ("../bdd_cake_test/" ^ file_name ^ "_eq_policy1_out_test.txt", var_policy1);
            val _ = write_term_to_file ("../bdd_cake_test/" ^ file_name ^ "_eq_policy2_out_test.txt", var_policy2);

            val _ = write_term_to_file ("../bdd_cake_test/" ^ file_name ^ "_eq_order_out_test.txt", policy_order);

            val start_cpu_total_stage2_bdd1_start = Timer.startCPUTimer ();
            val start_real_total_stage2_bdd1_start = Timer.startRealTimer ();

            val status_exec_policy1 = OS.Process.system 
            ("cd ../bdd_cake_test/ && time ./test_bdd_policy.cake " ^ 
            file_name ^ "_eq_policy1_out_test.txt " ^ 
            file_name ^ "_eq_order_out_test.txt > " ^ 
            file_name ^ "_eq_bdd_policy1_cakeml_export.txt")

            val _ = if OS.Process.isSuccess status_exec_policy1
                    then print "Ja, policy1 BDD compilation completed\n"
                    else (print "Nej, policy1 NDD compilation failed\n";
                        OS.Process.exit OS.Process.failure)


            val _ = time_stage ("Stage 2 from vars policy 1 to BDDs", start_cpu_total_stage2_bdd1_start, start_real_total_stage2_bdd1_start)
            val start_cpu_total_stage2_bdd2_start = Timer.startCPUTimer ();
            val start_real_total_stage2_bdd2_start = Timer.startRealTimer ();



            val status_exec_policy2 = OS.Process.system 
            ("cd ../bdd_cake_test/ && time ./test_bdd_policy.cake " ^ 
            file_name ^ "_eq_policy2_out_test.txt " ^ 
            file_name ^ "_eq_order_out_test.txt > " ^ 
            file_name ^ "_eq_bdd_policy2_cakeml_export.txt")


            val _ = if OS.Process.isSuccess status_exec_policy2
                    then print "Ja, policy2 BDD compilation completed\n"
                    else (print "Nej, policy2 NDD compilation failed\n";
                        OS.Process.exit OS.Process.failure)

            val _ = time_stage ("Stage 2 from vars policy 2 to BDDs", start_cpu_total_stage2_bdd2_start, start_real_total_stage2_bdd2_start)
            val start_cpu_total_stage2_clean = Timer.startCPUTimer ();
            val start_real_total_stage2_clean = Timer.startRealTimer ();


            val filename_policy_export1 = "../bdd_cake_test/" ^ file_name ^ "_eq_bdd_policy1_cakeml_export.txt"
            val ins_policy1 = TextIO.openIn filename_policy_export1
            val policy_content_str1 = TextIO.inputAll ins_policy1;
            val _ = TextIO.closeIn ins_policy1;



            val filename_policy_export2 = "../bdd_cake_test/" ^ file_name ^ "_eq_bdd_policy2_cakeml_export.txt"
            val ins_policy2 = TextIO.openIn filename_policy_export2
            val policy_content_str2 = TextIO.inputAll ins_policy2;
            val _ = TextIO.closeIn ins_policy2;


            (*open Term;*)

            val policy_bdd_content_term1 = Parse.Term [QUOTE policy_content_str1];
             (* let
                    (* Clean the string by removing newlines and backslash escapes *)
                    fun clean s =
                        let
                            val chars = String.explode s
                            fun process [] = []
                            | process (#"\\" :: #"n" :: rest) = process rest  (* remove \n *)
                            | process (c :: rest) = c :: process rest
                        in
                            String.implode (process chars)
                        end

                    val cleaned = clean policy_content_str1
                    val parsed = Parse.Term [QUOTE cleaned]
                in
                    parsed
            end; *)


            val _ = print "AA:finished cleaning input1 \n";


            val policy_bdd_content_term2 = Parse.Term [QUOTE policy_content_str2];

            val _ = print "AA:finished cleaning input2 \n";

            val _ = time_stage ("Stage 2 finished cleaning", start_cpu_total_stage2_clean, start_real_total_stage2_clean)

            val start_cpu_total_stage2_iso = Timer.startCPUTimer ();
            val start_real_total_stage2_iso = Timer.startRealTimer ();

            (*******************************)
            (*       get isomorphisim      *)
            (*******************************)

                     
            val get_i_policy = bdd_utilsLib.pairBDDs (policy_bdd_content_term1, policy_bdd_content_term2);

            val _ = time_stage ("Stage 2 get isomorph", start_cpu_total_stage2_iso, start_real_total_stage2_iso)

            val start_cpu_total_stage2_proof = Timer.startCPUTimer ();
            val start_real_total_stage2_proof = Timer.startRealTimer ();


            (*******************************)
            (*    Make Stage 2 proof       *)
            (*******************************)

            val eval_policy_full_opt1 = mk_thm ( [], “mk_BDDPred_opt policy_structure (0,[],[(0, non_termn (NONE, ^var_policy1))]) [] ^policy_order 1 = SOME ^policy_bdd_content_term1 ”);
            val eval_policy_full_opt2 = mk_thm ( [], “mk_BDDPred_opt policy_structure (0,[],[(0, non_termn (NONE, ^var_policy2))]) [] ^policy_order 1 = SOME ^policy_bdd_content_term2 ”);


            val var_eq_thm_extract = REWRITE_CONV [correct_var_policy_var_policy_exec_def, eval_policy_full_opt1 , eval_policy_full_opt2] “correct_var_policy_var_policy_exec ^var_policy1 ^var_policy2 ^policy_order ^get_i_policy”;


            val var_eq_thm_extract_red = computeLib.RESTR_EVAL_RULE  [“correct_var_policy_var_policy_exec”, “sem_policy”,“sem_policy”, “mv_dom_vars”]  var_eq_thm_extract;
            val var_policy_var_table_thm = SIMP_RULE bool_ss [correct_var_policy_var_policy_exec_thm1] var_eq_thm_extract_red;

            val _ = time_stage ("Stage 2 proof", start_cpu_total_stage2_proof, start_real_total_stage2_proof)
            val _ = time_stage ("Stage 2 total", start_cpu_total_stage2_bdd, start_real_total_stage2_bdd)


            (***********************)
            (*       FINAL PROOF   *)
            (***********************)

            val start_cpu_final = Timer.startCPUTimer ();
            val start_real_final = Timer.startRealTimer ();

            (* to glue the theorems we need to take care of the conditions/ assumptions *)

            (* condition1 *)
            val every_lval_in_me_in_type_thm = EVAL “every_lval_in_me_in_type ^test_pd_type ^policy_me”;
            val cond1_thm = REWRITE_RULE [every_lval_in_me_in_type_thm, policy_me_fst_distinct] (ISPECL[policy_me, test_pd_type ] lval_in_me_distinct_imp_cond1);

            val _ = time_stage ("Stage 3 prepp for proof COND1 ", start_cpu_final, start_real_final)
            val start_cpu_final_1 = Timer.startCPUTimer ();
            val start_real_final_1 = Timer.startRealTimer ();


            (* condition2 *)
            val in_order_then_in_me_thm = EVAL “in_order_then_in_me ^policy_order ^policy_me”;
            val ops_in_me_length_format_thm = EVAL “ops_in_me_length_format ^test_pd_type ^policy_me”;

            val _ = time_stage ("Stage 3 prepp for proof COND2 ", start_cpu_final_1, start_real_final_1)
            val start_cpu_final_2 = Timer.startCPUTimer ();
            val start_real_final_2 = Timer.startRealTimer ();


            val cond2_thm = REWRITE_RULE [every_lval_in_me_in_type_thm, policy_me_fst_distinct,
                                        in_order_then_in_me_thm, ops_in_me_length_format_thm]
                                        (ISPECL[policy_me, test_pd_type, policy_order ]
                                                wf_format_imp_cond2);

            val _ = time_stage ("Stage 3 prepp for proof COND2 THM ", start_cpu_final_2, start_real_final_2)

            val _ = time_stage ("Stage 3 total prepping for proof", start_cpu_final, start_real_final)
            val start_cpu_final_p = Timer.startCPUTimer ();
            val start_real_final_p = Timer.startRealTimer ();


             val final_thm = prove(
            “! packet_input .
                wf_packet ^test_pd_type packet_input ⇒
                sem_arith_policy ^arith_policy1 packet_input =
                sem_arith_policy ^arith_policy2 packet_input”
            ,

            rpt strip_tac >>

            assume_tac arith_policy_var_policy_thm1 >>
            first_x_assum (strip_assume_tac o (Q.SPECL [‘packet_input’,‘(create_mv ^policy_me packet_input)’])) >>

            assume_tac arith_policy_var_policy_thm2 >>
            first_x_assum (strip_assume_tac o (Q.SPECL [‘packet_input’,‘(create_mv ^policy_me packet_input)’])) >>
                          
            assume_tac var_policy_var_table_thm >>
            first_x_assum (strip_assume_tac o (Q.SPECL [‘(create_mv ^policy_me packet_input)’])) >>
            fs[cond1_thm, cond2_thm] 
            );

            val _ = time_stage ("ONLY FINAL CORRECTNESS PROOF", start_cpu_final_p, start_real_final_p)

    in
    final_thm
    end;

end;
