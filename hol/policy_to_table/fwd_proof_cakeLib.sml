structure fwd_proof_cakeLib :> fwd_proof_cakeLib = struct


open HolKernel boolLib simpLib Parse bossLib pairLib;

open listTheory;
open alistTheory;
open rich_listTheory;

open tables_specTheory;

open policy_arith_to_varTheory;
open table_arith_to_intervalTheory;

open bdd_end_to_endTheory;  


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


    fun convert_arith_policy_to_interval_tables_cake (arith_policy, policy_me, test_pd_type, policy_full_order, policy_order, file_name) =

       (* this compiles the input with cakeML It takes a very longer time, so I created a parser in CakeML, This should be in fwd_proof_cakeLib file*)


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

            val _ = time_stage ("Stage 1 for 2 BDDs ", start_cpu_total, start_real_total)

            (***********************)
            (*       STAGE 2       *)
            (***********************)

            val start_cpu_total_stage2 = Timer.startCPUTimer ();
            val start_real_total_stage2 = Timer.startRealTimer ();


            (************************************************************)
            (*       Fetch policy's BDD from the output text file       *)
            (************************************************************)
            (* 
            val _ = write_term_to_file ("../bdd_cake_test/policy_out_test.txt", var_policy);
            val _ = write_term_to_file ("../bdd_cake_test/order_out_test.txt", policy_order);
            *)



            val _ = write_term_to_file ("../bdd_cake_test/" ^ file_name ^ "_policy_out_test.txt", var_policy);
            val _ = write_term_to_file ("../bdd_cake_test/" ^ file_name ^ "_order_out_test.txt", policy_order);

            val _ = time_stage ("Stage 2 prepp policy ", start_cpu_total_stage2, start_real_total_stage2)

            val start_cpu_total_stage2a = Timer.startCPUTimer ();
            val start_real_total_stage2a = Timer.startRealTimer ();


            val status_exec_policy = OS.Process.system 
            ("cd ../bdd_cake_test/ && time ./test_bdd_policy.cake " ^ 
            file_name ^ "_policy_out_test.txt " ^ 
            file_name ^ "_order_out_test.txt > " ^ 
            file_name ^ "_bdd_policy_cakeml_export.txt")


            val _ = if OS.Process.isSuccess status_exec_policy
                    then print "Ja, policy BDD compilation completed\n"
                    else (print "Nej, policy NDD compilation failed\n";
                        OS.Process.exit OS.Process.failure)

            val _ = time_stage ("Stage 2 from var policy to BDD ", start_cpu_total_stage2a, start_real_total_stage2a)
            val start_cpu_total_stage2b = Timer.startCPUTimer ();
            val start_real_total_stage2b = Timer.startRealTimer ();



            val filename_policy_export = "../bdd_cake_test/" ^ file_name ^ "_bdd_policy_cakeml_export.txt"
            val ins_policy = TextIO.openIn filename_policy_export
            val policy_content_str = TextIO.inputAll ins_policy;
            val _ = TextIO.closeIn ins_policy;

            (*open Term;*)

            val policy_bdd_content_term = Parse.Term [QUOTE policy_content_str];

            val _ = print "AA:finished cleaning input \n";



            (************************************************************)
            (*            Generate a table using sml function           *)
            (************************************************************)

            val test_groupings = rhs(concl(EVAL policy_full_order));
            val gen_var_table_auto = bdd_utilsLib.bdd_to_tables_iterative policy_bdd_content_term test_groupings;

            val _ = print "AA:finished creating table \n";

            (**********************************************************)
            (*          prepp table:  translation to CakeML           *)
            (**********************************************************)

           val _ = write_term_to_file ("../bdd_cake_test/" ^ file_name ^ "_table_out_test.txt", gen_var_table_auto)

            val _ = time_stage ("Stage 2 prepp tables ", start_cpu_total_stage2b, start_real_total_stage2b)
            val start_cpu_total_stage2c = Timer.startCPUTimer ();
            val start_real_total_stage2c = Timer.startRealTimer ();

            val status_exec_table = OS.Process.system 
                            ("cd ../bdd_cake_test/ && time ./test_bdd_table.cake " ^ 
                            file_name ^ "_table_out_test.txt " ^ 
                            file_name ^ "_order_out_test.txt > " ^ 
                            file_name ^ "_bdd_table_cakeml_export.txt");


            val _ = if OS.Process.isSuccess status_exec_table
                    then print "Ja, table BDD compilation completed\n"
                    else (print "Nej, table NDD compilation failed\n";
                        OS.Process.exit OS.Process.failure)


            val _ = time_stage ("Stage 2 from table to BDD ", start_cpu_total_stage2c, start_real_total_stage2c)


            val filename_policy_export = "../bdd_cake_test/" ^ file_name ^ "_bdd_table_cakeml_export.txt"
            val ins_tbl = TextIO.openIn filename_policy_export
            val tbl_content_str = TextIO.inputAll ins_tbl;
            val _ = TextIO.closeIn ins_tbl;

            val _ = print "AA:finished getting sexp table to hol4 \n";


            val table_bdd_content_term = Parse.Term [QUOTE tbl_content_str];

            val _ = print "AA:finished cleaning sexp table in hol4 \n";


                        
            val get_i_policy = bdd_utilsLib.pairBDDs (policy_bdd_content_term, table_bdd_content_term);

            val start_cpu_total_stage2_proof = Timer.startCPUTimer ();
            val start_real_total_stage2_proof = Timer.startRealTimer ();

            val eval_policy_full_opt = mk_thm ( [], “mk_BDDPred_opt policy_structure (0,[],[(0, non_termn (NONE, ^var_policy))]) [] ^policy_order 1 = SOME ^policy_bdd_content_term ”);
            val eval_table_full_opt_auto = mk_thm ( [], “mk_BDDPred_opt table_structure (0,[],[(0, non_termn (NONE, ^gen_var_table_auto))]) [] ^policy_order 1 = SOME ^table_bdd_content_term ”);


            val var_eq_thm_extract = REWRITE_CONV [correct_var_policy_var_tables_exec_def, eval_policy_full_opt , eval_table_full_opt_auto] “correct_var_policy_var_tables_exec ^var_policy ^gen_var_table_auto ^policy_order ^get_i_policy”;
            val var_eq_thm_extract_red = computeLib.RESTR_EVAL_RULE  [“correct_var_policy_var_tables_exec”, “sem_tables”,“sem_policy”, “mv_dom_vars”]  var_eq_thm_extract;
            val var_policy_var_table_thm = SIMP_RULE bool_ss [correct_var_policy_var_tables_exec_thm1] var_eq_thm_extract_red;


(*
val isIsomorph_exec_thm = mk_thm ( [], “isIsomorph_exec ^get_i_policy ^policy_bdd_content_term
                                                              ^table_bdd_content_term”);


val assumption1 = mk_thm ( [], “ALOOKUP ^get_i_policy 0 = SOME 0”);    
val assumption2 = mk_thm ( [], “node_in_BDD 0 ^policy_bdd_content_term”);
val assumption3 = mk_thm ( [],  “node_in_BDD 0 ^table_bdd_content_term”);
val assumption4 = mk_thm ( [],  “prop_in_BDD 0 ^policy_bdd_content_term = SOME ^var_policy”);
val assumption5 = mk_thm ( [],  “prop_in_BDD 0 ^table_bdd_content_term = SOME ^gen_var_table_auto”);
val assumption6 = mk_thm ( [],  “fv_in_vars_exec <|sem := sem_tables; sub := mk_substitute_tables;
         simp := simp_tables_wrapper; final := final_tables;
         fv := fv_tables|> ^gen_var_table_auto ^policy_order”);
val assumption7 = mk_thm ( [],  “fv_in_vars_exec
                                 <|sem := sem_policy; sub := mk_substitute_policy; simp := simp_policy;
         final := final_policy; fv := fv_policy|> ^var_policy ^policy_order”);
val assumption8 = mk_thm ( [],  “ALL_DISTINCT ^policy_order”);
val assumption9 = mk_thm ( [],  “^var_policy ≠ []”);
val assumption10 = mk_thm ( [],  “SOME ^var_policy = SOME ^var_policy”);
val assumption11 = mk_thm ( [],  “SOME ^gen_var_table_auto = SOME ^gen_var_table_auto”);

val var_eq_thm_extract = REWRITE_CONV [
    correct_var_policy_var_tables_exec_def, eval_policy_full_opt , eval_table_full_opt_auto] “correct_var_policy_var_tables_exec ^var_policy ^gen_var_table_auto ^policy_order ^get_i_policy”;

                                        
val var_eq_thm_extract_red = computeLib.RESTR_EVAL_RULE
                                       [“correct_var_policy_var_tables_exec”, “sem_tables”,“sem_policy”, “mv_dom_vars”,
                                        “isIsomorph_exec”, “node_in_BDD”, “prop_in_BDD”, “ALL_DISTINCT”, “fv_in_vars_exec”]  var_eq_thm_extract;

                                        
val var_policy_var_table_thm = REWRITE_RULE [correct_var_policy_var_tables_exec_thm1,
                                                  assumption1, assumption2,
                                                  assumption3, assumption4, assumption5, assumption6,
                                                  assumption7, assumption8, assumption9, assumption10, assumption11,
                                                  isIsomorph_exec_thm] (var_eq_thm_extract_red)




*)
            val _ = time_stage ("Stage 2 full proof", start_cpu_total_stage2_proof, start_real_total_stage2_proof)
            val _ = time_stage ("Stage 2 total", start_cpu_total_stage2, start_real_total_stage2)


            (***********************)
            (*       STAGE 3       *)
            (***********************)

            val start_cpu_total_stage3 = Timer.startCPUTimer ();
            val start_real_total_stage3 = Timer.startRealTimer ();

            (* covert var table to interval table *)
            val only_var_table = fst (dest_pair gen_var_table_auto);
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
    final_thm
    end;

end;
