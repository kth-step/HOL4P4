structure fwd_proof_cakeLib :> fwd_proof_cakeLib = struct


open HolKernel boolLib simpLib Parse bossLib pairLib;
open freq_func_in_fwdLib;

open listTheory;
open alistTheory;
open rich_listTheory;

open tables_specTheory;

open policy_arith_to_varTheory;
open table_arith_to_intervalTheory;

open bdd_end_to_endTheory;  


val _ = type_abbrev("action_table_type", “:((string# num list) var_table_list # num)”);


(* ---------------------------------------------------------------------------
   convert_arith_policy_to_interval_tables_cake

   Implements the POLYGRAM compilation pipeline (Purple Path, Figure 3),
   instantiated for input policy and output P4 tables, using CakeML
   binaries for MTBDD construction (Section VI).

   Delegates mk_mtbdd_opt to compiled CakeML executables
   (test_bdd_policy.cake and test_bdd_table.cake) rather than HOL4 EVAL,
   which is significantly faster for larger inputs (see Table II).
   MTBDD results are serialized to text files and read back into HOL4;
   this I/O is trusted via mk_oracle_thm (see Stage 2).

   Arguments:
     arith_policy      -- high-level forwarding policy with arithmetic
                          predicates over packet header fields (Sec. IV-B)
     policy_me         -- mapping m : variables -> atomic predicates,
                          connecting the policy language and its ILR (Sec. IV-A)
     test_pd_type      -- packet-field type descriptor encoding bit-vector
                          widths; needed for interval complements (Sec. IV-D)
     policy_full_order -- variable grouping G assigning variables to P4
                          tables (Sec. IV-D, Algorithm 3)
     policy_order      -- variable order x1,...,xn for mk_mtbdd_opt (Sec. V)
     file_name         -- base name for intermediate I/O files exchanged
                          with the CakeML binaries (TCB, Section VI)

   Returns:
    ORACLE |- !packet. wf_packet T packet =>
          sem_arith_policy policy packet =
          sem_sinterval_tables (tables, 0) packet
     (carries CakeML oracle tags reflecting the TCB serialization)
   --------------------------------------------------------------------------- *)

    fun convert_arith_policy_to_interval_tables_cake (arith_policy, policy_me, test_pd_type, policy_full_order, policy_order, file_name) =

    let

        val start_cpu_total = Timer.startCPUTimer ();
        val start_real_total = Timer.startRealTimer ();

        (****************************************************)
        (*  STAGE 1: Forward translation                    *)
        (*           arith policy -> policy ILR             *)
        (*           trans-fwd (Theorem 1 / Thm IF1)        *)
        (*                                                  *)
        (* The mapping m (policy_me) replaces each atomic   *)
        (* predicate with a fresh Boolean variable, giving  *)
        (* the policy ILR (var_policy). Theorem 1 proves    *)
        (* soundness of trans-fwd:                          *)
        (*   for every u ~_m packet,                        *)
        (*     sem-up(arith_policy) packet                  *)
        (*       = sem-down(var_policy) u                   *)
        (****************************************************)

        (* Apply trans-fwd: replace every atomic predicate in arith_policy
           with its corresponding variable in m (policy_me). *)
        val arith_policy_eval = EVAL “convert_arith_to_var_policy ^arith_policy ^policy_me”;
        val var_policy = optionSyntax.dest_some (rhs (concl arith_policy_eval));


        (* Establish distinctness of the domain (FST) and range (SND) of m.
           These are side conditions of Theorem 1 (Definition 1, Section IV-A),
           ensuring distinct variables map to distinct predicates. *)
        val policy_me_fst_distinct = EVAL “ALL_DISTINCT (MAP FST ^policy_me)”;
        val policy_me_snd_distinct = EVAL “ALL_DISTINCT (MAP SND ^policy_me)”;

        val all_distinct_conj = CONJ policy_me_fst_distinct policy_me_snd_distinct;


        (* Instantiate Theorem 1 (sound policy translation, Thm IF1):
             |- for every u ~_m packet,
                  sem-up(arith_policy) packet = sem-down(var_policy) u  *)
        val arith_policy_var_policy_thm = REWRITE_RULE[all_distinct_conj, arith_policy_eval]
        (ISPECL[arith_policy, var_policy, policy_me] policy_airth_to_var_sem_conversion_correct);

        val _ = time_stage ("Stage 1 (Policy to policy ILR)", start_cpu_total, start_real_total)

        (* Save the ILR Policy *) 
        val _ = save_thm("policy_trans_fwd", arith_policy_eval);
        (* Save the trans proof Policy Theorem 1 *)
        val _ = save_thm("policy_trans_fwd_proof", arith_policy_var_policy_thm); 

        (****************************************************)
        (*  STAGE 2: MTBDD construction and validation      *)
        (*           via CakeML binaries  (Theorems 3 & 4)  *)
        (*                                                  *)
        (* mk_mtbdd_opt runs as a verified CakeML binary    *)
        (* (Section VI) rather than inside HOL4 EVAL.      *)
        (* I/O serialization to/from text files is TCB;    *)
        (* see mk_oracle_thm below.                        *)
        (*                                                  *)
        (* 2a. policy ILR  -> MTBDD1  (CakeML binary)      *)
        (* 2b. MTBDD1      -> var table ILR  (untrusted SML)*)
        (* 2c. var table   -> MTBDD2  (CakeML binary)      *)
        (* 2d. MTBDD1 iso MTBDD2  (Theorem 4)              *)
        (****************************************************)



        val start_cpu_total_stage2 = Timer.startCPUTimer ();
        val start_real_total_stage2 = Timer.startRealTimer ();


        (* 2a. Serialize var_policy and policy_order to text files.
               These files are the input to the CakeML binary.
               Serialization/deserialization is part of the TCB (Section VI). *)
        val _ = write_term_to_file ("../bdd_cake_test/" ^ file_name ^ "_policy_out_test.txt", var_policy);
        val _ = write_term_to_file ("../bdd_cake_test/" ^ file_name ^ "_order_out_test.txt", policy_order);

        val _ = time_stage ("Stage 2 prepp policy ", start_cpu_total_stage2, start_real_total_stage2)

        val start_cpu_total_stage2a = Timer.startCPUTimer ();
        val start_real_total_stage2a = Timer.startRealTimer ();


        (* Run the verified CakeML binary test_bdd_policy.cake to build MTBDD1.
           The binary implements mk_mtbdd_opt (Theorem 3, Section V), compiled
           via CakeML verified compilation (Section VI).
           The result is written to a text file for deserialization back into HOL4. *)
        val status_exec_policy = OS.Process.system 
        ("cd ../bdd_cake_test/ && ./test_bdd_policy.cake " ^ 
        file_name ^ "_policy_out_test.txt " ^ 
        file_name ^ "_order_out_test.txt > " ^ 
        file_name ^ "_bdd_policy_cakeml_export.txt")


        val _ = if OS.Process.isSuccess status_exec_policy
        then print "Ja, policy BDD compilation completed\n"
        else (print "Nej, policy BDD compilation failed\n";
        OS.Process.exit OS.Process.failure)

        val _ = time_stage ("Stage 2 (Policy MTBDD) ", start_cpu_total_stage2a, start_real_total_stage2a)
        val start_cpu_total_stage2b = Timer.startCPUTimer ();
        val start_real_total_stage2b = Timer.startRealTimer ();


        (* Deserialize MTBDD1 from the CakeML output file back into a HOL4 term.
           This deserialization is part of the TCB (Section VI). *)
        val filename_policy_export = "../bdd_cake_test/" ^ file_name ^ "_bdd_policy_cakeml_export.txt"
        val ins_policy = TextIO.openIn filename_policy_export
        val policy_content_str = TextIO.inputAll ins_policy;
        val _ = TextIO.closeIn ins_policy;

        val policy_bdd_content_term = Parse.Term [QUOTE policy_content_str];

        val _ = print "Note:finished cleaning input \n";


        (* 2b. Run the untrusted MTBDD-to-table algorithm (Section IV-E, SML).
               bdd_to_tables_iterative traverses MTBDD1 and produces a candidate
               var table ILR (gen_var_table_auto). This step is untrusted;
               its correctness is validated a posteriori by step 2d. *)
        val test_groupings = rhs(concl(EVAL policy_full_order));
        val gen_var_table_auto = bdd_utilsLib.bdd_to_tables_iterative policy_bdd_content_term test_groupings;

        val _ = print "Note:finished creating table \n";


        (* 2c. Serialize the candidate var table ILR to a text file and run
               test_bdd_table.cake to build MTBDD2.
               As with MTBDD1, serialization/deserialization is part of the TCB. *)
        val _ = write_term_to_file ("../bdd_cake_test/" ^ file_name ^ "_table_out_test.txt", gen_var_table_auto)

        val _ = time_stage ("Stage 2 prepp tables ", start_cpu_total_stage2b, start_real_total_stage2b)
        val start_cpu_total_stage2c = Timer.startCPUTimer ();
        val start_real_total_stage2c = Timer.startRealTimer ();

        val _ = OS.Process.system 
        ("cd ../bdd_cake_test/ && ./test_bdd_table.cake " ^ 
        file_name ^ "_table_out_test.txt " ^ 
        file_name ^ "_order_out_test.txt > " ^ 
        file_name ^ "_bdd_table_cakeml_export.txt");


        (* val _ = if OS.Process.isSuccess status_exec_table
        then print "Ja, table BDD compilation completed\n"
        else (print "Nej, table BDD compilation failed\n";
        OS.Process.exit OS.Process.failure) *)


        val _ = time_stage ("Stage 2 (Table MTBDD) ", start_cpu_total_stage2c, start_real_total_stage2c)


        (* Deserialize MTBDD2 from the CakeML output file back into a HOL4 term.
           This deserialization is part of the TCB (Section VI). *)
        val filename_policy_export = "../bdd_cake_test/" ^ file_name ^ "_bdd_table_cakeml_export.txt"
        val ins_tbl = TextIO.openIn filename_policy_export
        val tbl_content_str = TextIO.inputAll ins_tbl;
        val _ = TextIO.closeIn ins_tbl;

        val _ = print "Note:finished getting sexp table to hol4 \n";


        val table_bdd_content_term = Parse.Term [QUOTE tbl_content_str];

        val _ = print "Note:finished cleaning sexp table in hol4 \n";


        (* 2d. Check isomorphism between MTBDD1 and MTBDD2.
               pairBDDs computes the candidate isomorphism witness I. *)
        val get_i_policy = bdd_utilsLib.pairBDDs (policy_bdd_content_term, table_bdd_content_term);

        val start_cpu_total_stage2_proof = Timer.startCPUTimer ();
        val start_real_total_stage2_proof = Timer.startRealTimer ();


        val _ = (show_tags := true);

        (* !!!!!!!!!!!!!!!!!!!!!!!!!!!!
           mk_oracle_thm introduces the CakeML MTBDD results as axioms tagged
           with "CakeML_policy_TCB" and "CakeML_table_TCB" respectively.
           This is necessary because the serialization and deserialization of
           HOL4 terms to/from the CakeML binary I/O files is not verified and
           constitutes of this pipeline variant (Section VI).  
           The mk_mtbdd_opt function itself IS VERIFIED via
           CakeML verified compilation, but we cannot prove inside HOL4 that
           the text file roundtrip faithfully represents the MTBDD term.
           The oracle tags make this trust assumption explicit and visible
           in the final theorem. *)
        val CakeML_policy_TCB_thm = mk_oracle_thm "CakeML_policy_TCB";
        val CakeML_table_TCB_thm = mk_oracle_thm "CakeML_table_TCB";

        val eval_policy_full_opt = CakeML_policy_TCB_thm ([], “mk_BDDPred_opt policy_structure (0,[],[(0, non_termn (NONE, ^var_policy))]) [] ^policy_order 1 = SOME ^policy_bdd_content_term ”);

        val eval_table_full_opt_auto = CakeML_table_TCB_thm ([], “mk_BDDPred_opt table_structure (0,[],[(0, non_termn (NONE, ^gen_var_table_auto))]) [] ^policy_order 1 = SOME ^table_bdd_content_term ”);        

        (* val _ = print_thm eval_table_full_opt_auto *)

        (* Complete the isomorphism check and lift to semantic equivalence
           via Theorem 4:  |- sem(MTBDD1) = sem(MTBDD2).
           Compilation correctness is thus reduced to MTBDD equivalence
           checking, independently of the untrusted algorithm in 2b. *)

        val var_eq_thm_extract = REWRITE_CONV [correct_var_policy_var_tables_exec_def, eval_policy_full_opt , eval_table_full_opt_auto] “correct_var_policy_var_tables_exec ^var_policy ^gen_var_table_auto ^policy_order ^get_i_policy”;

        val var_eq_thm_extract_red = computeLib.RESTR_EVAL_RULE  [“correct_var_policy_var_tables_exec”, “sem_tables”,“sem_policy”, “mv_dom_vars”]  var_eq_thm_extract;

        val var_policy_var_table_thm = SIMP_RULE bool_ss [correct_var_policy_var_tables_exec_thm1] var_eq_thm_extract_red;


        val _ = time_stage ("Stage 2 proof", start_cpu_total_stage2_proof, start_real_total_stage2_proof)
        val _ = time_stage ("Stage 2 total", start_cpu_total_stage2, start_real_total_stage2)


        (* Save the Policy BDD *) 
        val _ = save_thm("policy_BDD", eval_policy_full_opt);
        (* Save the Table BDD *)
        val _ = save_thm("table_BDD", eval_table_full_opt_auto);


        (****************************************************)
        (*  STAGE 3: Back translation  (Theorem 2 / OF2)    *)
        (*           var table ILR -> interval tables       *)
        (*                                                  *)
        (* trans-back converts each Boolean row constraint  *)
        (* to a closed bit-vector interval using m and      *)
        (* field widths in test_pd_type (Section IV-D):     *)
        (*   for every u ~_m packet,                        *)
        (*     sem-down(var_table) u                        *)
        (*       = sem-up(interval_table) packet            *)
        (****************************************************)

        val start_cpu_total_stage3 = Timer.startCPUTimer ();
        val start_real_total_stage3 = Timer.startRealTimer ();

        (* Apply trans-back: convert the var table ILR to concrete P4 interval
           tables. only_var_table extracts the table component from the pair
           returned by the untrusted algorithm. *)
        val only_var_table = fst (dest_pair gen_var_table_auto);
        val convert_to_interval = EVAL “convert_var_to_sinterval_tables ^only_var_table ^policy_me  ^test_pd_type”;
        val only_interval_table1 = optionSyntax.dest_some(rhs (concl convert_to_interval));


        (* Instantiate Theorem 2 (sound table retranslation, Thm OF2):
             |- for every u ~_m packet,
                  sem-down(var_table) u = sem-up(interval_table) packet  *)
        val var_table_sinterval_tbl_thm =
        REWRITE_RULE [convert_to_interval] (ISPECL[only_var_table, only_interval_table1, “0:num”, policy_me, test_pd_type ] correct_tables_from_var_to_sinterval_thm);

        val _ = time_stage ("Stage 3 (Table ILR to P4 table)", start_cpu_total_stage3, start_real_total_stage3)


        (* Save the trans Table *)
        val _ = save_thm("table_trans_back", convert_to_interval);
        (* Save the trans proof Table Theorem 2 *)
        val _ = save_thm("table_trans_fwd_proof", var_table_sinterval_tbl_thm); 



        (****************************************************)
        (*  FINAL PROOF: End-to-end semantic equivalence    *)
        (*                                                  *)
        (* Composes Thm 1 (IF1), Thms 3+4, Thm 2 (OF2):     *)
        (*  ORACLE |- !packet. wf_packet T packet =>        *)
        (*        sem_arith_policy policy packet =          *)
        (*        sem_sinterval_tables (tables,0) packet    *)
        (*                                                  *)
        (* Carries oracle tags CakeML_policy_TCB and        *)
        (* CakeML_table_TCB (I/O serialization is TCB).     *)
        (* cond1-cond3: well-formedness of m and order.     *)
        (****************************************************)

        val start_cpu_final = Timer.startCPUTimer ();
        val start_real_final = Timer.startRealTimer ();


        (* cond1: every left-value in m appears in the type descriptor,
                  and the keys of m are distinct (Section IV-A). *)
        val every_lval_in_me_in_type_thm = EVAL “every_lval_in_me_in_type ^test_pd_type ^policy_me”;
        val cond1_thm = REWRITE_RULE [every_lval_in_me_in_type_thm, policy_me_fst_distinct] (ISPECL[policy_me, test_pd_type ] lval_in_me_distinct_imp_cond1);


        (* cond2: the variable order is consistent with m, and the type
                  descriptor correctly encodes the bit-vector widths of
                  all header fields. *)
        val in_order_then_in_me_thm = EVAL “in_order_then_in_me ^policy_order ^policy_me”;
        val ops_in_me_length_format_thm = EVAL “ops_in_me_length_format ^test_pd_type ^policy_me”;

        val cond2_thm = REWRITE_RULE [every_lval_in_me_in_type_thm, policy_me_fst_distinct,
        in_order_then_in_me_thm, ops_in_me_length_format_thm]
        (ISPECL[policy_me, test_pd_type, policy_order ]
        wf_format_imp_cond2);

        (* cond3: same well-formedness conditions required by trans-back
                  to produce valid interval complements (Section IV-D). *)
        val cond3_thm = REWRITE_RULE [every_lval_in_me_in_type_thm, policy_me_fst_distinct,
        in_order_then_in_me_thm, ops_in_me_length_format_thm]
        (ISPECL[policy_me, test_pd_type]
        wf_format_imp_cond3);


        (* Prove the end-to-end theorem by chaining all stage theorems
           via the shared valuation (create_mv policy_me packet).
           fs discharges remaining goals using cond1-cond3. *)
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

        val _ = time_stage ("Final glue proof", start_cpu_final, start_real_final)
        (* val _ = write_term_to_file ( file_name ^ "_table_out.txt", only_interval_table1); *)

        (* save final proof *)
        val _ = save_thm("final_proof", final_thm);

    in
    final_thm
    end;

end;