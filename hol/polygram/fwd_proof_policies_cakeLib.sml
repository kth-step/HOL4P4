structure fwd_proof_polcies_cakeLib :> fwd_proof_polcies_cakeLib = struct

open HolKernel boolLib simpLib Parse bossLib pairLib;
open freq_func_in_fwdLib;

open listTheory;
open alistTheory;
open rich_listTheory;

open tables_specTheory;

open policy_arith_to_varTheory;
open table_arith_to_intervalTheory;

open bdd_end_to_endTheory;  


(* ---------------------------------------------------------------------------
   check_two_polcies_eq

   Implements certified policy equivalence checking (Section VII),
   the orange path,
   reusing the same MTBDD construction as the compilation pipeline.

   Both input policies are independently translated to their policy ILRs
   (Theorem 1 / Thm IF1 twice), and their MTBDDs are built via the verified
   CakeML binary (Theorem 3). Semantic equivalence is then certified by
   checking isomorphism between the two MTBDDs (Theorem 4).
   I/O serialization to/from the CakeML binary is TCB; see mk_oracle_thm.

   Arguments:
     arith_policy1/2   -- two high-level forwarding policies with arithmetic
                          predicates over packet header fields (Sec. IV-B)
     policy_me         -- mapping m : variables -> atomic predicates,
                          shared by both policies (Sec. IV-A)
     test_pd_type      -- packet-field type descriptor encoding bit-vector
                          widths (Sec. IV-D)
     policy_order      -- variable order x1,...,xn for mk_mtbdd_opt (Sec. V)
     file_name         -- base name for intermediate I/O files exchanged
                          with the CakeML binary (TCB, Section VI)

   Returns:
    ORACLE |- !packet. wf_packet T packet =>
          sem_arith_policy policy1 packet =
          sem_arith_policy policy2 packet
     (carries CakeML oracle tag reflecting the TCB serialization)
   --------------------------------------------------------------------------- *)

    fun check_two_polcies_eq (arith_policy1, arith_policy2, policy_me, test_pd_type, policy_order, file_name) =

        let

        val start_cpu_total = Timer.startCPUTimer ();
        val start_real_total = Timer.startRealTimer ();


          (****************************************************)
        (*  STAGE 1: Forward translation  (Theorem 1 / IF1) *)
        (*           arith policy1 -> policy ILR1           *)
        (*           arith policy2 -> policy ILR2           *)
        (*                                                  *)
        (* trans-fwd is applied independently to each       *)
        (* policy using the shared mapping m (policy_me).   *)
        (* Theorem 1 is instantiated twice, once per policy.*)
        (****************************************************)

        (* Apply trans-fwd to policy1: replace each atomic predicate
           with its corresponding variable in m (policy_me). *)
        val arith_policy_eval1 = EVAL “convert_arith_to_var_policy ^arith_policy1 ^policy_me”;
        val var_policy1 = optionSyntax.dest_some (rhs (concl arith_policy_eval1));

        (* Apply trans-fwd to policy2. *)
        val arith_policy_eval2 = EVAL “convert_arith_to_var_policy ^arith_policy2 ^policy_me”;
        val var_policy2 = optionSyntax.dest_some (rhs (concl arith_policy_eval2));


        (* Establish distinctness of the domain (FST) and range (SND) of m.
           Side conditions of Theorem 1 (Definition 1, Section IV-A),
           shared by both instantiations. *)
        val policy_me_fst_distinct = EVAL “ALL_DISTINCT (MAP FST ^policy_me)”;
        val policy_me_snd_distinct = EVAL “ALL_DISTINCT (MAP SND ^policy_me)”;

        val all_distinct_conj = CONJ policy_me_fst_distinct policy_me_snd_distinct;


        (* Instantiate Theorem 1 (Thm IF1) for policy1:
             |- for every u ~_m packet,
                  sem-up(arith_policy1) packet = sem-down(var_policy1) u  *)
        val arith_policy_var_policy_thm1 = REWRITE_RULE[all_distinct_conj, arith_policy_eval1]
        (ISPECL[arith_policy1, var_policy1, policy_me] policy_airth_to_var_sem_conversion_correct);

        (* Instantiate Theorem 1 (Thm IF1) for policy2. *)
        val arith_policy_var_policy_thm2 = REWRITE_RULE[all_distinct_conj, arith_policy_eval2]
        (ISPECL[arith_policy2, var_policy2, policy_me] policy_airth_to_var_sem_conversion_correct);

        val _ = time_stage ("Stage 1 (Both policies to their ILR)", start_cpu_total, start_real_total)


        (* Save the ILR Policy 1 *) 
        val _ = save_thm("policy_trans_fwd_1", arith_policy_eval1);
        (* Save the ILR Policy 2 *) 
        val _ = save_thm("policy_trans_fwd_2", arith_policy_eval2);

        (* Save the ILR Policy 1*) 
        val _ = save_thm("policy_trans_fwd_proof_1", arith_policy_var_policy_thm1);
        (* Save the ILR Policy 2*) 
        val _ = save_thm("policy_trans_fwd_proof_2", arith_policy_var_policy_thm2);


        (****************************************************)
        (*  STAGE 2: MTBDD construction and equivalence     *)
        (*           check via CakeML  (Theorems 3 and 4)   *)
        (*                                                  *)
        (* mk_mtbdd_opt runs as a verified CakeML binary    *)
        (* (Section VI) rather than inside HOL4 EVAL.       *)
        (* I/O serialization to/from text files is TCB;     *)
        (* see mk_oracle_thm below.                         *)
        (*                                                  *)
        (* 2a. policy ILR1 -> MTBDD1  (CakeML binary)      *)
        (* 2b. policy ILR2 -> MTBDD2  (CakeML binary)      *)
        (* 2c. MTBDD1 iso MTBDD2      (Theorem 4)          *)
        (****************************************************)

        val start_cpu_total_stage2_bdd = Timer.startCPUTimer ();
        val start_real_total_stage2_bdd = Timer.startRealTimer ();


        (* 2a. Serialize var_policy1, var_policy2, and policy_order to text
               files. Serialization is part of the TCB (Section VI). *)
        val _ = write_term_to_file ("../bdd_cake_test/" ^ file_name ^ "_eq_policy1_out_test.txt", var_policy1);
        val _ = write_term_to_file ("../bdd_cake_test/" ^ file_name ^ "_eq_policy2_out_test.txt", var_policy2);
        val _ = write_term_to_file ("../bdd_cake_test/" ^ file_name ^ "_eq_order_out_test.txt", policy_order);

        val start_cpu_total_stage2_bdd1_start = Timer.startCPUTimer ();
        val start_real_total_stage2_bdd1_start = Timer.startRealTimer ();

        (* Run the verified CakeML binary to build MTBDD1 from var_policy1.
           The binary implements mk_mtbdd_opt (Theorem 3, Section V). *)
        val status_exec_policy1 = OS.Process.system 
        ("cd ../bdd_cake_test/ && time ./test_bdd_policy.cake " ^ 
        file_name ^ "_eq_policy1_out_test.txt " ^ 
        file_name ^ "_eq_order_out_test.txt > " ^ 
        file_name ^ "_eq_bdd_policy1_cakeml_export.txt")

        val _ = if OS.Process.isSuccess status_exec_policy1
        then print "Ja, policy1 BDD compilation completed\n"
        else (print "Nej, policy1 NDD compilation failed\n";
        OS.Process.exit OS.Process.failure)


        val _ = time_stage ("Stage 2 (Policy 1 MTBDD)", start_cpu_total_stage2_bdd1_start, start_real_total_stage2_bdd1_start)
        val start_cpu_total_stage2_bdd2_start = Timer.startCPUTimer ();
        val start_real_total_stage2_bdd2_start = Timer.startRealTimer ();

        (* Run the verified CakeML binary to build MTBDD2 from var_policy2. *)
        val status_exec_policy2 = OS.Process.system 
        ("cd ../bdd_cake_test/ && time ./test_bdd_policy.cake " ^ 
        file_name ^ "_eq_policy2_out_test.txt " ^ 
        file_name ^ "_eq_order_out_test.txt > " ^ 
        file_name ^ "_eq_bdd_policy2_cakeml_export.txt")


        val _ = if OS.Process.isSuccess status_exec_policy2
        then print "Ja, policy2 BDD compilation completed\n"
        else (print "Nej, policy2 NDD compilation failed\n";
        OS.Process.exit OS.Process.failure)

        val _ = time_stage ("Stage 2 (Policy 2 MTBDD)", start_cpu_total_stage2_bdd2_start, start_real_total_stage2_bdd2_start)
        val start_cpu_total_stage2_clean = Timer.startCPUTimer ();
        val start_real_total_stage2_clean = Timer.startRealTimer ();

        (* Deserialize MTBDD1 and MTBDD2 from the CakeML output files back
           into HOL4 terms. Deserialization is part of the TCB (Section VI). *)
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
        val _ = print "Note:finished cleaning input1 \n";

        val policy_bdd_content_term2 = Parse.Term [QUOTE policy_content_str2];
        val _ = print "Note:finished cleaning input2 \n";

        val _ = time_stage ("Stage 2 finished cleaning", start_cpu_total_stage2_clean, start_real_total_stage2_clean)

        val start_cpu_total_stage2_iso = Timer.startCPUTimer ();
        val start_real_total_stage2_iso = Timer.startRealTimer ();

        (* 2c. Compute the candidate isomorphism witness I between MTBDD1
               and MTBDD2. *)
        val get_i_policy = bdd_utilsLib.pairBDDs (policy_bdd_content_term1, policy_bdd_content_term2);

        val _ = time_stage ("Stage 2 get isomorph", start_cpu_total_stage2_iso, start_real_total_stage2_iso)

        val start_cpu_total_stage2_proof = Timer.startCPUTimer ();
        val start_real_total_stage2_proof = Timer.startRealTimer ();


        (* mk_oracle_thm introduces MTBDD1 and MTBDD2 as axioms tagged
           "CakeML_policy_TCB": the CakeML binary implements verified
           mk_mtbdd_opt (Theorem 3), but the text file I/O roundtrip is
           not verified and constitutes the TCB (Section VI).
           The oracle tag makes this 
           trust assumption explicit and visible
           in the final theorem.*)
        val _ = (show_tags := true);

        val CakeML_policy_TCB_thm = mk_oracle_thm "CakeML_policy_TCB";

        val eval_policy_full_opt1 = CakeML_policy_TCB_thm ([], “mk_BDDPred_opt policy_structure (0,[],[(0, non_termn (NONE, ^var_policy1))]) [] ^policy_order 1 = SOME ^policy_bdd_content_term1 ”);

        val eval_policy_full_opt2 = CakeML_policy_TCB_thm ([], “mk_BDDPred_opt policy_structure (0,[],[(0, non_termn (NONE, ^var_policy2))]) [] ^policy_order 1 = SOME ^policy_bdd_content_term2 ”); 


        val var_eq_thm_extract = REWRITE_CONV [correct_var_policy_var_policy_exec_def, eval_policy_full_opt1 , eval_policy_full_opt2] “correct_var_policy_var_policy_exec ^var_policy1 ^var_policy2 ^policy_order ^get_i_policy”;

        (* Verify isomorphism between MTBDD1 and MTBDD2 and lift to semantic
           equivalence via Theorem 4:  |- sem(MTBDD1) = sem(MTBDD2). *)
        val var_eq_thm_extract_red = computeLib.RESTR_EVAL_RULE  [“correct_var_policy_var_policy_exec”, “sem_policy”,“sem_policy”, “mv_dom_vars”]  var_eq_thm_extract;
        val var_policy_var_policy_thm = SIMP_RULE bool_ss [correct_var_policy_var_policy_exec_thm1] var_eq_thm_extract_red;



        val _ = time_stage ("Stage 2 proof", start_cpu_total_stage2_proof, start_real_total_stage2_proof)
        val _ = time_stage ("Stage 2 total", start_cpu_total_stage2_bdd, start_real_total_stage2_bdd)


        (* Save the Policy BDD of 1*) 
        val _ = save_thm("policy_BDD_1", eval_policy_full_opt1);
        (* Save the Policy BDD of output*)
        val _ = save_thm("policy_BDD_2", eval_policy_full_opt2);


        (****************************************************)
        (*  FINAL PROOF: End-to-end semantic equivalence    *)
        (*                                                  *)
        (* Composes Thm 1 (IF1) x2 and Thm 4:              *)
        (*   ORACLE|- !packet. wf_packet T packet =>        *)
        (*        sem_arith_policy policy1 packet =         *)
        (*        sem_arith_policy policy2 packet           *)
        (*                                                  *)
        (* Carries oracle tag CakeML_policy_TCB             *)
        (* (I/O serialization is TCB).                      *)
        (* cond1-cond2: well-formedness of m and order.    *)
        (****************************************************)

        val start_cpu_final = Timer.startCPUTimer ();
        val start_real_final = Timer.startRealTimer ();



        (* cond1: every left-value in m appears in the type descriptor,
                  and the keys of m are distinct (Section IV-A). *)
        val every_lval_in_me_in_type_thm = EVAL “every_lval_in_me_in_type ^test_pd_type ^policy_me”;
        val cond1_thm = REWRITE_RULE [every_lval_in_me_in_type_thm, policy_me_fst_distinct] (ISPECL[policy_me, test_pd_type ] lval_in_me_distinct_imp_cond1);

        val _ = time_stage ("Stage 3 prepp for proof COND1 ", start_cpu_final, start_real_final)
        val start_cpu_final_1 = Timer.startCPUTimer ();
        val start_real_final_1 = Timer.startRealTimer ();


        (* cond2: the variable order is consistent with m, and the type
                  descriptor correctly encodes the bit-vector widths of
                  all header fields. *)
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


        (* Prove the end-to-end theorem by chaining both Theorem 1 instances
           and the MTBDD equivalence theorem via the shared valuation
           (create_mv policy_me packet).
           fs discharges remaining goals using cond1-cond2. *)
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

        assume_tac var_policy_var_policy_thm >>
        first_x_assum (strip_assume_tac o (Q.SPECL [‘(create_mv ^policy_me packet_input)’])) >>
        fs[cond1_thm, cond2_thm] 
        );

        val _ = time_stage ("Final glue proof", start_cpu_final_p, start_real_final_p)
        val _ = time_stage ("Total ", start_cpu_total, start_real_total)
        val _ = save_thm("final_proof", final_thm);
    in
    final_thm
    end;

end;