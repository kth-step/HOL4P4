structure fwd_proofLib :> fwd_proofLib = struct


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
   convert_arith_policy_to_interval_tables

   Implements the POLYGRAM compilation pipeline (Path 2, Figure 3),
   instantiated for input policy and output P4 tables.
   Fully end-to-end verified in HOL4; no TCB.

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

   Returns:
     |- !packet. wf_packet T packet =>
          sem_arith_policy policy packet =
          sem_sinterval_tables (tables, 0) packet
   --------------------------------------------------------------------------- *)

   fun convert_arith_policy_to_interval_tables (arith_policy, policy_me, test_pd_type, policy_full_order, policy_order) =

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

        val start_cpu_stage1 = Timer.startCPUTimer ();
        val start_real_stage1 = Timer.startRealTimer (); 


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


        val _ = time_stage ("Stage 1 (Policy to policy ILR)", start_cpu_stage1, start_real_stage1);

        (* Save the ILR Policy *) 
        val _ = save_thm("policy_trans_fwd", arith_policy_eval);
        (* Save the trans proof Policy Theorem 1 *)
        val _ = save_thm("policy_trans_fwd_proof", arith_policy_var_policy_thm); 


        (****************************************************)
        (*  STAGE 2: MTBDD construction and validation      *)
        (*           (Theorems 3 and 4)                     *)
        (*                                                  *)
        (* 2a. policy ILR  -> MTBDD1       (Theorem 3)     *)
        (* 2b. MTBDD1      -> var table ILR (untrusted SML) *)
        (* 2c. var table   -> MTBDD2       (Theorem 3)     *)
        (* 2d. MTBDD1 iso MTBDD2           (Theorem 4)     *)
        (****************************************************)


        val start_cpu_stage2 = Timer.startCPUTimer ();
        val start_real_stage2 = Timer.startRealTimer (); 


        (* 2a. Build MTBDD1 from var_policy.
               mk_BDDPred_opt implements mk_mtbdd_opt (Theorem 3, Section V):
               result is well-formed, ordered, reduced, and semantically
               equivalent to var_policy. *)
        val eval_policy_full_opt = EVAL “mk_BDDPred_opt policy_structure (0,[],[(0, non_termn (NONE, ^var_policy))]) [] ^policy_order 1”;
        val eval_policy_full_opt_rhs = optionSyntax.dest_some (rhs (concl eval_policy_full_opt));

        val _ = time_stage ("Stage 2 (Policy MTBDD)", start_cpu_stage2, start_real_stage2);
        val start_cpu_stage2_vbdd = Timer.startCPUTimer ();
        val start_real_stage2_vbdd = Timer.startRealTimer (); 

        (* 2b. Run the untrusted MTBDD-to-table algorithm (Section IV-E, SML).
               bdd_to_tables_iterative traverses MTBDD1 and produces a candidate
               var table ILR (gen_var_table_auto). This step is untrusted;
               its correctness is validated a posteriori by step 2d. *)
        val test_groupings = rhs(concl(EVAL policy_full_order));
        val gen_var_table_auto = bdd_utilsLib.bdd_to_tables_iterative eval_policy_full_opt_rhs test_groupings;


        val _ = time_stage ("Stage 2 (Policy MTBDD to Table)", start_cpu_stage2_vbdd, start_real_stage2_vbdd);
        val start_cpu_stage2_tbl = Timer.startCPUTimer ();
        val start_real_stage2_tbl = Timer.startRealTimer ();


        (* 2c. Build MTBDD2 from the candidate var table ILR (gen_var_table_auto)
               using the same certified mk_mtbdd_opt (Theorem 3).
               This construction is independent of the untrusted algorithm. *)
        val eval_table_full_opt_auto = EVAL “mk_BDDPred_opt table_structure (0,[],[(0, non_termn (NONE, ^gen_var_table_auto))]) [] ^policy_order 1”;
        val eval_table_full_opt_auto_rhs = optionSyntax.dest_some (rhs (concl eval_table_full_opt_auto));

        val _ = time_stage ("Stage 2 (Table MTBDD)", start_cpu_stage2_tbl, start_real_stage2_tbl);
        val start_cpu_stage2_tbdd = Timer.startCPUTimer ();
        val start_real_stage2_tbdd = Timer.startRealTimer ();

        (* 2d. Check isomorphism between MTBDD1 and MTBDD2.
               pairBDDs computes the candidate isomorphism witness I.
               correct_var_policy_var_tables_exec verifies I is a valid
               isomorphism; correct_var_policy_var_tables_exec_thm1 lifts
               this to semantic equivalence via Theorem 4:
                 |- sem(MTBDD1) = sem(MTBDD2)
               Compilation correctness is thus reduced to MTBDD equivalence
               checking, independently of the untrusted algorithm in 2b. *)
        val get_i_policy = bdd_utilsLib.pairBDDs (eval_policy_full_opt_rhs, eval_table_full_opt_auto_rhs);


        val var_eq_thm_extract = REWRITE_CONV [correct_var_policy_var_tables_exec_def, eval_policy_full_opt , eval_table_full_opt_auto] “correct_var_policy_var_tables_exec ^var_policy ^gen_var_table_auto ^policy_order ^get_i_policy”;
        val var_eq_thm_extract_red = computeLib.RESTR_EVAL_RULE  [“correct_var_policy_var_tables_exec”, “sem_tables”,“sem_policy”, “mv_dom_vars”]  var_eq_thm_extract; 
        val var_policy_var_table_thm = SIMP_RULE bool_ss [correct_var_policy_var_tables_exec_thm1] var_eq_thm_extract_red;  


        val _ = time_stage ("Stage 2 proof", start_cpu_stage2_tbdd, start_real_stage2_tbdd);

        val _ = time_stage ("Stage 2 total", start_cpu_stage2, start_real_stage2);


        (* Save the Policy BDD *) 
        val _ = save_thm("policy_BDD", eval_policy_full_opt);
        (* Save the Table BDD *)
        val _ = save_thm("table_BDD", eval_table_full_opt_auto); 


        (****************************************************)
        (*  STAGE 3: Back translation  (Theorem 2 / OF2)   *)
        (*           var table ILR -> interval tables       *)
        (*                                                  *)
        (* trans-back converts each Boolean row constraint  *)
        (* to a closed bit-vector interval using m and      *)
        (* field widths in test_pd_type (Section IV-D):     *)
        (*   for every u ~_m packet,                        *)
        (*     sem-down(var_table) u                        *)
        (*       = sem-up(interval_table) packet            *)
        (****************************************************)

        val start_cpu_stage3 = Timer.startCPUTimer ();
        val start_real_stage3 = Timer.startRealTimer (); 


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

        val _ = time_stage ("Stage 3 (Table ILR to P4 table)", start_cpu_stage3, start_real_stage3);

        (* Save the trans Table *)
        val _ = save_thm("table_trans_back", convert_to_interval);
        (* Save the trans proof Table Theorem 2 *)
        val _ = save_thm("table_trans_fwd_proof", var_table_sinterval_tbl_thm); 


        (****************************************************)
        (*  FINAL PROOF: End-to-end semantic equivalence    *)
        (*                                                  *)
        (* Composes all stage theorems to establish:        *)
        (*   |- !packet. wf_packet T packet =>              *)
        (*        sem_arith_policy policy packet =          *)
        (*        sem_sinterval_tables (tables,0) packet    *)
        (*                                                  *)
        (* Proof chain:                                     *)
        (*   arith_policy_var_policy_thm (Thm 1 / IF1)     *)
        (*   var_policy_var_table_thm    (Thms 3 + 4)       *)
        (*   var_table_sinterval_tbl_thm (Thm 2 / OF2)     *)
        (*                                                  *)
        (* cond1-cond3 assert well-formedness of m and the  *)
        (* variable order w.r.t. the type descriptor.       *)
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


        val _ = time_stage ("Final glue proof", start_cpu_final, start_real_final);

        val _ = time_stage ("Total time of everything", start_cpu_total, start_real_total);

        (* save final proof *)
        val _ = save_thm("final_proof", final_thm);
    in
    final_thm
    end;

end;
