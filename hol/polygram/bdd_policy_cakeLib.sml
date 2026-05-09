structure bdd_policy_cakeLib :> bdd_policy_cakeLib = struct


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
   convert_arith_policy_to_bdd
 
   Implements only the first two stages of the POLYGRAM pipeline (Figure 3):
   forward translation and MTBDD construction. Does not perform compilation
   or equivalence checking. The resulting MTBDD and stage theorems are saved
   as named HOL4 theorems for reuse by other pipeline components.
 
   Arguments:
     arith_policy -- high-level forwarding policy with arithmetic predicates
                     over packet header fields (Sec. IV-B)
     policy_me    -- mapping m : variables -> atomic predicates,
                     connecting the policy language and its ILR (Sec. IV-A)
     test_pd_type -- packet-field type descriptor encoding bit-vector widths
                     (Sec. IV-D)
     policy_order -- variable order x1,...,xn for mk_mtbdd_opt (Sec. V)
     file_name    -- base name for intermediate I/O files exchanged with
                     the CakeML binary (TCB, Section VI)
 
   Saves:
     policy_trans_fwd       -- result of trans-fwd (Theorem 1 / Thm IF1)
     policy_trans_fwd_proof -- soundness proof of trans-fwd (Theorem 1)
     policy_BDD             -- MTBDD theorem (Theorem 3, via CakeML oracle)
   --------------------------------------------------------------------------- *)


    fun convert_arith_policy_to_bdd (arith_policy, policy_me, test_pd_type, policy_order, file_name) =

    let

        val start_cpu_total = Timer.startCPUTimer ();
        val start_real_total = Timer.startRealTimer ();



        (****************************************************)
        (*  STAGE 1: Forward translation  (Theorem 1 / IF1) *)
        (*           arith policy -> policy ILR             *)
        (*                                                  *)
        (* trans-fwd replaces each atomic predicate with    *)
        (* its variable in m (policy_me). Theorem 1 proves  *)
        (* soundness:                                       *)
        (*   for every u ~_m packet,                        *)
        (*     sem-up(arith_policy) packet                  *)
        (*       = sem-down(var_policy) u                   *)
        (****************************************************)


        (* Apply trans-fwd: replace every atomic predicate in arith_policy
           with its corresponding variable in m (policy_me). *)
        val arith_policy_eval = EVAL “convert_arith_to_var_policy ^arith_policy ^policy_me”;
        val var_policy = optionSyntax.dest_some (rhs (concl arith_policy_eval));


        (* Establish distinctness of the domain (FST) and range (SND) of m.
           Side conditions of Theorem 1 (Definition 1, Section IV-A). *)
        val policy_me_fst_distinct = EVAL “ALL_DISTINCT (MAP FST ^policy_me)”;
        val policy_me_snd_distinct = EVAL “ALL_DISTINCT (MAP SND ^policy_me)”;

        val all_distinct_conj = CONJ policy_me_fst_distinct policy_me_snd_distinct;


        (* Instantiate Theorem 1 (Thm IF1):
             |- for every u ~_m packet,
                  sem-up(arith_policy) packet = sem-down(var_policy) u  *)
        val arith_policy_var_policy_thm = REWRITE_RULE[all_distinct_conj, arith_policy_eval]
        (ISPECL[arith_policy, var_policy, policy_me] policy_airth_to_var_sem_conversion_correct);

        val _ = time_stage ("(Policy to policy ILR)", start_cpu_total, start_real_total)
        (* Save the ILR Policy *) 
        val _ = save_thm("policy_trans_fwd", arith_policy_eval);
        (* Save the trans proof Policy Theorem 1 *)
        val _ = save_thm("policy_trans_fwd_proof", arith_policy_var_policy_thm); 



        (****************************************************)
        (*  STAGE 2: MTBDD construction via CakeML          *)
        (*           policy ILR -> MTBDD  (Theorem 3)       *)
        (*                                                  *)
        (* mk_mtbdd_opt runs as a verified CakeML binary    *)
        (* (Section VI) rather than inside HOL4 EVAL.       *)
        (* I/O serialization to/from text files is TCB;     *)
        (* see mk_oracle_thm below.                         *)
        (****************************************************)



        (* Serialize var_policy and policy_order to text files.
           These are the inputs to the CakeML binary. TCB. *)
        val _ = write_term_to_file ("../bdd_cake_test/" ^ file_name ^ "_policy_out_test.txt", var_policy);
        val _ = write_term_to_file ("../bdd_cake_test/" ^ file_name ^ "_order_out_test.txt", policy_order);


        val start_cpu_total_stage2a = Timer.startCPUTimer ();
        val start_real_total_stage2a = Timer.startRealTimer ();


        (* Run the verified CakeML binary test_bdd_policy.cake to build the
           MTBDD. The binary implements mk_mtbdd_opt (Theorem 3, Section V),
           compiled via CakeML verified compilation (Section VI). The result
           is written to a text file for deserialization back into HOL4. *)
        val status_exec_policy = OS.Process.system 
        ("cd ../bdd_cake_test/ && time ./test_bdd_policy.cake " ^ 
        file_name ^ "_policy_out_test.txt " ^ 
        file_name ^ "_order_out_test.txt > " ^ 
        file_name ^ "_bdd_policy_cakeml_export.txt")


        val _ = if OS.Process.isSuccess status_exec_policy
        then print "Ja, policy BDD compilation completed\n"
        else (print "Nej, policy BDD compilation failed\n";
        OS.Process.exit OS.Process.failure)

        val _ = time_stage ("(Policy MTBDD creation time via CakeML) ", start_cpu_total_stage2a, start_real_total_stage2a)

        (* Deserialize the MTBDD from the CakeML output file back into a HOL4
           term. Deserialization is part of the TCB (Section VI). *)
        val filename_policy_export = "../bdd_cake_test/" ^ file_name ^ "_bdd_policy_cakeml_export.txt"
        val ins_policy = TextIO.openIn filename_policy_export
        val policy_content_str = TextIO.inputAll ins_policy;
        val _ = TextIO.closeIn ins_policy;

        val policy_bdd_content_term = Parse.Term [QUOTE policy_content_str];

        val _ = print "Note:finished cleaning input \n";


        (* mk_oracle_thm introduces the MTBDD as an axiom tagged
           "CakeML_policy_TCB": the CakeML binary implements verified
           mk_mtbdd_opt (Theorem 3), but the text file I/O roundtrip is
           not verified and constitutes the TCB (Section VI).
           The oracle tag makes this trust assumption explicit and visible
           in any theorem that depends on this result. *)

        val _ = (show_tags := true);

        val CakeML_policy_TCB_thm = mk_oracle_thm "CakeML_policy_TCB";

        val eval_policy_full_opt = CakeML_policy_TCB_thm ([], “mk_BDDPred_opt policy_structure (0,[],[(0, non_termn (NONE, ^var_policy))]) [] ^policy_order 1 = SOME ^policy_bdd_content_term ”);


        val _ = time_stage ("Total ", start_cpu_total, start_real_total)


        (* Save the Policy BDD *) 
        val _ = save_thm("policy_BDD", eval_policy_full_opt);


    in
    eval_policy_full_opt
    end;

end;