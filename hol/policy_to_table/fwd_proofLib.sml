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


        val start_cpu_stage2 = Timer.startCPUTimer ();
        val start_real_stage2 = Timer.startRealTimer (); 

(*
val policy_main_hol4_def = Define`
  policy_main_hol4 =
    case sp_mk_BDD_policy ^var_policy ^policy_order of
      NONE => NONE
    | SOME (r, sp_edges, sp_labels) => 
        SOME (r,
            ((toSortedAList sp_edges):edges),
           ((toSortedAList sp_labels): (((string#num list) action_expr) policy, (string#num list) action_expr) labelings))
`;


            val eval_policy_full_opt = EVAL “policy_main_hol4”; *)

            val eval_policy_full_opt = EVAL “
              sp_mk_BDDPred_opt policy_structure (0n,LN,insert 0 (non_termn (NONE, ^var_policy)) LN) [] ^policy_order 1n”;

            
            val eval_policy_full_opt_rhs1 = optionSyntax.dest_some (rhs (concl eval_policy_full_opt));

        val _ = time_stage ("Stage 2 from var policy to BDD", start_cpu_stage2, start_real_stage2);


        val start_cpu_stage2b = Timer.startCPUTimer ();
        val start_real_stage2b = Timer.startRealTimer (); 

val conv_policy_from_sp_to_bdd = 
  EVAL ``let (r, sp_edges, sp_labels) = ^eval_policy_full_opt_rhs1
         in SOME (r,
                  (toSortedAList sp_edges),
                  (toSortedAList sp_labels))``;


              val eval_policy_full_opt_rhs =  optionSyntax.dest_some (rhs (concl conv_policy_from_sp_to_bdd));

        val _ = time_stage ("Stage toStrted List", start_cpu_stage2b, start_real_stage2b);


    in
    eval_policy_full_opt
    end;

end;


             
