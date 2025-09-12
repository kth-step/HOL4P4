open HolKernel boolLib liteLib simpLib Parse bossLib;
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
open set_relationTheory;
open pred_setTheory;
open pred_setLib;

open p4_auxTheory;

open bdd_auxTheory;          
open bdd_genTheory;     
open bdd_gen_wfTheory;     
open bdd_gen_orderTheory;
open bdd_gen_correctTheory;

open bdd_gen_mergeTheory;
open bdd_gen_eliminateTheory;


val _ = new_theory "bdd_gen_optimization";

(*******************************************************)
(*         Optimzations Correctness full               *)
(*                       proofs                        *)
(*******************************************************)



(* Helper lemma: operate_opt1 preserves correctness *)
Theorem operate_opt1_preserves_correctness:
  ∀BDD nl all_nodes vars vars_consumed rec.
    valid_BDD rec BDD vars vars_consumed∧
    correct_sem rec BDD (vars ⧺ vars_consumed)   ⇒
    (valid_BDD rec (operate_opt1 BDD nl all_nodes) vars vars_consumed ∧
     correct_sem rec (operate_opt1 BDD nl all_nodes) (vars ⧺ vars_consumed) 
     )
Proof

  Induct_on ‘nl’ >> rpt gen_tac >- (
    (* Base case: empty list *)
    fs [operate_opt1_def]
  ) >>
  
  (* Inductive case *)
  rpt gen_tac >> strip_tac >>
  fs [operate_opt1_def] >>
  
  (* Apply inductive hypothesis *)
  first_x_assum irule >>
          
  (* Use merge_BDD_preserves_valid_and_correctness *)
  imp_res_tac merge_BDD_preserves_valid_and_correctness >>
  metis_tac[]  
QED



        
(* Now the main theorem follows easily *)
Theorem bdd_optminzation1_preserves_correctness:
  ∀BDD vars vars_consumed rec.   
    valid_BDD rec BDD vars vars_consumed ∧
    correct_sem rec BDD (vars ⧺ vars_consumed)  ⇒
    ( valid_BDD rec (bdd_optminzation1 BDD) vars vars_consumed ∧
      correct_sem rec (bdd_optminzation1 BDD) (vars ⧺ vars_consumed) 
    )
Proof
  rpt strip_tac >>
  fs [bdd_optminzation1_def] >>
  
  PairCases_on ‘BDD’ >>
  rename1 ‘(root, edges, labels)’ >>

  rw[]>>
  (* Apply operate_opt1_preserves_correctness *)
  imp_res_tac operate_opt1_preserves_correctness >>
  metis_tac[] 
QED




(* some elimination work*)

Theorem operate_opt2_preserves_correctness:
  ∀BDD nl all_nodes vars vars_consumed rec.
    valid_BDD rec BDD vars vars_consumed ∧
    correct_sem rec BDD (vars ⧺ vars_consumed)   ⇒
    (valid_BDD rec (operate_opt2 BDD nl all_nodes) vars vars_consumed ∧
     correct_sem rec (operate_opt2 BDD nl all_nodes) (vars ⧺ vars_consumed) 
     )
Proof

  Induct_on ‘nl’ >> rpt gen_tac >- (
    (* Base case: empty list *)
    fs [operate_opt2_def]
  ) >>
  
  (* Inductive case *)
  rpt gen_tac >> strip_tac >>
  fs [operate_opt2_def] >>
  
  (* Apply inductive hypothesis *)
  first_x_assum irule >>
                
  gvs[] >>
  imp_res_tac eliminate_BDD_preserves_valid_and_correctness >>
  metis_tac[]  
QED



        
(* Now the main theorem follows easily *)
Theorem bdd_optminzation2_preserves_correctness:
  ∀BDD vars vars_consumed rec.   
    valid_BDD rec BDD vars vars_consumed ∧
    correct_sem rec BDD (vars ⧺ vars_consumed) ⇒
    ( valid_BDD rec (bdd_optminzation2 BDD) vars vars_consumed  ∧
      correct_sem rec (bdd_optminzation2 BDD) (vars ⧺ vars_consumed)
    )
Proof
  rpt strip_tac >>
  fs [bdd_optminzation2_def] >>
  
  PairCases_on ‘BDD’ >>
  rename1 ‘(root, edges, labels)’ >>


  rw[]>>
  (* Apply operate_opt1_preserves_correctness *)
  imp_res_tac operate_opt2_preserves_correctness >>
  metis_tac[] 
QED




 (**** GLUE OPT TOGETHER *****)       
 
(* Combining the two optimizations *)
Theorem bdd_one_round_preserves_correctness:
  ∀BDD vars vars_consumed rec.
    valid_BDD rec BDD vars vars_consumed ∧
    correct_sem rec BDD (vars ⧺ vars_consumed) ⇒
    (
    valid_BDD rec (bdd_one_round BDD) vars vars_consumed ∧
    correct_sem rec (bdd_one_round BDD) (vars ⧺ vars_consumed)
    )            
Proof
  rw[bdd_one_round_def] >>
  imp_res_tac bdd_optminzation2_preserves_correctness >>
  imp_res_tac bdd_optminzation1_preserves_correctness
QED




        

        
(* This theorem is just for optimisations *)
Theorem bdd_optimize_preserves_correctness:
  ∀BDD vars vars_consumed rec.
    valid_BDD rec BDD vars vars_consumed ∧
    correct_sem rec BDD (vars ⧺ vars_consumed) ⇒
    (
    valid_BDD rec (bdd_full_optimize BDD) vars vars_consumed ∧
    correct_sem rec (bdd_full_optimize BDD) (vars ⧺ vars_consumed)
    )
Proof
  (* Use strong induction on the measure that ensures termination *)
  completeInduct_on ‘BDD_label_length BDD’ >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
      
  (* Unfold the definition *)
  once_rewrite_tac[bdd_full_optimize_def] >>
  Cases_on ‘bdd_one_round BDD = BDD’ >> fs[] >>
           
  (* Recursive case: optimization makes progress *)
  imp_res_tac bdd_one_round_preserves_correctness >>

  (* Apply induction hypothesis *)
  subgoal ‘BDD_label_length (bdd_one_round BDD) < BDD_label_length BDD’ >- (
    metis_tac[bdd_one_round_reduce]
  ) >>
    
  (* Apply induction hypothesis *)
  first_x_assum (strip_assume_tac o (Q.SPECL [‘BDD_label_length (bdd_one_round BDD)’])) >>
  gvs[] >>
        
  first_x_assum (strip_assume_tac o (Q.SPECL [‘(bdd_one_round BDD)’])) >>
  gvs[] >>

  first_x_assum (strip_assume_tac o (Q.SPECL [‘vars’, ‘rec’])) >>
  gvs[] 
       
QED






Theorem fv_in_BDD_reverse_triv2:
  ∀ BDD vars vars_consumed h rec.
    fv_in_BDD rec BDD (REVERSE vars ++ h ++ vars_consumed) =
    fv_in_BDD rec BDD (vars ++ h ++ vars_consumed)
Proof
  rpt strip_tac >>
  PairCases_on ‘BDD’ >>
  rename1 ‘(r,edges,labels)’ >>
  
  fs[fv_in_labels_def, fv_in_BDD_def, merge_def, fv_in_vars_def] >>
  rpt strip_tac >>
  res_tac >>
  fs[fv_in_vars_def]
QED



(* RANGE IS PRESERVED *)

   
Theorem merge_BDD_preserves_range:
  ∀ BDD c n nl.
    range_c c BDD ⇒
    (range_c c (merge_BDD BDD n nl) ∧
     range_c c (eliminate_BDD BDD nl) )
Proof
  Induct_on ‘nl’ >-
   fs [merge_BDD_def, eliminate_BDD_def] >>
  
  rpt strip_tac >>
      
  fs [merge_BDD_def, eliminate_BDD_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> rgs[]) >|[
      
    Cases_on ‘mergable BDD n h’ >> gvs[] >>
    imp_res_tac merge_range_preservation >>
    metis_tac[]
    ,
    imp_res_tac merge_range_preservation >>
    metis_tac[]
  ]
QED
        

Theorem operate_opt1_preserves_range:
  ∀BDD c nl all_nodes.   
    range_c c BDD  ⇒
    range_c c (operate_opt1 BDD nl all_nodes) 
Proof

  Induct_on ‘nl’ >> rpt gen_tac >- 
    fs [operate_opt1_def] >>
  
  rpt gen_tac >> strip_tac >>
  fs [operate_opt1_def] >>
  
  first_x_assum irule >>    
  gvs[] >>
  imp_res_tac merge_BDD_preserves_range >>
  metis_tac[]  
QED




Theorem operate_opt2_preserves_range:
  ∀BDD c nl all_nodes.   
    range_c c BDD  ⇒
    range_c c (operate_opt2 BDD nl all_nodes) 
Proof

  Induct_on ‘nl’ >> rpt gen_tac >- 
    fs [operate_opt2_def] >>
  
  rpt gen_tac >> strip_tac >>
  fs [operate_opt2_def] >>
  
  first_x_assum irule >>    
  gvs[] >>
  imp_res_tac merge_BDD_preserves_range >>
  metis_tac[]  
QED

        
   
Theorem bdd_optminzation1_preserves_range:
  ∀BDD c.   
    range_c c BDD  ⇒
    range_c c (bdd_optminzation1 BDD) 
Proof
  rpt strip_tac >>
  fs [bdd_optminzation1_def] >>
  
  PairCases_on ‘BDD’ >>
  rename1 ‘(root, edges, labels)’ >>


  rw[]>>
  metis_tac[operate_opt1_preserves_range]
QED

   
Theorem bdd_optminzation2_preserves_range:
  ∀BDD c.   
    range_c c BDD  ⇒
    range_c c (bdd_optminzation2 BDD) 
Proof
  rpt strip_tac >>
  fs [bdd_optminzation2_def] >>
  
  PairCases_on ‘BDD’ >>
  rename1 ‘(root, edges, labels)’ >>


  rw[]>>
  metis_tac[operate_opt2_preserves_range]
QED


Theorem bdd_one_round_preserves_range:
  ∀ BDD c.
    range_c c BDD ⇒
    range_c c (bdd_one_round BDD)
Proof
  rw[bdd_one_round_def] >>
  imp_res_tac bdd_optminzation2_preserves_range >>
  imp_res_tac bdd_optminzation1_preserves_range
QED

        
Theorem full_optimizations_preserves_range:
  ∀ BDD c.
    range_c c BDD ⇒
    range_c c (bdd_full_optimize BDD)
Proof

 completeInduct_on ‘BDD_label_length BDD’ >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
      
  (* Unfold the definition *)
  once_rewrite_tac[bdd_full_optimize_def] >>
  Cases_on ‘bdd_one_round BDD = BDD’ >> fs[] >>
           
  (* Recursive case: optimization makes progress *)
  imp_res_tac bdd_one_round_preserves_range >>

  (* Apply induction hypothesis *)
  subgoal ‘BDD_label_length (bdd_one_round BDD) < BDD_label_length BDD’ >- (
    metis_tac[bdd_one_round_reduce]
  ) >>

 gvs[]
QED
      
    

        
Theorem correct_sem_valid_translation_opt:
  ∀ vars vars_consumed BDD BDD' rec c.
    prop1 rec ∧ prop2 rec ∧ prop3 rec ∧ prop4 rec ∧

    range_c c BDD ∧
    ALL_DISTINCT ((REVERSE vars)++vars_consumed) ∧
          
    valid_BDD rec BDD vars vars_consumed ∧
    correct_sem rec BDD ((REVERSE vars)++vars_consumed) ∧
                
    SOME BDD' = mk_BDDPred_opt rec BDD vars_consumed vars c ⇒
    (
    valid_BDD rec BDD' [] ((REVERSE vars)++vars_consumed) ∧
    correct_sem rec BDD' ((REVERSE vars)++vars_consumed) )
Proof

  
 Induct >>
 rpt gen_tac >> strip_tac >>
 gvs[mk_BDDPred_opt_def] >>

 gvs[AllCaseEqs()] >>


 rpt strip_tac >>
 
 PairCases_on ‘BDD’ >>
 rename1 ‘(r,edges,labels)’ >>
 
 PairCases_on ‘BDD'’ >>
 rename1 ‘(r',edges',labels')’ >>
 
 PairCases_on ‘BDD''’ >>
 rename1‘((r'',edges'',labels''),c')’ >>
 
 gvs[valid_BDD_def] >>

 ‘range_c c' (r'',edges'',labels'')’ by imp_res_tac WFness_range_c_inter >>
 
 ‘BDD_WF (r'',edges'',labels'')’ by imp_res_tac WFness_translation_inter >> gvs[]>>
 
 ‘ALL_DISTINCT (h::vars_consumed)’ by gvs[ALL_DISTINCT_APPEND] >>        
 ‘BDD_ordered (r'',edges'',labels'') (h::vars_consumed)’ by imp_res_tac order_translation_inter >>
 
 ‘consumed_dom_bdd (h::vars_consumed) (r'',edges'',labels'')’ by imp_res_tac consumed_dom_bdd_inter >>
 
 
 assume_tac correct_sem_translation_inter >>
 first_x_assum (strip_assume_tac o (Q.SPECL [‘(r,edges,labels)’, ‘(r'',edges'',labels'')’, ‘rec’, ‘c’, ‘c'’, ‘REVERSE vars’, ‘h’, ‘vars_consumed’])) >>
 gvs[]>>

 ‘fv_in_BDD rec (r'',edges'',labels'') (REVERSE vars ⧺ [h] ⧺ vars_consumed)’ by metis_tac[fv_in_BDD_body_preserved] >>

 (* now we show that opt is also correct *)
 
 assume_tac bdd_optimize_preserves_correctness >>
 first_x_assum (strip_assume_tac o (Q.SPECL [‘(r'',edges'',labels'')’, ‘REVERSE vars’, ‘[h] ⧺ vars_consumed’, ‘rec’])) >>
 gvs[valid_BDD_def] >>


 ‘fv_in_BDD rec (r'',edges'',labels'') (vars ⧺ [h] ⧺ vars_consumed) ’ by metis_tac[fv_in_BDD_reverse_triv2] >>
  gvs[] >>
        
 first_x_assum (strip_assume_tac o (Q.SPECL [‘[h] ⧺ vars_consumed’, ‘(bdd_full_optimize (r'',edges'',labels''))’,
                                            ‘(r',edges',labels')’, ‘rec’, ‘c'’])) >>

 gvs[] >>

 ‘range_c c' (bdd_full_optimize (r'',edges'',labels''))’ by metis_tac[full_optimizations_preserves_range] >>
 ‘fv_in_BDD rec (bdd_full_optimize (r'',edges'',labels'')) (REVERSE vars ⧺ [h] ⧺ vars_consumed)’ by metis_tac[fv_in_BDD_reverse_triv2] >>
 
 metis_tac[]
QED 




val _ = export_theory ();

