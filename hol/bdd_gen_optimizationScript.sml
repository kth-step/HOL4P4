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
  ∀BDD nl all_nodes vars rec.
    BDD_WF BDD ∧
    BDD_ordered BDD vars ∧
    fv_in_BDD rec BDD vars ∧
    consumed_dom_bdd vars BDD ∧
    correct_sem rec BDD vars  ⇒
    (BDD_WF (operate_opt1 BDD nl all_nodes) ∧
     BDD_ordered (operate_opt1 BDD nl all_nodes) vars ∧
     fv_in_BDD rec (operate_opt1 BDD nl all_nodes) vars ∧
     consumed_dom_bdd vars (operate_opt1 BDD nl all_nodes) ∧
     correct_sem rec (operate_opt1 BDD nl all_nodes) vars
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

                
  (* Use merge_BDD_preserves_correctness *)
  gvs[] >>
  imp_res_tac merge_BDD_preserves_correctness >>
  metis_tac[]  
QED



        
(* Now the main theorem follows easily *)
Theorem bdd_optminzation1_preserves_correctness:
  ∀BDD vars rec.   
    BDD_WF BDD ∧
    BDD_ordered BDD vars ∧
    fv_in_BDD rec BDD vars ∧
    consumed_dom_bdd vars BDD ∧
    correct_sem rec BDD vars ⇒
    ( BDD_WF (bdd_optminzation1 BDD) ∧
      BDD_ordered (bdd_optminzation1 BDD) vars ∧
      fv_in_BDD rec (bdd_optminzation1 BDD) vars ∧
      consumed_dom_bdd vars (bdd_optminzation1 BDD) ∧
      correct_sem rec (bdd_optminzation1 BDD) vars
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
  ∀BDD nl all_nodes vars rec.
    BDD_WF BDD ∧
    BDD_ordered BDD vars ∧
    fv_in_BDD rec BDD vars ∧
    consumed_dom_bdd vars BDD ∧
    correct_sem rec BDD vars  ⇒
    (BDD_WF (operate_opt2 BDD nl all_nodes) ∧
     BDD_ordered (operate_opt2 BDD nl all_nodes) vars ∧
     fv_in_BDD rec (operate_opt2 BDD nl all_nodes) vars ∧
     consumed_dom_bdd vars (operate_opt2 BDD nl all_nodes) ∧
     correct_sem rec (operate_opt2 BDD nl all_nodes) vars
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

                
  (* Use merge_BDD_preserves_correctness *)
  gvs[] >>
  imp_res_tac eliminate_BDD_preserves_correctness >>
  metis_tac[]  
QED



        
(* Now the main theorem follows easily *)
Theorem bdd_optminzation2_preserves_correctness:
  ∀BDD vars rec.   
    BDD_WF BDD ∧
    BDD_ordered BDD vars ∧
    fv_in_BDD rec BDD vars ∧
    consumed_dom_bdd vars BDD ∧
    correct_sem rec BDD vars ⇒
    ( BDD_WF (bdd_optminzation2 BDD) ∧
      BDD_ordered (bdd_optminzation2 BDD) vars ∧
      fv_in_BDD rec (bdd_optminzation2 BDD) vars ∧
      consumed_dom_bdd vars (bdd_optminzation2 BDD) ∧
      correct_sem rec (bdd_optminzation2 BDD) vars
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
  ∀BDD vars rec.
    BDD_WF BDD ∧
    BDD_ordered BDD vars ∧
    fv_in_BDD rec BDD vars ∧
    consumed_dom_bdd vars BDD ∧
    correct_sem rec BDD vars ⇒
    (
    BDD_WF (bdd_one_round BDD) ∧
    BDD_ordered (bdd_one_round BDD) vars ∧
    fv_in_BDD rec (bdd_one_round BDD) vars ∧
    consumed_dom_bdd vars (bdd_one_round BDD) ∧
    correct_sem rec (bdd_one_round BDD) vars
    )            
Proof
  rw[bdd_one_round_def] >>
  imp_res_tac bdd_optminzation2_preserves_correctness >>
  imp_res_tac bdd_optminzation1_preserves_correctness
QED




        

        
(* Main theorem using strong induction on the termination measure *)
Theorem bdd_full_optimize_preserves_correctness:
  ∀BDD vars rec.
    BDD_WF BDD ∧
    BDD_ordered BDD vars ∧
    fv_in_BDD rec BDD vars ∧
    consumed_dom_bdd vars BDD ∧
    correct_sem rec BDD vars ⇒
    (
    BDD_WF (bdd_full_optimize BDD) ∧
    BDD_ordered (bdd_full_optimize BDD) vars ∧
    fv_in_BDD rec (bdd_full_optimize BDD) vars ∧
    consumed_dom_bdd vars (bdd_full_optimize BDD) ∧
    correct_sem rec (bdd_full_optimize BDD) vars
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


(* TODO: now add those in Valid_BDD rec (BDD:('a,'b)BDD) vars *)
(* make sure that also you add the _opt version here *)

val _ = export_theory ();

