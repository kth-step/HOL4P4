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
(*                                                     *)
(*         Optimzations and their termination          *)
(*                       proofs                        *)
(*                                                     *)
(*******************************************************)


(*

TODO before start with user input:
prove these about the merge:
fv_in_BDD rec (merge BDD n h) vars ⇒
        BDD_ordered (merge BDD n h) vars ⇒
        consumed_dom_bdd vars (merge BDD n h) ⇒
        BDD_WF (merge BDD n h)


finish the same proof for eliminate
        
To do, edit the rot that it can contain terminal or ntl, not internal node in wfness
NO NEED to set up root in WFness for teh proof producing patr, just add in eliminate 0

make execurable versions of the correccness, WFness and order and other things.

move the auxiliary functions to BDD aux

     check slow theorems for merge and make them fast using the new work

     
*)


(* basic optimization application on the BDD tree *)
(* merge part *)
Definition merge_BDD_def:
  merge_BDD (BDD:('a,'b) BDD) n [] = BDD ∧
  merge_BDD (BDD:('a,'b) BDD) n (n'::nl) = 
  (case mergable BDD n n' of
   | F => merge_BDD BDD n nl
   | T => merge_BDD (merge BDD n n') n nl
  )
End


Definition operate_opt1_def:
  (operate_opt1 (BDD:('a,'b) BDD)  ([]:num list)  (all_nodes:num list) = (BDD:('a,'b) BDD)) ∧
  (operate_opt1 BDD (n::rest) all_nodes = (operate_opt1 (merge_BDD BDD n all_nodes) rest all_nodes) )   
End
        

Definition bdd_optminzation1_def:
  bdd_optminzation1 (BDD:('a,'b) BDD) =
  let (r,edges,labels) = BDD in
    let all_nodes = MAP FST labels in
        operate_opt1 BDD all_nodes all_nodes
End




        
(* eliminate part *) 
Definition eliminate_BDD_def:
  eliminate_BDD (BDD:('a,'b) BDD) n [] = BDD ∧
  eliminate_BDD (BDD:('a,'b) BDD) n (n'::nl) = 
  (case eliminable BDD n' n of
   | F => eliminate_BDD BDD n nl
   | T => eliminate_BDD (merge BDD n' n) n nl
  )
End

Definition operate_opt2_def:
  (operate_opt2 (BDD:('a,'b) BDD) ([]:num list)   (all_nodes:num list) = (BDD:('a,'b) BDD)) ∧
  (operate_opt2 BDD (n::rest) all_nodes =  (operate_opt2 (eliminate_BDD BDD n all_nodes) rest all_nodes)) 
End
  
Definition bdd_optminzation2_def:
  bdd_optminzation2 (BDD:('a,'b) BDD) =
  let (r,edges,labels) = BDD in
    let all_nodes = MAP FST labels in
        operate_opt2 BDD all_nodes all_nodes
End




(* proof of optimization 1 merge  termination *)
(* First, we need a measure function that decreases with each optimization step *)
Definition BDD_label_length_def:
  BDD_label_length (BDD:('a,'b) BDD) =
  let (r,edges,labels) = BDD in
  LENGTH labels
End





(* termination proof *)
Theorem merge_trio_extract_triv:
  ∀ r edges labels n n'.
  merge (r,edges,labels) n n' = (r, ADELKEY n' (merge_edges edges n n'), ADELKEY n' labels)
Proof
  gvs[merge_def]
QED
        

        
Theorem merge_length_labels_less:
  ∀ r edges labels n n'.
    MEM n' (MAP FST labels) ⇒
        BDD_label_length (merge (r,edges,labels) n n') < BDD_label_length (r,edges,labels)
Proof
  gvs[BDD_label_length_def, merge_def] >>
  Induct_on ‘labels’ >>
  rpt strip_tac >>
  gvs[] >|[
    PairCases_on ‘h’ >> gvs[ADELKEY_def, SUC_ADD_ONE] >>
    ‘LENGTH (FILTER (λp. FST p ≠ h0) labels) ≤ LENGTH labels’ by gvs[LENGTH_FILTER_LEQ] >>
    decide_tac
    ,
    res_tac >>
    gvs[ADELKEY_def, SUC_ADD_ONE] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
    gvs[ADELKEY_def, SUC_ADD_ONE] >>
    ‘LENGTH (FILTER (λp. FST p ≠ FST h) labels) ≤ LENGTH labels’ by gvs[LENGTH_FILTER_LEQ] >>
    decide_tac
  ]       
QED




        
        

Theorem BDD_label_length_neq:
  ∀ BDD BDD'.
    BDD_label_length BDD <  BDD_label_length BDD' ⇒  BDD ≠ BDD'
Proof
  rpt strip_tac >>
  PairCases_on ‘BDD’ >>
  PairCases_on ‘BDD'’ >>
  gvs[BDD_label_length_def] 
QED
      


Theorem merge_decrease:
  ∀ BDD n n'.
    mergable BDD n n' ⇒
    BDD_label_length (merge BDD n n') < BDD_label_length BDD
Proof
  rpt strip_tac >>
  PairCases_on ‘BDD’ >>
  rename1 ‘(r,edges,labels)’ >>
  gvs[mergable_def] >>
  ‘MEM n' (MAP FST labels)’ by gvs[ALOOKUP_NONE] >>
  gvs[merge_length_labels_less]
QED

  
Theorem merge_BDD_decrease:
  ∀ l BDD n .      
    merge_BDD BDD n l ≠ BDD ⇒
    BDD_label_length (merge_BDD BDD n l) <  BDD_label_length BDD
Proof
  Induct_on ‘l’ >>
  rpt strip_tac >>
  gvs[merge_BDD_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> rgs[]) >>
  Cases_on ‘(merge BDD n h) = BDD’ >> gvs[] >>
  first_x_assum (strip_assume_tac o (Q.SPECL [‘(merge BDD n h)’, ‘n’])) >>
  gvs[] >>
    
  ‘BDD_label_length (merge BDD n h)  < BDD_label_length BDD’ by gvs[merge_decrease] >>
  imp_res_tac BDD_label_length_neq >>
  Cases_on ‘merge_BDD (merge BDD n h) n l = merge BDD n h’ >> gvs[]                                     
QED



Theorem ADELKEY_LENGTH_BOUND:
  ∀ l c n. LENGTH l < c ⇒
           LENGTH (ADELKEY n l) < c
Proof
  Induct >>
  rw[ADELKEY_def] >>
  PairCases_on ‘h’ >> gvs[ADELKEY_def, SUC_ADD_ONE] >>
  res_tac >>                    
  ‘LENGTH (FILTER (λp. FST p ≠ n) l) ≤ LENGTH l’ by gvs[LENGTH_FILTER_LEQ] >>
  decide_tac
QED



                   
Theorem merge_less_than_const:
  ∀ BDD n n' c.
    BDD_label_length BDD < c ∧
    mergable BDD n n' ⇒
    BDD_label_length (merge BDD n n') < c
Proof        
  rpt strip_tac >>
  PairCases_on ‘BDD’ >>
  rename1 ‘(r,edges,labels)’ >>
  gvs[mergable_def] >>
  gvs[merge_trio_extract_triv, BDD_label_length_def] >>
  gvs[ADELKEY_LENGTH_BOUND]             
QED

             
Theorem eliminate_decrease:
  ∀ BDD h n.
    eliminable BDD h n ⇒
    BDD_label_length (merge BDD h n) < BDD_label_length BDD
Proof
  rpt strip_tac >>
  PairCases_on ‘BDD’ >>
  rename1 ‘(r,edges,labels)’ >>
  gvs[eliminable_def] >>
                       
  ‘MEM n (MAP FST labels)’ by gvs[ALOOKUP_NONE] >>
  gvs[merge_length_labels_less]
QED

Theorem merge_BDD_less_than_const:
  ∀ l BDD n c .
    BDD_label_length BDD < c ⇒
    (BDD_label_length (merge_BDD BDD n l) < c ∧ BDD_label_length (eliminate_BDD BDD n l) < c) 
Proof

  Induct >>
  rpt strip_tac >>
  gvs[merge_BDD_def, eliminate_BDD_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> rgs[]) >>
  res_tac >|[
      
    Cases_on ‘(merge BDD n h) = BDD’ >> gvs[] >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘(merge BDD n h)’, ‘n’, ‘c’])) >>
    gvs[] >>
    
    ‘BDD_label_length (merge BDD n h)  < BDD_label_length BDD’ by gvs[merge_decrease] >>
    imp_res_tac BDD_label_length_neq >>
    Cases_on ‘merge_BDD (merge BDD n h) n l = merge BDD n h’ >> gvs[]       
    ,

           
    Cases_on ‘(merge BDD h n) = BDD’ >> gvs[] >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘(merge BDD h n)’, ‘n’, ‘c’])) >>
    gvs[] >>
    
    ‘BDD_label_length (merge BDD h n)  < BDD_label_length BDD’ by gvs[eliminate_decrease] >>
    imp_res_tac BDD_label_length_neq >>
    Cases_on ‘merge_BDD (merge BDD n h) n l = merge BDD n h’ >> gvs[]    
    
  ]
QED


        


        
        
        
Theorem less_imp_less_in_length_label:
  ∀ BDD (n:num) l l'.
    (BDD_label_length BDD < n ⇒
     BDD_label_length  (operate_opt1 BDD  l l') <  n ∧
     BDD_label_length  (operate_opt2 BDD  l l') <  n)
    
Proof
  Induct_on ‘l’ >>
  gvs[operate_opt1_def, operate_opt2_def] >>
  rpt strip_tac >>
  res_tac >>

  ‘BDD_label_length (merge_BDD BDD h l')  < n’ by gvs[merge_BDD_less_than_const] >>
  ‘BDD_label_length (eliminate_BDD BDD h l')  < n’ by gvs[merge_BDD_less_than_const] >> 

  res_tac >>
  gvs[]
QED



Theorem less_imp_less_in_length_bdd_optminzation:
  ∀ BDD (n:num).
    (BDD_label_length BDD < n ⇒
     BDD_label_length  (bdd_optminzation1 BDD) <  n ∧
     BDD_label_length  (bdd_optminzation2 BDD) <  n)
    
Proof
  gvs[bdd_optminzation1_def, bdd_optminzation2_def] >>
  rpt strip_tac >>
  imp_res_tac less_imp_less_in_length_label >>
  PairCases_on ‘BDD’ >> gvs[]   
QED


    
Theorem operate_opt1_decrease:  
  ∀ BDD l l'.
    operate_opt1 BDD l l' ≠ BDD
    ⇒
    (λ(r,edges,labels). LENGTH labels) (operate_opt1 BDD l l') < BDD_label_length BDD
Proof
  Induct_on ‘l’ >> gvs[] >>
  rpt strip_tac >-
   gvs[operate_opt1_def] >>
  PairCases_on ‘BDD’ >>
  rename1 ‘(r,edges,labels)’ >>
  rw[] >>
  gvs[operate_opt1_def] >>
  res_tac >>
  Cases_on ‘merge_BDD (r,edges,labels) h l' = (r,edges,labels)’ >> gvs[] >>
  imp_res_tac merge_BDD_decrease >>
  imp_res_tac less_imp_less_in_length_label >>
  gvs[BDD_label_length_def]
QED  
      



      
Theorem bdd_optminzation1_decreases:
  ∀BDD. bdd_optminzation1 BDD ≠ BDD ⇒
        BDD_label_length (bdd_optminzation1 BDD) < BDD_label_length BDD
Proof

  rw[bdd_optminzation1_def] >>                       
  PairCases_on ‘BDD’ >>
  rename1 ‘(r,edges,labels)’ >>
  rw[] >>
  gvs[] >>
       
  imp_res_tac operate_opt1_decrease >> 
  rw[operate_opt1_def] >>
  gvs[BDD_label_length_def]
QED

        
Theorem bdd_optminzation1_decreases_verbose:
  ∀r edges labels . bdd_optminzation1 (r,edges,labels) ≠ (r,edges,labels) ⇒
        BDD_label_length (bdd_optminzation1 (r,edges,labels)) < BDD_label_length (r,edges,labels)
Proof
  metis_tac[bdd_optminzation1_decreases]
QED

        



Theorem eliminate_BDD_decrease:        
  ∀ l BDD n .      
    eliminate_BDD BDD n l ≠ BDD ⇒
    BDD_label_length (eliminate_BDD BDD n l) <  BDD_label_length BDD
Proof

  Induct_on ‘l’ >>
  rpt strip_tac >>
  gvs[eliminate_BDD_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> rgs[]) >>
  Cases_on ‘(merge BDD h n) = BDD’ >> gvs[] >>
  first_x_assum (strip_assume_tac o (Q.SPECL [‘(merge BDD h n)’, ‘n’])) >>
  gvs[] >>

  
  ‘BDD_label_length (merge BDD h n) < BDD_label_length BDD’ by gvs[eliminate_decrease] >>
  imp_res_tac BDD_label_length_neq >>
  Cases_on ‘eliminate_BDD (merge BDD h n) n l = merge BDD h n’ >> gvs[] 
QED
   


Theorem operate_opt2_decrease:
  ∀BDD l l'.
    operate_opt2 BDD l l' ≠ BDD ⇒
    (λ(r,edges,labels). LENGTH labels) (operate_opt2 BDD l l') <
    BDD_label_length BDD
Proof
  Induct_on ‘l’ >> gvs[] >>
  rpt strip_tac >-
   gvs[operate_opt2_def] >>
  PairCases_on ‘BDD’ >>
  rename1 ‘(r,edges,labels)’ >>
  rw[] >>
  gvs[operate_opt2_def] >>
  res_tac >>
  Cases_on ‘eliminate_BDD (r,edges,labels) h l' = (r,edges,labels)’ >> gvs[] >>
  imp_res_tac eliminate_BDD_decrease >>
  imp_res_tac less_imp_less_in_length_label >>
  gvs[BDD_label_length_def]
QED


     
Theorem bdd_optminzation2_decreases:
  ∀BDD. bdd_optminzation2 BDD ≠ BDD ⇒
        BDD_label_length (bdd_optminzation2 BDD) < BDD_label_length BDD
Proof
  rw[bdd_optminzation2_def] >>                       
  PairCases_on ‘BDD’ >>
  rename1 ‘(r,edges,labels)’ >>
  rw[] >>
  gvs[] >>
  imp_res_tac operate_opt2_decrease >> 
  rw[operate_opt2_def] >>
  gvs[BDD_label_length_def]
QED        


           
Theorem bdd_optminzationone_shot_decreases_verbose:
  ∀ r edges labels .
    bdd_optminzation2 (r,edges,labels) ≠ (r,edges,labels) ∧
    bdd_optminzation1 (bdd_optminzation2 (r,edges,labels)) ≠  (r,edges,labels) ⇒
    BDD_label_length (bdd_optminzation1 (bdd_optminzation2 (r,edges,labels))) < BDD_label_length (r,edges,labels)
Proof

  rpt strip_tac >>
  assume_tac bdd_optminzation2_decreases >>
  res_tac >>
  imp_res_tac less_imp_less_in_length_bdd_optminzation
QED



        
Definition bdd_one_round_def:
  bdd_one_round BDD = bdd_optminzation1 (bdd_optminzation2 BDD)
End



Theorem bdd_one_round_reduce:
  ∀ BDD.
  bdd_one_round BDD ≠ BDD ⇒
  BDD_label_length (bdd_one_round BDD) < BDD_label_length BDD
Proof
  rpt strip_tac >>
  PairCases_on ‘BDD’ >>
  rename1 ‘(r,edges,labels)’ >>
  gvs[bdd_one_round_def] >>
  Cases_on ‘bdd_optminzation2 (r,edges,labels) = (r,edges,labels)’ >> gvs[] >|[
    assume_tac bdd_optminzation1_decreases >>
    gvs[]
    ,
    
    Cases_on ‘bdd_optminzation1 (bdd_optminzation2 (r,edges,labels)) =
              bdd_optminzation2 (r,edges,labels)’  >> gvs[] >|[
        assume_tac bdd_optminzation2_decreases >>
        res_tac 
        ,
        assume_tac bdd_optminzationone_shot_decreases_verbose >>
        res_tac
      ]
  ]                  
QED
        

Definition bdd_full_optimize_def:
  bdd_full_optimize (BDD:('a,'b) BDD) =
  case bdd_one_round BDD = BDD of
  | T => BDD
  | F => bdd_full_optimize  (bdd_one_round BDD)                                      
Termination
        
  WF_REL_TAC `measure BDD_label_length` >>
  rpt strip_tac >>
      
  rename1 ‘ bdd_one_round (r,edges,labels) = (r,edges,labels)’ >>
  metis_tac[bdd_one_round_reduce]
End


(*******************************************************)
(*                                                     *)
(*         Optimzations Correctness full               *)
(*                       proofs                        *)
(*                                                     *)
(*******************************************************)


        

(* Helper lemma: merge_BDD preserves correctness
   TODO: add a def for the guarantee...
 *)
Theorem merge_BDD_preserves_correctness:
  ∀BDD n nl vars rec.
    
    BDD_WF BDD ∧
    BDD_ordered BDD vars ∧
    fv_in_BDD rec BDD vars ∧
    consumed_dom_bdd vars BDD ∧
    correct_sem rec BDD vars  ⇒
                
    (
    BDD_WF (merge_BDD BDD n nl) ∧
    BDD_ordered (merge_BDD BDD n nl) vars ∧
    fv_in_BDD rec (merge_BDD BDD n nl) vars ∧
    consumed_dom_bdd vars (merge_BDD BDD n nl) ∧
    correct_sem rec (merge_BDD BDD n nl) vars
    )
Proof
  Induct_on ‘nl’ >-
   (* Base case: empty list *)
   fs [merge_BDD_def] >>
  
  (* Inductive case *)
  rpt gen_tac >> strip_tac >>
  fs [merge_BDD_def] >>
  
  (* Case analysis on mergable BDD n h *)
  Cases_on ‘mergable BDD n h’ >> gvs[] >|[
    gvs[] >>
    assume_tac merge_correct >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘BDD’, ‘[]’, ‘vars’, ‘n’, ‘h’, ‘rec’])) >>
    gvs[] >>
    (*res_tac >>*)
    ‘BDD_WF (merge BDD n h)’ by imp_res_tac merge_wf_preservation >>
    ‘BDD_ordered (merge BDD n h) vars’ by imp_res_tac merge_order_preservation >>
    ‘fv_in_BDD rec (merge BDD n h) vars’ by (imp_res_tac merge_fv_final_preservation >>
                                             first_x_assum (strip_assume_tac o (Q.SPECL [‘h’, ‘n’]))) >>
    ‘consumed_dom_bdd vars (merge BDD n h)’ by (imp_res_tac merge_consumed_dom_final_preservation >>
                                             first_x_assum (strip_assume_tac o (Q.SPECL [‘h’, ‘n’]))) >>
    res_tac >>
    gvs[]
    , 
    metis_tac[]
  ]
QED

        


(* todo add the rest of the properties, wfness...etc in one definition*)        
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

(* TODO: move to elimination, and make this elim_correct *)
Theorem eliminate_correct_not_verbose:        
  ∀ BDD vars vars_consumed n n' rec .
    correct_sem rec BDD (vars++vars_consumed) ∧
    BDD_WF BDD ∧
    consumed_dom_bdd vars_consumed BDD ∧
    BDD_ordered BDD vars_consumed ∧
    fv_in_BDD rec BDD (vars++vars_consumed)  ∧
    eliminable BDD n n'
    ==>
    correct_sem rec (merge BDD n n')  (vars++vars_consumed)
Proof
  rpt strip_tac >>
  rw[] >>
  
  PairCases_on ‘BDD’ >>
  rename1 ‘(root, edges, labels)’ >>
 metis_tac[eliminate_correct]
QED



                
Theorem eliminate_BDD_preserves_correctness:
  ∀BDD n nl vars rec.
    
    BDD_WF BDD ∧
    BDD_ordered BDD vars ∧
    fv_in_BDD rec BDD vars ∧
    consumed_dom_bdd vars BDD ∧
    correct_sem rec BDD vars  ⇒
                
    (
    BDD_WF (eliminate_BDD BDD n nl) ∧
    BDD_ordered (eliminate_BDD BDD n nl) vars ∧
    fv_in_BDD rec (eliminate_BDD BDD n nl) vars ∧
    consumed_dom_bdd vars (eliminate_BDD BDD n nl) ∧
    correct_sem rec (eliminate_BDD BDD n nl) vars
    )
Proof
  Induct_on ‘nl’ >-
   (* Base case: empty list *)
   fs [eliminate_BDD_def] >>
  
  (* Inductive case *)
  rpt gen_tac >> strip_tac >>
  fs [eliminate_BDD_def] >>
  
  Cases_on ‘eliminable BDD h n’ >> gvs[] >|[
    gvs[] >>
    assume_tac eliminate_correct_not_verbose >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘BDD’, ‘[]’, ‘vars’, ‘h’, ‘n’, ‘rec’])) >>
    gvs[] >>
    (*res_tac >>*)
    ‘BDD_WF (merge BDD h n)’ by imp_res_tac eliminate_wf_preservation >>
    ‘BDD_ordered (merge BDD h n) vars’ by imp_res_tac eliminate_order_preservation >>
    ‘fv_in_BDD rec (merge BDD h n) vars’ by (imp_res_tac merge_fv_final_preservation >>
                                             first_x_assum (strip_assume_tac o (Q.SPECL [‘n’, ‘h’]))) >>
    imp_res_tac merge_consumed_dom_final_preservation >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘n’, ‘h’]) ) >>
    gvs[]>>

        
    res_tac >>
    gvs[]
    , 
    metis_tac[]
  ]
QED

        


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




val _ = export_theory ();

