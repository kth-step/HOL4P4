open HolKernel boolLib simpLib Parse bossLib;

open listTheory;
open alistTheory;
open rich_listTheory;

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




Theorem merge_safe_preserves_valid_and_correctness:
  ∀ BDD b_BDD' rec vars_consumed vars n n' c.
    
    valid_BDD rec BDD vars vars_consumed ∧
    correct_sem rec BDD (REVERSE vars ⧺ vars_consumed) ∧
    range_c c BDD ∧
    
    b_BDD' = merge_safe BDD n n' ⇒
    
    (valid_BDD rec (SND b_BDD') vars vars_consumed ∧
     correct_sem rec (SND b_BDD') (REVERSE vars ⧺ vars_consumed) ∧
     range_c c (SND b_BDD')
     )
Proof
  rw[merge_safe_def] >>
  Cases_on ‘mergable BDD n n'’ >> gvs[] >|[
    gvs[valid_BDD_def] >>
    ‘BDD_WF (merge BDD n n')’ by imp_res_tac merge_wf_preservation >>
    ‘BDD_ordered (merge BDD n n') vars_consumed’ by imp_res_tac merge_order_preservation >>
    ‘fv_in_BDD rec (merge BDD n n') (REVERSE vars ⧺ vars_consumed)’ by
      (imp_res_tac merge_fv_final_preservation >>
       first_x_assum (strip_assume_tac o (Q.SPECL [‘n'’, ‘n’]))) >>
    ‘consumed_dom_bdd vars_consumed (merge BDD n n')’ by
      (imp_res_tac merge_consumed_dom_final_preservation >>
       first_x_assum (strip_assume_tac o (Q.SPECL [‘n'’, ‘n’]))) >>
    
    gvs[]
    ,
    
    gvs[valid_BDD_def] >>
    assume_tac merge_correct >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘BDD’, ‘REVERSE vars’, ‘vars_consumed’, ‘n’, ‘n'’, ‘rec’])) >>
    gvs[]
    ,
    gvs[merge_range_preservation]
  ]
QED


        
Theorem eliminate_safe_preserves_valid_and_correctness:
  ∀ BDD b_BDD' rec vars_consumed vars n c.
    
    valid_BDD rec BDD vars vars_consumed ∧
    correct_sem rec BDD (REVERSE vars ⧺ vars_consumed) ∧
    range_c c BDD ∧
    
    b_BDD' = eliminate_safe BDD n ⇒
    
    (valid_BDD rec (SND b_BDD') vars vars_consumed ∧
     correct_sem rec (SND b_BDD') (REVERSE vars ⧺ vars_consumed)∧
     range_c c (SND b_BDD'))
Proof
  rw[eliminate_safe_def] >>
  Cases_on ‘eliminable BDD n’ >> gvs[] >|[
    gvs[valid_BDD_def] >>
    ‘BDD_WF (merge BDD x n)’ by imp_res_tac eliminate_wf_preservation >>
    ‘BDD_ordered (merge BDD x n) vars_consumed’ by imp_res_tac eliminate_order_preservation >>
    ‘fv_in_BDD rec (merge BDD x n) (REVERSE vars ⧺ vars_consumed)’ by
      (imp_res_tac merge_fv_final_preservation >>
       first_x_assum (strip_assume_tac o (Q.SPECL [‘n’, ‘x’]))) >>
    imp_res_tac merge_consumed_dom_final_preservation >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘n’, ‘x’]) ) >>
    gvs[]
    ,
    gvs[valid_BDD_def] >>
    assume_tac eliminate_correct >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘BDD’, ‘REVERSE vars’, ‘vars_consumed’, ‘x’, ‘n’, ‘rec’])) >>
    gvs[]
    ,
    gvs[merge_range_preservation]
  ]
QED
                                         



Theorem optimize_node_preserves_valid_and_correctness:
  ∀ BDD BDD' rec vars_consumed vars edges_proj labels_proj nl n c.
    
    valid_BDD rec BDD vars vars_consumed ∧
    correct_sem rec BDD (REVERSE vars ⧺ vars_consumed) ∧
    range_c c BDD ∧
            
    BDD' = optimize_node edges_proj labels_proj BDD n nl ⇒
    
    (valid_BDD rec BDD' vars vars_consumed ∧
     correct_sem rec BDD' (REVERSE vars ⧺ vars_consumed) ∧
     range_c c BDD') 
Proof
  
  Induct_on ‘nl’ >> rpt gen_tac >> strip_tac >|[
    gvs[optimize_node_def] >>
    metis_tac[eliminate_safe_preserves_valid_and_correctness]
    ,
    rgs[optimize_node_def] >>
    Cases_on ‘eliminable_projection edges_proj n’ >> rgs[] >|[
        Cases_on ‘mergable_projection edges_proj labels_proj h n’ >> rgs[] >>
        Cases_on ‘merge_safe BDD h n ’ >> rgs[] >>
        Cases_on ‘q’ >> gvs[] >>
        
        imp_res_tac merge_safe_preserves_valid_and_correctness >>
        gvs[] >>
        first_x_assum (strip_assume_tac o (Q.SPECL [‘n’, ‘h’, ‘vars_consumed’, ‘vars’, ‘rec’])) >>
        first_x_assum (strip_assume_tac o (Q.SPECL [‘n’, ‘h’, ‘vars_consumed’, ‘vars’, ‘rec’])) >>
        first_x_assum (strip_assume_tac o (Q.SPECL [‘n’, ‘h’, ‘c’])) >>
        gvs[] >>

        res_tac >>
        metis_tac[]
        ,
        metis_tac[eliminate_safe_preserves_valid_and_correctness]  
      ]                                                                                             
  ]
QED



      

Theorem optimize_layer_preserves_valid_and_correctness:
  ∀ nl BDD BDD' rec vars_consumed vars edges_proj labels_proj c.
       
    valid_BDD rec BDD vars vars_consumed ∧
    correct_sem rec BDD (REVERSE vars ⧺ vars_consumed) ∧
    range_c c BDD ∧
    
    BDD' = optimize_layer edges_proj labels_proj BDD nl ⇒
         
    (valid_BDD rec BDD' vars vars_consumed ∧
     correct_sem rec BDD' (REVERSE vars ⧺ vars_consumed) ∧
     range_c c BDD')
Proof
  Induct >>
  rw[optimize_layer_def] >> gvs[] >>
  ‘∃ BDD_opt . optimize_node edges_proj labels_proj BDD h nl = BDD_opt’ by gvs[] >> rgs[] >>
  metis_tac[optimize_node_preserves_valid_and_correctness]
QED


      


Theorem optimize_internals_preserves_valid_and_correctness:
  ∀ internals BDD BDD' rec vars_consumed vars c.
    valid_BDD rec BDD vars vars_consumed ∧
    correct_sem rec BDD (REVERSE vars ⧺ vars_consumed) ∧
    range_c c BDD ∧
    
    BDD' = optimize_internals BDD internals ⇒
    (correct_sem rec BDD' (REVERSE vars ⧺ vars_consumed) ∧
     valid_BDD rec BDD' vars vars_consumed ∧
     range_c c BDD')
Proof
  Induct >> rpt gen_tac >> strip_tac >>
  rgs[optimize_internals_def] >>

  PairCases_on ‘h’ >>
  Cases_on ‘h1’ >>

  rgs[optimize_internals_def] >>

  ‘∃ edges_proj . project_edges_to BDD x = edges_proj’ by gvs[] >> rgs[] >>
  ‘∃ labels_proj . project_labels_to BDD x = labels_proj’ by gvs[] >> rgs[] >>
  ‘∃ BDD1 . optimize_layer edges_proj labels_proj BDD x = BDD1’ by gvs[] >> rgs[] >>
  
  metis_tac[optimize_layer_preserves_valid_and_correctness]
QED


                              
Theorem optimize_bdd_preserves_valid_and_correctness:

 ∀ BDD BDD' vars_consumed vars rec c.
       
   valid_BDD rec BDD vars vars_consumed ∧
   correct_sem rec BDD (REVERSE vars ⧺ vars_consumed) ∧
   range_c c BDD ∧

               
   optimize_bdd BDD vars_consumed = BDD'
   ⇒
   (correct_sem rec BDD' (REVERSE vars ⧺ vars_consumed) ∧
    valid_BDD rec BDD' vars vars_consumed ∧
    range_c c BDD' )
Proof
  
  rpt gen_tac >> strip_tac >>
  rgs[optimize_bdd_def] >>
  
  ‘∃ l . bdd_distribute BDD vars_consumed = l ’ by gvs[] >> rgs[] >>
  PairCases_on ‘l’ >> rgs[] >>
  rename1 ‘(internals,ntl,tl)’ >>
  ‘∃ labels_proj_tl . project_labels_to BDD tl = labels_proj_tl’ by gvs[] >> rgs[] >>
  ‘∃ labels_proj_ntl . project_labels_to BDD ntl = labels_proj_ntl’ by gvs[] >> rgs[] >>
  ‘∃ BDD1 . optimize_layer [] labels_proj_tl BDD tl = BDD1’  by gvs[] >> rgs[] >>
  ‘∃ BDD2 . optimize_layer [] labels_proj_ntl BDD1 ntl = BDD2’  by gvs[] >> rgs[] >>
  
  
  ‘correct_sem rec BDD1 (REVERSE vars ⧺ vars_consumed) ∧
   valid_BDD rec BDD1 vars vars_consumed ∧
   range_c c BDD1’ by metis_tac[optimize_layer_preserves_valid_and_correctness] >>
  
  
  ‘correct_sem rec BDD2 (REVERSE vars ⧺ vars_consumed)∧
   valid_BDD rec BDD2 vars vars_consumed ∧
   range_c c BDD2’ by metis_tac[optimize_layer_preserves_valid_and_correctness] >>
  
  metis_tac[optimize_internals_preserves_valid_and_correctness]
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
 gvs[mk_BDDPred_opt_def] >|[
                         
    (* base case : one final optimization *)
    assume_tac optimize_bdd_preserves_valid_and_correctness >>
    gvs[] >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘BDD’, ‘vars_consumed’, ‘[]’,  ‘rec’, ‘c’])) >>
    gvs[]
          
    ,

    gvs[AllCaseEqs()] >>

    PairCases_on ‘BDD’ >>
    rename1 ‘(r,edges,labels)’ >>
 
    PairCases_on ‘BDD'’ >>
    rename1 ‘(r',edges',labels')’ >>
 
    PairCases_on ‘BDD''’ >>
    rename1‘((r'',edges'',labels''),c')’ >>
 
    gvs[valid_BDD_def] >>


    (* first show that the body of make preserves all of the desired properties *)
                       
    ‘range_c c' (r'',edges'',labels'')’ by imp_res_tac WFness_range_c_inter >>
 
    ‘BDD_WF (r'',edges'',labels'')’ by imp_res_tac WFness_translation_inter >> gvs[]>>
 
    ‘ALL_DISTINCT (h::vars_consumed)’ by gvs[ALL_DISTINCT_APPEND] >>        
    ‘BDD_ordered (r'',edges'',labels'') (h::vars_consumed)’ by
      imp_res_tac order_translation_inter >>

    ‘consumed_dom_bdd (h::vars_consumed) (r'',edges'',labels'')’ by
      imp_res_tac consumed_dom_bdd_inter >>
    
    
    assume_tac correct_sem_translation_inter >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘(r,edges,labels)’, ‘(r'',edges'',labels'')’,
                                                ‘rec’, ‘c’, ‘c'’, ‘REVERSE vars’, ‘h’, ‘vars_consumed’])) >>
    gvs[]>>
    
    ‘fv_in_BDD rec (r'',edges'',labels'') (REVERSE vars ⧺ [h] ⧺ vars_consumed)’ by
      metis_tac[fv_in_BDD_body_preserved] >>
     
    (* now we show that opt is also correct *)
    
    assume_tac optimize_bdd_preserves_valid_and_correctness >> gvs[] >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘(r'',edges'',labels'')’, ‘[h] ⧺ vars_consumed’, ‘vars’,  ‘rec’, ‘c'’])) >>
    gvs[valid_BDD_def] >>

       
    first_x_assum (strip_assume_tac o (Q.SPECL [‘[h] ⧺ vars_consumed’,
                                                ‘optimize_bdd (r'',edges'',labels'') (h::vars_consumed)’,
                                                ‘(r',edges',labels')’, ‘rec’, ‘c'’])) >>

    gvs[] 
  ]
QED 




val _ = export_theory ();

