open HolKernel boolLib liteLib simpLib Parse bossLib;
open arithmeticTheory stringTheory containerTheory pred_setTheory
     listTheory finite_mapTheory;

open bitstringTheory;
open wordsTheory;
open optionTheory;
open sumTheory;
open ottTheory;
open pairTheory;
open rich_listTheory;
open alistTheory;
open numeralTheory;
open set_relationTheory;
open pred_setLib;

open p4_auxTheory;

open bdd_auxTheory;          
open bdd_genTheory;     
open bdd_gen_wfTheory;     
open bdd_gen_orderTheory;
open bdd_gen_correctTheory;
open bdd_isomorphTheory;

open bdd_gen_optimizationTheory;

open pred_specTheory;     
open policy_specTheory;
open tables_specTheory;



     
     
val _ = new_theory "bdd_end_to_end";


        
Theorem correct_sem_policy_structure_root:
  ∀ var_policy vars.
    correct_sem policy_structure (0,[],[(0,non_termn (NONE,var_policy))]) (REVERSE vars)
Proof
  gvs[correct_sem_def] >>
  rpt strip_tac >>
  Cases_on ‘n’ >>
  gvs[Once BDD_sem_cases] >>
  gvs[from_formula_to_action_def] >>
  gvs[get_prop_def, op_sem_def]
QED


        
Theorem correct_sem_table_structure_root:
  ∀ var_table vars.
    correct_sem table_structure (0,[],[(0,non_termn (NONE,var_table))]) (REVERSE vars)
Proof
  gvs[correct_sem_def] >>
  rpt strip_tac >>
  Cases_on ‘n’ >>
  gvs[Once BDD_sem_cases] >>
  gvs[from_formula_to_action_def] >>
  gvs[get_prop_def, op_sem_def]
QED


Triviality BDD_WF_init:        
  ∀ n n' prop.
    BDD_WF (n,[],[(n,non_termn (NONE,prop))])
Proof
  gvs[BDD_WF_def, dom_range_edges_def]
QED


Triviality BDD_ordered_init:
    ∀ n n' prop vars_consumed.      
      BDD_ordered (n,[],[(n,non_termn (NONE,prop))]) vars_consumed
Proof
  gvs[BDD_ordered_def]
QED


Triviality range_c_init:
    ∀ n  prop vars_consumed.      
      range_c 1 (n,[],[(0,non_termn (NONE,prop))])
Proof
  gvs[range_c_def]
QED

        
Triviality fv_vars_reverse:                           
  ∀ vars rec prop.
    fv_in_vars rec prop vars = fv_in_vars rec prop (REVERSE vars)
Proof
  rpt strip_tac >>
  gvs[fv_in_vars_def]
QED

        
Triviality consumed_dom_bdd_init:
  ∀ n n' prop.
  consumed_dom_bdd [] (n,[],[(n',non_termn (NONE,prop))])
Proof
  gvs[consumed_dom_bdd_def]
QED   




Triviality mem_lookup_local_triv:        
  ∀ l n .
    MEM n (MAP FST l) ⇒
    ∃ elem. ALOOKUP l n= SOME elem
Proof
  Induct >>
  gvs[] >>
  rpt strip_tac >>
  PairCases_on ‘h’ >> gvs[] >>
  rgs[AllCaseEqs()]  >>
  res_tac >>
  gvs[] >>
  Cases_on ‘h0 = n’ >> gvs[]
QED

        
Definition non_termn_type_def:
  non_termn_type n BDD =
  let (r,edges,labels) = BDD in
  (case ALOOKUP labels n of
   | SOME (non_termn (x,p)) => T
   | _ => F
  )         
End

        
(* this theorem is for BDD without optimizations!*)      
Theorem policy_mk_bdd_correct_thm:
  ∀ var_policy vars BDD mv.
    ALL_DISTINCT vars ∧
    fv_in_vars policy_structure var_policy vars ∧
    SOME BDD = mk_BDDPred policy_structure (0,[],[(0, non_termn (NONE, var_policy))]) [] vars 1 ⇒
    correct_sem policy_structure BDD (REVERSE vars)
Proof
  rpt strip_tac >>                            
  assume_tac (INST_TYPE [“:'a” |-> “: (pred # 'a) list”, “:'b” |-> “: 'a”] correct_sem_translation)  >>
  first_x_assum (strip_assume_tac o (Q.SPECL [‘vars’, ‘[]’,
                                              ‘(0,[],[(0,non_termn (NONE,(var_policy : (pred # α) list)))])’,
                                              ‘BDD’, ‘policy_structure’, ‘1’])) >>
  
  gvs[prop1_policy,prop2_policy,prop3_policy,prop4_policy] >>
  
  gvs[correct_sem_policy_structure_root] >>
  
  gvs[BDD_ordered_def, range_c_def] >>
  
  gvs[consumed_dom_bdd_def] >>
  
  gvs[BDD_WF_init] >>
  
  gvs[fv_in_BDD_def, fv_in_labels_def] >>
  gvs[Once fv_vars_reverse]
QED
        
Theorem table_mk_bdd_correct_thm:
  ∀ var_table vars BDD mv.
    ALL_DISTINCT vars ∧
    fv_in_vars table_structure var_table vars ∧
    SOME BDD = mk_BDDPred table_structure (0,[],[(0, non_termn (NONE, var_table))]) [] vars 1 ⇒
    correct_sem table_structure BDD (REVERSE vars)
Proof
  rpt strip_tac >>
  assume_tac (INST_TYPE [“:'a” |-> “: (('a table) list # num)”, “:'b” |-> “: 'a action_expr”] correct_sem_translation)  >>
  first_x_assum (strip_assume_tac o (Q.SPECL [‘vars’, ‘[]’,
                                              ‘(0,[],[(0,non_termn (NONE,(var_table)))])’,
                                              ‘BDD’, ‘table_structure’, ‘1’])) >>

  gvs[prop1_var_tables, prop2_var_tables, prop3_var_tables, prop4_var_tables] >>
                     
  gvs[correct_sem_table_structure_root] >>
  
  gvs[BDD_ordered_def, range_c_def] >>
  
  gvs[consumed_dom_bdd_def] >>
  
  gvs[BDD_WF_init] >>
  
  gvs[fv_in_BDD_def, fv_in_labels_def] >>
  gvs[Once fv_vars_reverse]
QED




Definition node_in_labels_def:
  node_in_labels n BDD =
  let (r,edges,labels) = BDD in
    MEM n (MAP FST labels)
End


Definition  prop_in_BDD_def: 
  prop_in_BDD n BDD =
  let (r,edges,labels) = BDD in
     get_prop labels n
End
        


Theorem BDD_sem_exsists_label_init:  
  ∀ BDD mv n vars_consumed vars rec.
    BDD_ordered BDD vars_consumed ∧
    mv_dom_vars mv (vars ++ vars_consumed)  ∧
    consumed_dom_bdd vars_consumed BDD ∧
    node_in_labels n BDD ∧  
    BDD_WF BDD ⇒
    ∃ b . BDD_sem rec BDD mv n b
Proof
              
  rgs[Once BDD_sem_cases] >>
  rpt strip_tac >>
  
  PairCases_on ‘BDD’ >>
  rename1 ‘(root,edges,labels)’ >>
   gvs[node_in_labels_def] >>

  rgs[] >>
  Cases_on ‘ALOOKUP edges n’ >> gvs[] >|[
    gvs[BDD_WF_def, is_lookup_ntl_def] >>
    Cases_on ‘edges = []’ >> gvs[] >>
    imp_res_tac distinct_mem_lookup_local >> gvs[]          
    ,
    PairCases_on ‘x’ >> gvs[] >>

    subgoal ‘∃pred x'.ALOOKUP labels n = SOME (non_termn (SOME x',pred))’ >-
     (
     ‘MEM n (dom_range_edges edges)’ by  imp_res_tac lookup_edges_in_domain >>
     gvs[BDD_WF_def, is_lookup_internal_def, lookup_is_some_def] >>
     last_x_assum (strip_assume_tac o (Q.SPECL [‘n’])) >>
     gvs[]
     ) >>
    gvs[] >>

    subgoal ‘∃b . ALOOKUP mv x' = SOME b’ >-
     (
    imp_res_tac consumed_dom_bdd_in_mv >> metis_tac[]
     ) >>

    metis_tac [BDD_sem_exsists_inter]
  ]       
QED



Triviality mem_non_term_leaf_updt:
∀ labels n h.
MEM n (MAP FST labels) ⇒
MEM n (MAP FST (non_term_leaf_updt labels h))
Proof
  Induct >>
  gvs[non_term_leaf_updt_def] >>
  rpt strip_tac >|[
    PairCases_on ‘h’ >> gvs[] >>
    rpt (BasicProvers.full_case_tac >> gvs[])
    ,
    res_tac >>
    gvs[]
  ]
QED



        

Theorem  body_of_mk_mem_init:
  ∀ r edges labels r' edges' labels' n n' c' h rec.
   BDD_WF (r',edges',labels') ∧
  MEM n (MAP FST labels) ∧
  body_of_mk rec (r,edges,labels) h n' = SOME ((r',edges',labels'),c') ⇒
  MEM n (MAP FST labels') ∧ prop_in_BDD n (r,edges,labels) = prop_in_BDD n (r',edges',labels')
Proof
  rpt strip_tac >>
  imp_res_tac body_of_mk_output >>
  gvs[] >>
  
  imp_res_tac mem_non_term_leaf_updt >>
  gvs[prop_in_BDD_def, get_prop_def, ALOOKUP_APPEND] >>

  rpt (
    
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>           
    imp_res_tac lookup_ntl_updt_none >>
    imp_res_tac lookup_non_term_leaf_updt_internal >>
    
    imp_res_tac lookup_labels_in_updt_none >>
    imp_res_tac lookup_labels_in_updt >>
    
    imp_res_tac non_term_leaf_updt_imp_term >>
    imp_res_tac non_term_leaf_updt_imp_not_ntl >>
    gvs[] >>
    
    gvs[ALOOKUP_APPEND] >>
    
    imp_res_tac mem_lookup_local_triv >>
    gvs[] >>
    
    gvs[BDD_WF_def, ALL_DISTINCT_APPEND] >>
    gvs[] >>
    Cases_on ‘q'’ >> gvs[]
    )   
QED




      
Theorem node_indeed_in_final_bdd:
  ∀ rec vars vars_consumed BDD BDD' n n'.
    range_c n' BDD ∧
    node_in_labels n BDD ∧
    BDD_WF BDD ∧
    SOME BDD' = mk_BDDPred rec BDD vars_consumed vars n' ⇒
    (node_in_labels n BDD' ∧ (prop_in_BDD n BDD = prop_in_BDD n BDD'))
Proof
  Induct_on ‘vars’>>
  rpt strip_tac >-
   gvs[node_in_labels_def, mk_BDDPred_def, prop_in_BDD_def, get_prop_def] >-
   gvs[node_in_labels_def, mk_BDDPred_def, prop_in_BDD_def, get_prop_def] >>
 
  PairCases_on ‘BDD’ >>
  rename1 ‘BDD_WF (r,edges,labels)’ >>
  
  PairCases_on ‘BDD'’ >>
  rename1 ‘SOME (r',edges',labels') = mk_BDDPred rec (r,edges,labels) vars_consumed (h::vars) n'’ >>

  gvs[node_in_labels_def] >>
  gvs[mk_BDDPred_def] >>
  gvs[AllCaseEqs()] >>

  imp_res_tac WFness_translation_inter >>
  imp_res_tac WFness_range_c_inter >>
  
  PairCases_on ‘BDD'’ >>
  rename1 ‘mk_BDDPred rec (r'',edges'',labels'') (h::vars_consumed) vars c' =
        SOME (r',edges',labels')’ >>

  assume_tac body_of_mk_mem_init >>
  first_x_assum (strip_assume_tac o (Q.SPECL [ ‘r’, ‘edges’, ‘labels’, ‘r''’, ‘edges''’, ‘labels''’,
                                              ‘n’, ‘n'’, ‘c'’, ‘h’, ‘rec’])) >>
  
  gvs[] >>

  first_x_assum (strip_assume_tac o (Q.SPECL [ ‘rec’, ‘h::vars_consumed’, ‘(r'',edges'',labels'')’,
                                               ‘(r',edges',labels')’, ‘n’, ‘c'’])) >>
  gvs[]                                        
QED

              


Triviality final_sem_eq_triv:        
∀ labels labels' var_policy var_table mv.
        
(
op_sem policy_structure (get_prop labels 0) mv =
op_sem table_structure (get_prop labels' 0) mv
) ∧
get_prop labels 0 = SOME var_policy ∧
get_prop labels' 0 = SOME var_table
⇒
  sem_policy var_policy mv = sem_tables var_table mv
Proof

rpt strip_tac >>
gvs[op_sem_def, policy_structure_def, table_structure_def]
QED





Triviality node_in_bdd_mk_init_triv:
  ∀ n r labels r' edges' labels' c h rec.
    non_termn_type r (r,[],labels) ∧
    body_of_mk rec (r,[],labels) h 1 =
    SOME ((r',edges',labels'),c)⇒
    node_in_BDD r (r',edges',labels')
Proof
  rpt strip_tac >>
  
  rgs[body_of_mk_def] >>
  rgs[AllCaseEqs()]>>
  
  gvs[getLeaves_def, getLabels_def, leaves_pred_sub_def, simp_pred_list_def] >>
  gvs[determine_termn_list_def, determine_termn_def, mk_new_edges_def] >>
  gvs[node_in_BDD_def] >>
  gvs[extract_nontermn_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>           
  gvs[mk_new_edges_def, dom_range_edges_def] >>
  gvs[non_termn_type_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  gvs[extract_nontermn_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>           
  gvs[mk_new_edges_def, dom_range_edges_def]
QED

        


        
        
Theorem correct_var_policy_var_tables_thm1:
  ∀ var_policy var_table I vars BDD BDD' mv.
    
    isIsomorph I BDD BDD' ∧
    ALOOKUP I 0 = SOME 0 ∧
    node_in_BDD 0 BDD ∧
             
    SOME BDD = mk_BDDPred policy_structure (0,[],[(0, non_termn (NONE, var_policy))]) [] vars 1 ∧
    SOME BDD'= mk_BDDPred table_structure  (0,[],[(0, non_termn (NONE, var_table ))]) [] vars 1 ∧
  
    (fv_in_vars table_structure var_table vars ∧
     fv_in_vars policy_structure var_policy vars ∧
     ALL_DISTINCT vars ∧
     mv_dom_vars mv vars ∧
     vars ≠ [] )

    ⇒
    sem_policy var_policy mv = sem_tables var_table mv
Proof
                                                  
  rpt strip_tac >>

  (* 1. we know that given this layout of initial BDD, then
     for sure the final BDDs are correct w.r.t. any node *)
  imp_res_tac table_mk_bdd_correct_thm >>
  imp_res_tac policy_mk_bdd_correct_thm >>

            
  (* 2. from exsistance of the semantics theorem we know that indeed there is an answer b and b',
     to do so: *)
  (* 2.1 we need to show that the translation to BDD is ordered, and well formed *)
  subgoal ‘BDD_ordered BDD' (REVERSE vars) ∧
           BDD_ordered BDD (REVERSE vars) ∧
           consumed_dom_bdd (REVERSE vars) BDD' ∧
           consumed_dom_bdd (REVERSE vars) BDD ∧
           BDD_WF BDD' ∧ BDD_WF BDD ’ >- 
   (imp_res_tac order_translation >>
    gvs[consumed_dom_bdd_init, BDD_WF_init, BDD_ordered_init, range_c_init]) >>

            
  (* 2.2 now we can show that exists answer *) 
  subgoal ‘∃ b. BDD_sem policy_structure BDD mv 0 b ∧
           ∃ b'. BDD_sem table_structure BDD' mv 0 b'’ >-
   (
        
   imp_res_tac node_indeed_in_final_bdd >>
   gvs[BDD_WF_init, range_c_init] >>
   first_x_assum (strip_assume_tac o (Q.SPECL [‘0’])) >> 
   gvs[node_in_labels_def] >> res_tac >>

        
   ‘node_in_labels 0 BDD’ by gvs[node_in_labels_def] >>
   ‘node_in_labels 0 BDD'’ by gvs[node_in_labels_def] >>
   ‘mv_dom_vars mv ([] ⧺ REVERSE vars)’ by gvs[mv_dom_vars_def] >>
   imp_res_tac BDD_sem_exsists_label_init >> 
   gvs[]
   ) >>         


  PairCases_on ‘BDD’  >> rename1 ‘BDD_sem policy_structure (r, edges, labels ) mv 0 b’ >>
  PairCases_on ‘BDD'’ >> rename1 ‘BDD_sem table_structure  (r',edges',labels') mv 0 b'’ >>

  (* 3. now we can show that for the root node's contents (policy and table),
        it's BDD semantics is teh same as we gave in the BDD semantics *)             
  subgoal ‘(b  = op_sem policy_structure (get_prop labels  0) mv) ∧
           (b' = op_sem table_structure  (get_prop labels' 0) mv )’ >-
   (
   ‘mv_dom_vars mv (REVERSE vars)’ by gvs[mv_dom_vars_def] >>
   gvs[correct_sem_def] >>
   res_tac >>
   gvs[]
   ) >>
  
 
  subgoal ‘BDD_sem policy_structure (r,edges,labels) mv 0 b ⇔
           BDD_sem table_structure (r',edges',labels') mv 0 b’ >- (
  ‘mv_dom_vars mv (REVERSE vars)’ by gvs[mv_dom_vars_def] >>
  irule isomorphism_preserves_semantics >>
  srw_tac [SatisfySimps.SATISFY_ss][] >>
  qexistsl_tac [‘REVERSE vars’] >> gvs[]
  ) >>
  
  
  
  subgoal ‘get_prop labels 0 = SOME var_policy ∧
           get_prop labels' 0 = SOME var_table’ >- (
  
  imp_res_tac node_indeed_in_final_bdd >>
  gvs[BDD_WF_init, range_c_init] >>
  first_x_assum (strip_assume_tac o (Q.SPECL [‘0’])) >> 
  gvs[node_in_labels_def, prop_in_BDD_def, get_prop_def] >> res_tac >> gvs[]
  ) >>
  
  
  gvs[] >>    
  ‘op_sem policy_structure (SOME var_policy) mv =
   op_sem table_structure (SOME var_table) mv’ by imp_res_tac BDD_sem_determ >>
  gvs[] >>
  
  imp_res_tac final_sem_eq_triv >>
  gvs[op_sem_def, policy_structure_def, table_structure_def]
QED


    

 

val _ = export_theory ();
