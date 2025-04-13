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
     
val _ = new_theory "bdd_gen_correct";





Definition node_in_BDD_def:
  node_in_BDD n ((r,edges,labels):('a,'b)BDD) =
     MEM n (dom_range_edges edges)
End



val body_of_mk_pred_tac =    
( rename1 ‘getLeaves edges r = SOME leaves’ >>
  rename1 ‘getLabels labels leaves = SOME leaves_labels’ >>
  rename1 ‘extract_nontermn leaves_labels = SOME ntl’ >>
  
  ‘∃ leaves_sub . leaves_pred_sub rec ntl h = leaves_sub’ by gvs[] >>
  ‘∃ simp_leaves . simp_pred_list rec leaves_sub = simp_leaves’ by gvs[] >>
  ‘∃ simp_leaves' . determine_termn_list rec simp_leaves = simp_leaves'’ by gvs[] >>
  ‘∃ new_edges . mk_new_edges simp_leaves' c = new_edges’ by gvs[] >>
  ‘∃ new_labels . mk_new_labels simp_leaves' c = new_labels’ by gvs[] >>
  rgs[] );

  


Theorem BDD_sem_determ:
  ∀ n BDD mv b b' rec.        
    BDD_sem rec BDD mv n b ∧
    BDD_sem rec BDD mv n b' ⇒
    (b=b')
Proof
 Induct_on ‘BDD_sem’ >>        
 rpt strip_tac >>
 rgs[Once BDD_sem_cases]
QED


  
        

Theorem BDD_sem_exsists_inter:
  ∀ vars_consumed x' r edges labels mv n n' n'' p b rec.            
    BDD_ordered (r,edges,labels) vars_consumed ∧
    mv_dom_bdd mv (r,edges,labels)  ∧
    consumed_dom_bdd vars_consumed (r,edges,labels) ∧
    BDD_WF (r,edges,labels) ∧
    ALOOKUP edges n = SOME (n',n'') ∧
    ALOOKUP labels n = SOME (non_termn (SOME x',p)) ∧
    ALOOKUP mv x' = SOME b 
    ⇒
    ∃b'. ALOOKUP mv x' = SOME T ∧ BDD_sem rec (r,edges,labels) mv n' b' ∨
         ALOOKUP mv x' = SOME F ∧ BDD_sem rec (r,edges,labels) mv n'' b'
Proof
  ntac 2 strip_tac >>
  measureInduct_on `THE(INDEX_OF x' vars_consumed)` >>
  rpt strip_tac >>
  Cases_on ‘b’ >> gvs[] >>
  simp[Once BDD_sem_cases] >> rgs[] >|[

    (* case of True *)
    Cases_on ‘ALOOKUP edges n'’ >> gvs[] >>
    ‘MEM n' (dom_range_edges edges)’ by  imp_res_tac lookup_edges_in_domain >|[
      gvs[BDD_WF_def, is_lookup_ntl_def]
      ,
      
      PairCases_on ‘x’ >> gvs[] >>
      
      ‘∃p x'.ALOOKUP labels n' = SOME (non_termn (SOME x',p))’ by ( imp_res_tac WF_imp_non_leaf_lbl >> srw_tac [][]) >>

      ‘∃b . ALOOKUP mv x'' = SOME b’ by (gvs[mv_dom_bdd_def, lookup_is_some_def] >> metis_tac[]) >>
      gvs[]>>
      
      ‘MEM x' vars_consumed ∧ MEM x'' vars_consumed’ by (rgs[Once consumed_dom_bdd_def] >> metis_tac[])>>
      imp_res_tac MEM_INDEX_OF >>
      
      subgoal ‘THE (INDEX_OF x'' vars_consumed) < THE (INDEX_OF x' vars_consumed)’ >-
       (
       rgs[Once BDD_ordered_def]>>
       first_x_assum (strip_assume_tac o (Q.SPECL [‘n’,‘n'’, ‘n''’]))>>
       gvs[order_hold_def]
       ) >>
      
      first_x_assum (strip_assume_tac o (Q.SPECL [‘INDEX_OF (x'':string) (vars_consumed: string list)’])) >>
      gvs[] >>
      first_x_assum (strip_assume_tac o (Q.SPECL [‘x''’, ‘vars_consumed’])) >>
      gvs[] >>
      metis_tac[]
    ]
    ,
    
    (* case of False *)
    Cases_on ‘ALOOKUP edges n''’ >> gvs[] >>
    ‘MEM n'' (dom_range_edges edges)’ by  imp_res_tac lookup_edges_in_domain >|[
        gvs[BDD_WF_def, is_lookup_ntl_def]
        ,
        
        PairCases_on ‘x’ >> gvs[] >>
        
        ‘∃p x'.ALOOKUP labels n'' = SOME (non_termn (SOME x',p))’ by ( imp_res_tac WF_imp_non_leaf_lbl >> srw_tac [][]) >>
        
        ‘∃b . ALOOKUP mv x'' = SOME b’ by (gvs[mv_dom_bdd_def, lookup_is_some_def] >> metis_tac[]) >>
        gvs[]>>
        
        ‘MEM x' vars_consumed ∧ MEM x'' vars_consumed’ by (rgs[Once consumed_dom_bdd_def] >> metis_tac[])>>
        imp_res_tac MEM_INDEX_OF >>
        
        subgoal ‘THE (INDEX_OF x'' vars_consumed) < THE (INDEX_OF x' vars_consumed)’ >-
         (
         rgs[Once BDD_ordered_def]>>
       first_x_assum (strip_assume_tac o (Q.SPECL [‘n’,‘n'’, ‘n''’]))>>
         gvs[order_hold_def]
         ) >>
        
        first_x_assum (strip_assume_tac o (Q.SPECL [‘INDEX_OF (x'':string) (vars_consumed: string list)’])) >>
        gvs[] >>
        first_x_assum (strip_assume_tac o (Q.SPECL [‘x''’, ‘vars_consumed’])) >>
        gvs[] >>
        metis_tac[]
      ]
                                                                              
  ]          
QED




        
Theorem BDD_sem_exsists:
  ∀ BDD mv n vars_consumed rec.
    BDD_ordered BDD vars_consumed ∧
    mv_dom_bdd mv BDD  ∧
    consumed_dom_bdd vars_consumed BDD ∧
    node_in_BDD n BDD ∧   (*TODO: check this out*)
    BDD_WF BDD ⇒
    ∃ b . BDD_sem rec BDD mv n b
Proof

  rgs[Once BDD_sem_cases] >>
  rpt strip_tac >>
  
  PairCases_on ‘BDD’ >>
  rename1 ‘(root,edges,labels)’ >>

  rgs[] >>
  Cases_on ‘ALOOKUP edges n’ >> gvs[] >|[
    gvs[node_in_BDD_def] >>
    gvs[BDD_WF_def, is_lookup_ntl_def]
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
     gvs[mv_dom_bdd_def, lookup_is_some_def] >>
     metis_tac[]
     ) >>

    metis_tac [BDD_sem_exsists_inter]
  ]
QED






Theorem inner_edges_are_same_exists:
  ∀ r edges labels r' edges' labels' h c c' n n' n'' rec.
    BDD_WF (r',edges',labels') ∧
    body_of_mk rec (r,edges,labels) h c = SOME ((r',edges',labels'),c') ∧
    ALOOKUP edges n = SOME (n',n'') ⇒
    (∃ n1 n2.ALOOKUP edges' n = SOME (n1,n2) ∧ (n'=n1 ∧ n''=n2))
Proof
  rpt strip_tac >>
  gvs[body_of_mk_def] >>
  gvs[AllCaseEqs()]>>
  body_of_mk_pred_tac >>
  
  rgs[BDD_WF_def] >>
  rgs[ALOOKUP_APPEND]
QED



Theorem inner_edges_are_same:
  ∀ r edges labels r' edges' labels' h c c' n n' n'' n1 n2 rec.
    BDD_WF (r',edges',labels') ∧
    body_of_mk rec (r,edges,labels) h c = SOME ((r',edges',labels'),c') ∧
    ALOOKUP edges' n = SOME (n',n'') ∧
    ALOOKUP edges n = SOME (n1,n2) ⇒
    (n'=n1 ∧ n''=n2)
Proof
  rpt strip_tac >>
  imp_res_tac inner_edges_are_same_exists >>
  gvs[]
QED




        

Theorem inner_labels_are_same_exists:
  ∀ r edges labels r' edges' labels' h c c' n x p rec.
    BDD_WF (r',edges',labels') ∧
    body_of_mk rec (r,edges,labels) h c = SOME ((r',edges',labels'),c') ∧
    ALOOKUP labels n = SOME (non_termn (SOME x,p)) ⇒
    (∃ x' p' . ALOOKUP labels' n = SOME (non_termn (SOME x',p')) ∧ (x=x' ∧ p=p'))
Proof
  rpt strip_tac >>
  gvs[body_of_mk_def] >>
  gvs[AllCaseEqs()]>>
  body_of_mk_pred_tac >>
  
  rgs[BDD_WF_def] >>
  rgs[ALOOKUP_APPEND, ALL_DISTINCT_APPEND] >>
  rgs[AllCaseEqs()]>>
  
  Cases_on ‘ALOOKUP (non_term_leaf_updt labels h) n’ >> rgs[] >|[ 
    imp_res_tac lookup_ntl_updt_none >>
    rgs[]
    ,
    
    Cases_on ‘x'’ >> rgs[] >|[
        imp_res_tac lookup_labels_in_updt >> rgs[]
        ,
        Cases_on ‘p'’ >> rgs[] >> 
        Cases_on ‘q’ >> rgs[] >> 
        imp_res_tac lookup_labels_in_updt >> rgs[]
      ]
  ]
QED
        
  


Theorem inner_labels_are_same:
∀ r edges labels r' edges' labels' h c c' n x x' p p' rec.
BDD_WF (r',edges',labels') ∧
body_of_mk rec (r,edges,labels) h c = SOME ((r',edges',labels'),c') ∧
ALOOKUP labels n = SOME (non_termn (SOME x,p)) ∧
ALOOKUP labels' n = SOME (non_termn (SOME x',p'))⇒
(x=x' ∧ p=p')
Proof
rpt strip_tac >>
imp_res_tac inner_labels_are_same_exists >>
gvs[]
QED


(*

mv_dom_bdd mv (r,edges,labels) ∧
correct_sem rec (r,edges,labels) ∧
ALOOKUP edges n = SOME (n',n'') ∧
ALOOKUP labels n = SOME (non_termn (SOME x,p)) ∧
ALOOKUP edges n' = SOME (n1',n2') ∧
ALOOKUP labels n' = SOME (non_termn (SOME x',p')) ∧   
ALOOKUP mv x = SOME T⇒
rec.sem p' mv = rec.sem p mv

rpt strip_tac >>
gvs[correct_sem_def] >>
                     
first_x_assum (strip_assume_tac o (Q.SPECL [‘n’, ‘mv’, ‘rec.sem p mv’])) >>
rgs[op_sem_def, get_prop_def]
   subgoal ‘BDD_sem rec (r,edges,labels) mv n' (rec.sem p mv)’ >-
 (
 simp[Once BDD_sem_cases]

 )












∀ r edges labels r' edges' labels' mv n n' n'' x p c c' b vars_consumed h rec.
BDD_WF (r,edges,labels) ∧
BDD_WF (r',edges',labels') ∧
mv_dom_bdd mv (r',edges',labels') ∧
consumed_dom_bdd vars_consumed (r,edges,labels) ∧
correct_sem rec (r,edges,labels) ∧
body_of_mk rec (r,edges,labels) h c = SOME ((r',edges',labels'),c') ∧
BDD_sem rec (r',edges',labels') mv n b ∧
ALOOKUP edges' n = SOME (n',n'') ∧
ALOOKUP labels' n = SOME (non_termn (SOME x,p)) ∧
MEM n (dom_range_edges edges') ∧
ALOOKUP edges n = NONE ⇒
 b = op_sem rec (SOME p) mv


rpt strip_tac >>
 rgs[Once BDD_sem_cases] >>
‘ALOOKUP edges' n' = NONE’ by cheat >>
   ‘MEM n' (dom_range_edges edges')’ by imp_res_tac lookup_edges_in_domain >>

‘∃ b' p' .is_lookup_ntl labels' n' ∨ ALOOKUP labels' n' = SOME (termn (b',p'))’ by cheat >|[
    rgs[is_lookup_ntl_def] >>
    rgs[Once BDD_sem_cases] >>
    rgs[from_formula_to_action_def] >>
    rgs[op_sem_def] >>


    gvs[body_of_mk_def] >>
  gvs[AllCaseEqs()]>>
    body_of_mk_pred_tac >>


                        


  ]
                                                                                     

                
Induct_on ‘BDD_sem’ >>
rpt strip_tac >>
rgs[]
gvs[]

res_tac


        




                        
                                

  ∀ vars_consumed x r edges labels r' edges' labels' mv n n' n'' h c c' p b rec.                     
    BDD_ordered ((r,edges,labels):('a,'b) BDD) (vars_consumed) ∧
    BDD_WF (r,edges,labels) ∧
    BDD_WF (r',edges',labels') ∧ (* induce it initially *)
             
    mv_dom_bdd mv (r',edges',labels') ∧
    consumed_dom_bdd (vars_consumed) (r,edges,labels) ∧
                     
    correct_sem rec (r,edges,labels) ∧
    body_of_mk rec (r,edges,labels) h c = SOME ((r',edges',labels'),c') ∧
               
    BDD_sem rec (r',edges',labels') mv n b ∧
    ALOOKUP edges' n = SOME (n',n'') ∧
    ALOOKUP labels' n = SOME (non_termn (SOME x,p)) ⇒
    b = op_sem rec (SOME p) mv


  ntac 2 strip_tac >>
  measureInduct_on `THE(INDEX_OF x vars_consumed)` >>
  rpt strip_tac >>

   ‘MEM n (dom_range_edges edges')’ by imp_res_tac lookup_edges_in_domain >>

  (*imp_res_tac WFness_range_c_inter >>*)
  Cases_on ‘ALOOKUP edges n’ >> rgs[] >|[
    (* this needs the body *)
    cheat
    
    ,
    (* directly from IH *)
    PairCases_on ‘x'’ >>
    rename1 ‘ALOOKUP edges n = SOME (n1',n2')’ >>
    ‘(n'=n1') ∧ (n''=n2')’ by (imp_res_tac inner_edges_are_same >> srw_tac[][]) >>
            
    ‘lookup_is_some edges n’ by gvs[lookup_is_some_def] >>
    ‘∃x p. ALOOKUP labels n = SOME (non_termn (SOME x,p))’ by (imp_res_tac WF_imp_non_leaf_lbl_abs >> metis_tac[]) >>
    ‘(x=x') ∧ (p=p')’ by (imp_res_tac inner_labels_are_same >> srw_tac[][]) >>

              
    ‘MEM n1' (dom_range_edges edges)’ by imp_res_tac lookup_edges_in_domain >>
    ‘MEM n2' (dom_range_edges edges)’ by imp_res_tac lookup_edges_in_domain >>

    gvs[op_sem_def] >>




                    
                    
    rgs[Once BDD_sem_cases] >|[
        (*True*)
        Cases_on ‘ALOOKUP edges n'’ >> rgs[]>|[
          (* from body *)
          cheat
          ,
          PairCases_on ‘x'’ >>
          rename1 ‘ALOOKUP edges n' = SOME (n1',n2')’ >>
                  
          ‘lookup_is_some edges n'’ by gvs[lookup_is_some_def] >>
          ‘∃x p. ALOOKUP labels n' = SOME (non_termn (SOME x,p))’ by (imp_res_tac WF_imp_non_leaf_lbl_abs >> metis_tac[]) >>
          
          ‘MEM x' vars_consumed ∧ MEM x vars_consumed’ by (rgs[Once consumed_dom_bdd_def] >> res_tac >> fs[]) >>
          ‘∃i. INDEX_OF x vars_consumed = SOME i’ by (imp_res_tac MEM_INDEX_OF >> gvs[] )>>
          ‘∃i'. INDEX_OF x' vars_consumed = SOME i'’ by (imp_res_tac MEM_INDEX_OF >> gvs[]) >>


          subgoal ‘THE (INDEX_OF x' vars_consumed) < THE (INDEX_OF x vars_consumed)’ >-
           (
           rgs[Once BDD_ordered_def]>>
           first_x_assum (strip_assume_tac o (Q.SPECL [‘n’,‘n'’, ‘n''’]))>>
           gvs[order_hold_def]
           ) >>
          
                
          first_x_assum (strip_assume_tac o (Q.SPECL [‘INDEX_OF (x':string) (vars_consumed: string list)’])) >>
          gvs[] >>
                
          first_x_assum (strip_assume_tac o (Q.SPECL [‘x'’, ‘vars_consumed’])) >>
          gvs[] >>

          first_x_assum (strip_assume_tac o (Q.SPECL [‘r’, ‘edges’, ‘labels’, ‘r'’, ‘edges'’, ‘labels'’])) >>
          gvs[] >>

          first_x_assum (strip_assume_tac o (Q.SPECL [‘mv’, ‘n'’,‘n1'’, ‘n2'’, ‘h’, ‘c’, ‘c'’])) >>
          gvs[] >>

          first_x_assum (strip_assume_tac o (Q.SPECL [‘p'’, ‘b’, ‘rec’])) >>
          gvs[] >>

                
          ‘ALOOKUP edges' n' = SOME (n1',n2')’ by (imp_res_tac inner_edges_are_same_exists >> gvs[]) >>
          ‘ALOOKUP labels' n' = SOME (non_termn (SOME x',p'))’ by (imp_res_tac inner_labels_are_same_exists >> gvs[]) >>
          ‘MEM n' (dom_range_edges edges')’ by imp_res_tac lookup_edges_in_domain >>
          rgs[] >>


          ‘BDD_sem rec (r',edges',labels') mv n b’ by cheat >>

          ‘BDD_sem rec (r',edges',labels') mv n' (rec.sem p mv)’ by cheat >>
          rgs[] >>
          
          imp_res_tac BDD_sem_determ >>
          rgs[Once BDD_sem_cases]
                                                                                
                
          
        ]
        ,
        (* False *)

      ]


  ]


               







        

Theorem correct_sem_translation_inter:
  ∀ (BDD:('a,'b) BDD) BDD'' rec c c' vars h vars_consumed  .
  BDD_ordered BDD'' (h::vars_consumed) ∧      
  BDD_WF BDD'' ∧
  consumed_dom_bdd (h::vars_consumed) BDD'' ∧
  correct_sem rec BDD ∧
  body_of_mk rec BDD h c = SOME (BDD'',c') ⇒
  correct_sem rec BDD'' 
Proof

  rpt strip_tac >>
  
  PairCases_on ‘BDD’ >>
  rename1 ‘(r,edges,labels)’ >>
  
  PairCases_on ‘BDD''’ >>
  rename1 ‘(r',edges',labels')’ >>

  simp [correct_sem_def] >>
  rpt strip_tac >>

  Cases_on ‘ALOOKUP edges' n’ >|[
    rgs[op_sem_def] >>
    rgs[get_prop_def] >>
    rpt (BasicProvers.full_case_tac >> gvs[]) >>
        
    rgs[Once BDD_sem_cases] >>
    rgs[from_formula_to_action_def] >>
    Cases_on ‘b’ >> gvs[] >>
  
    cheat
    ,

    Cases_on ‘x’ >>
    rename1 ‘ALOOKUP edges' n = SOME (n',n'')’ >>

    (* from WFness we know that n's label is x,p*)
    ‘MEM n (dom_range_edges edges')’ by imp_res_tac lookup_edges_in_domain >>
    ‘lookup_is_some edges' n’ by gvs[lookup_is_some_def] >>
    ‘is_lookup_internal labels' n’ by (rgs[BDD_WF_def] >>res_tac) >>

    rgs[is_lookup_internal_def] >>
    rgs[get_prop_def] >>

    (*************)
                      
    rgs[Once BDD_sem_cases] >>

    rgs[op_sem_def]
    Cases_on ‘b’ >> rgs[] >>
    rgs[Once BDD_sem_cases] >>


    rgs[Once BDD_sem_cases] >>
    rgs[from_formula_to_action_def] >>
        rpt (BasicProvers.full_case_tac >> gvs[]) >>

             

  ]

QED




        
    

Theorem correct_sem_translation:
  ∀ vars vars_consumed BDD BDD' rec c   .
    BDD_ordered BDD vars_consumed ∧
    BDD_WF BDD ∧
    range_c c BDD ∧
    consumed_dom_bdd vars_consumed BDD ∧
    ALL_DISTINCT ((REVERSE vars)++vars_consumed) ∧
    correct_sem rec BDD ∧
    SOME BDD' = mk_BDDPred rec BDD vars_consumed vars c ⇒
    correct_sem rec BDD' 
Proof
  Induct >| [
    rpt strip_tac >>
    gvs[mk_BDDPred_def]
    ,
    rpt strip_tac >>
    
    gvs[mk_BDDPred_def] >>
    gvs[AllCaseEqs()] >>

    rpt strip_tac >>
    
    PairCases_on ‘BDD’ >>
    rename1 ‘(r,edges,labels)’ >>
    
    PairCases_on ‘BDD'’ >>
    rename1 ‘(r',edges',labels')’ >>

    PairCases_on ‘BDD''’ >>
    rename1‘((r'',edges'',labels''),c')’ >>

                 
    ‘range_c c' (r'',edges'',labels'')’ by imp_res_tac WFness_range_c_inter >>

    ‘BDD_WF (r'',edges'',labels'')’ by imp_res_tac WFness_translation_inter >> gvs[]>>

    ‘ALL_DISTINCT (h::vars_consumed)’ by cheat >>        
    ‘BDD_ordered (r'',edges'',labels'') (h::vars_consumed)’ by imp_res_tac order_translation_inter >>

    ‘ALL_DISTINCT (h::vars_consumed)’ by cheat >>        
    ‘consumed_dom_bdd (h::vars_consumed) (r'',edges'',labels'')’ by imp_res_tac consumed_dom_bdd_inter >>


    assume_tac correct_sem_translation_inter >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘(r,edges,labels)’, ‘(r'',edges'',labels'')’, ‘rec’, ‘c’, ‘c'’, ‘vars’, ‘h’, ‘vars_consumed’])) >>
    ‘BDD_ordered (r,edges,labels) (h::vars_consumed)’ by cheat >>
    gvs[]>>
                
    ‘correct_sem rec (r'',edges'',labels'')’ by cheat >>

    ‘ALL_DISTINCT (REVERSE vars ⧺ h::vars_consumed)’ by cheat >>

    metis_tac[]
  ]
QED
    

*)

val _ = export_theory ();
