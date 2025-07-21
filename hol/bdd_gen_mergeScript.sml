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

val _ = new_theory "bdd_gen_merge";


(*eliminable add that node 0 is not eliminatable *)

Theorem merge_lookup_none:
  ∀ edges n n' n''.
    n' ≠ n'' ⇒
    ((ALOOKUP edges n'' = NONE) ⇔ (ALOOKUP (merge_edges edges n n') n'' = NONE))
Proof
  Induct >-
   gvs[merge_edges_def] >>
  rpt strip_tac >>
  rw[merge_edges_def] >>
  
  PairCases_on ‘h’ >>
  gvs[] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  res_tac >>
  gvs[merge_edges_def]
QED



        

        
Theorem merge_lookup_exists:
  ∀ edges n n' n'' x.        
    n' ≠ n'' ∧
    ALOOKUP (merge_edges edges n n') n'' = SOME x ⇒
    ∃ x' . ALOOKUP edges n'' = SOME x'
Proof
  Induct >-
   gvs[merge_edges_def] >>
  rpt strip_tac >>
  rgs[Once merge_edges_def] >>
  PairCases_on ‘h’ >> gvs[] >>
  PairCases_on ‘x’ >>
  fs[AllCaseEqs()] >>
  gvs[merge_edges_def] >>
  res_tac >>                                
  gvs[]
QED


Theorem mergable_correct_leaf:
  ∀labels n'' r edges n' n mv b rec.
    BDD_WF (r,edges,labels) ∧
    n' ≠ n'' ∧
    ALOOKUP edges n'' = NONE ⇒
    BDD_sem rec (r,edges,labels) mv n'' b =
    BDD_sem rec (r,ADELKEY n' (merge_edges edges n n'),ADELKEY n' labels) mv n'' b
Proof
  rpt strip_tac >>
  simp[Once BDD_sem_cases]>> gvs[] >>
  rpt strip_tac >>
  
      
  subgoal ‘ALOOKUP (merge_edges edges n n') n'' = NONE’ >-
   (
   imp_res_tac merge_lookup_none >>
   last_x_assum (strip_assume_tac o (Q.SPECL [‘n’]))
   ) >>
    
  gvs[] >>
  
  simp[Once BDD_sem_cases] >>
  gvs[] >>
  gvs[ALOOKUP_ADELKEY]        
QED



Theorem merge_edges_same:
  ∀ edges n n.        
    merge_edges edges n n = edges
Proof
  Induct >>
  rpt strip_tac>>
  gvs[merge_edges_def]>>
  PairCases_on ‘h’ >> rgs[]>>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[])
QED


Theorem merge_edges_list_cons:        
  ∀ edges h n n'.
    merge_edges (h::edges) n n' = (merge_edges [h] n n')++(merge_edges (edges) n n')
Proof
  rpt strip_tac>>
  gvs[Once merge_edges_def] >>
  PairCases_on ‘h’ >> gvs[merge_edges_def]
QED


        
Theorem merge_edges_list_normalize:
  ∀ t t' h1 h2 h3 h1' h2' h3' n n'.
    (merge_edges ((h1,h2,h3)::t) n n' = (h1',h2',h3')::t') =
      (merge_edges [(h1,h2,h3)] n n' = [(h1',h2',h3')] ∧ merge_edges t n n' = t')
Proof
  Induct >>
  Induct_on ‘t'’ >>
  rpt strip_tac >>
  gvs[merge_edges_def]                          
QED
        

Theorem merge_edges_res_sing:
  ∀ n n' n'' nr nl h.
    n ≠ n' ∧
    n'' ≠ n' ⇒
    ALOOKUP (merge_edges [h] n n') n'' = SOME (nr,nl) ⇒
    (nr ≠ n' ∧ nl ≠ n')
Proof
  rpt strip_tac >>
  PairCases_on ‘h’ >> gvs[] >>
  rpt strip_tac>>
  gvs[merge_edges_def] >>       
  gvs[AllCaseEqs()]
QED


Theorem merge_edges_glue:        
  ∀ edges n n' n'' nr nl.
    n ≠ n' ∧
    n'' ≠ n' ∧
    ALOOKUP (merge_edges edges n n') n'' = SOME (nr,nl) ⇒
    (nr ≠ n' ∧ nl ≠ n')
Proof   
  Induct >>
  rpt strip_tac>-
   gvs[merge_edges_def] >-
   gvs[merge_edges_def] >> (
  fs[Once merge_edges_list_cons] >>
  fs[ALOOKUP_APPEND] >>
  fs[AllCaseEqs()]>|[
      res_tac >>
      metis_tac[]
      ,
      metis_tac[merge_edges_res_sing]
    ]
  )
QED        


           

Theorem merge_edges_res:        
  ∀ edges n n' n'' nr nl r labels.
    (mergable (r,edges,labels) n n' ∨ eliminable (r,edges,labels) n n') ∧
    n'' ≠ n' ∧
    ALOOKUP (merge_edges edges n n') n'' = SOME (nr,nl) ⇒
    (nr ≠ n' ∧ nl ≠ n')
Proof   
  rpt strip_tac >>
  gvs[mergable_def, eliminable_def] >>
  metis_tac[merge_edges_glue]
QED        


   


Theorem merge_Theorem1:
  (ALOOKUP (merge_edges [(h0,h1,h2)] n n') n'' = NONE ⇒
   h0 ≠ n'') ∧
  (ALOOKUP (merge_edges [(h0,h1,h2)] n n') n'' = SOME x ⇒
   h0 = n'')
Proof
  gvs[merge_edges_def]
QED

        
Triviality alookup_Theorem1:
  ALOOKUP ((h0,h1,h2)::edges) n'' = SOME (nr,nl) ∧
  h0 = n'' ⇒
  (nr = h1 ∧ nl = h2)
Proof
  rpt strip_tac >>
  fs[AllCaseEqs()]
QED
     




Theorem merge_parent_change:         
  ∀ edges n n' n'' nr nl nr' nl'.
    (nr ≠ nr' ∧
     ALOOKUP edges n'' = SOME (nr,nl) ∧
     ALOOKUP (merge_edges edges n n') n'' = SOME (nr',nl') ⇒
     (nr = n' ∧  nr' = n))
    ∧
    (nl ≠ nl' ∧
     ALOOKUP edges n'' = SOME (nr,nl) ∧
     ALOOKUP (merge_edges edges n n') n'' = SOME (nr',nl') ⇒
     (nl = n' ∧  nl' = n))
Proof        
  Induct >>                                                
  rpt strip_tac >-
   gvs[merge_edges_def] >-
   gvs[merge_edges_def] >-
   gvs[merge_edges_def] >-
   gvs[merge_edges_def] >>
  
  ‘ALOOKUP (merge_edges [h] n n' ⧺ merge_edges edges n n') n'' =
   SOME (nr',nl')   ’ by fs[Once merge_edges_list_cons] >>
  (
  Cases_on ‘ALOOKUP (merge_edges [h] n n') n''’ >|[
      
      ‘ALOOKUP (merge_edges edges n n') n'' = SOME (nr',nl')’ by
       (imp_res_tac alookup_defined_append1 >> metis_tac[]) >>
      
      PairCases_on ‘h’ >>
      
      imp_res_tac merge_Theorem1 >>
      
      qpat_x_assum ‘ALOOKUP (h::edges) n'' = SOME (nr,nl)’ (fn thm => assume_tac (SIMP_RULE (srw_ss()) [Once ALOOKUP_def] thm)) >>
      
      ‘ALOOKUP edges n'' = SOME (nr,nl)’ by  rgs[] >>
      metis_tac[]
      ,
      
      PairCases_on ‘h’ >>
      imp_res_tac merge_Theorem1 >>
      PairCases_on ‘x’ >>
      ‘x0 = nr'’ by (imp_res_tac alookup_defined_append2 >> metis_tac []) >>
      ‘x1 = nl'’ by (imp_res_tac alookup_defined_append2 >> metis_tac []) >>
      
      subgoal ‘ (nr = h1 ∧ nl = h2)’  >-           
       (imp_res_tac alookup_Theorem1 >>
        metis_tac[]
       ) >>
      
      
      metis_tac [lookup_merge_uni_bs]
    ]
  )
QED




Theorem  lookup_edges_not_parent:       
  ∀ r edges labels vars_consumed n nl nr.
    BDD_ordered (r,edges,labels) vars_consumed ∧
    BDD_WF (r,edges,labels) ∧
    consumed_dom_bdd vars_consumed (r,edges,labels) ∧
    ALOOKUP edges n = SOME (nr,nl) ⇒
    (nr ≠ n ∧ nl ≠ n) 
Proof
  rpt strip_tac >>
  ‘MEM n (dom_range_edges edges)’ by imp_res_tac lookup_edges_in_domain >>
  
  ‘∃ x p. ALOOKUP labels n = SOME (non_termn (SOME x,p))’ by
    (gvs[BDD_WF_def] >>
     gvs[lookup_is_some_def, is_lookup_internal_def] >>
     res_tac >> gvs[]) >|[
    
    gvs[BDD_ordered_def] >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘n’, ‘n’, ‘nl’])) >>
    gvs[order_hold_def] >>
    
    gvs[consumed_dom_bdd_def] >>
    res_tac >>
    imp_res_tac MEM_INDEX_OF >>
    
    first_x_assum (strip_assume_tac o (Q.SPECL [‘i’, ‘i’])) >>
    gvs[] 
    ,
    
    gvs[BDD_ordered_def] >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘n’, ‘nr’, ‘n’])) >>
    gvs[order_hold_def] >>
    
    gvs[consumed_dom_bdd_def] >>
    res_tac >>
    imp_res_tac MEM_INDEX_OF >>
    
    last_x_assum (strip_assume_tac o (Q.SPECL [‘i’, ‘i’])) >>
    gvs[]
  ]
QED


Theorem merge_replaces_stays_same_singular:
  n' ≠ x1'  ∧ n' ≠ x2' ∧      
  ALOOKUP (h::edges) n = SOME (x1',x2') ∧
  ALOOKUP (merge_edges [h] n n') n = SOME (x1,x2) ⇒
  (x1=x1' ∧ x2=x2')
Proof
  rpt strip_tac >>
  rgs[Once merge_edges_def] >>
  PairCases_on ‘h’ >>
  fs[AllCaseEqs()]
QED



(* very slow proof, check why, replace with MEM proofs*)       
Theorem merge_replaces_stays_same:            
  ∀ edges n' n x1 x2 x1' x2'.
    n' ≠ x1' ∧ n' ≠ x2' ∧
    ALOOKUP (merge_edges edges n n') n = SOME (x1,x2) ∧
    ALOOKUP edges n = SOME (x1',x2') ⇒
    (x1=x1' ∧ x2=x2')
Proof
  Induct >-
   gvs[merge_edges_def] >>
  rpt strip_tac >>
  
  (
  qpat_x_assum ‘ALOOKUP (merge_edges (h::edges) n n') n = SOME (x1,x2)’
               (fn thm => assume_tac (SIMP_RULE (srw_ss()) [Once merge_edges_list_cons] thm)) >>
  
  qpat_x_assum ‘ALOOKUP (merge_edges [h] n n' ⧺ merge_edges edges n n') n = SOME (x1,x2)’
               (fn thm => assume_tac (SIMP_RULE (srw_ss()) [Once ALOOKUP_APPEND] thm)) >>
  fs[AllCaseEqs()] >|[
      PairCases_on ‘h’ >>
      imp_res_tac merge_Theorem1 >>
      rgs[Once ALOOKUP_def] >>
      metis_tac[]
      ,
      metis_tac[merge_replaces_stays_same_singular]
    ]
  )                                                    
QED
       

    

                                               
Theorem mergable_correct_internal:
  ∀ x vars_consumed  vars r edges labels n n' n'' nl nr pred mv b rec.
    consumed_dom_bdd vars_consumed (r,edges,labels) ∧
    fv_in_BDD rec (r,edges,labels) (vars ⧺ vars_consumed)∧
    mv_dom_vars mv (vars ⧺ vars_consumed) ∧
    BDD_ordered (r,edges,labels) vars_consumed ∧
    BDD_WF (r,edges,labels) ∧
    mergable (r,edges,labels) n n' ∧
    n'' ≠ n' ∧
    ALOOKUP edges n'' = SOME (nr,nl) ∧
    ALOOKUP labels n'' = SOME (non_termn (SOME x,pred))
    ⇒
    (BDD_sem rec (r,edges,labels) mv n'' b ⇔
       BDD_sem rec (r,ADELKEY n' (merge_edges edges n n'),ADELKEY n' labels) mv n'' b)
Proof
        
  ntac 2 strip_tac >>
  measureInduct_on `THE(INDEX_OF x vars_consumed)` >>
  rpt strip_tac >>
  
  
  simp[Once BDD_sem_cases]>> gvs[] >>
  
  simp[Once EQ_SYM_EQ, Once BDD_sem_cases] >>
  gvs[ALOOKUP_ADELKEY] >>
  
  gvs[from_formula_to_action_def] >>
  Cases_on ‘ALOOKUP (merge_edges edges n n') n''’ >> gvs[]  >|[
    
    assume_tac merge_lookup_none >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘edges’,‘n’,‘n'’,‘n''’])) >>
    gvs[]
    ,
    
    PairCases_on ‘x'’ >> gvs[] >>
                 
    Cases_on ‘ALOOKUP mv x’ >> gvs[] >> Cases_on ‘x'’ >> gvs[] >|[
        
        (* true case *)
        (* is it a merged nodes i.e. (nr≠x'0) or not (nr=x'0) ... we started with non merged nodes *)   
        Cases_on ‘nr=x'0’ >> gvs[] >|[
          
          Cases_on ‘ALOOKUP edges nr’ >> gvs[] >|[

            ‘n'≠nr’ by metis_tac[merge_edges_res] >>
            metis_tac[mergable_correct_leaf]
            ,
            
            Cases_on ‘x'’ >> gvs[] >>
            ‘MEM nr (dom_range_edges edges)’ by imp_res_tac lookup_edges_in_domain >>
            ‘∃pred x'. ALOOKUP labels nr = SOME (non_termn (SOME x',pred))’ by
              (imp_res_tac WF_imp_non_leaf_lbl >> gvs[]) >>
            
            gvs[] >>
            subgoal ‘THE (INDEX_OF x' vars_consumed) < THE (INDEX_OF x vars_consumed)’ >-
             (imp_res_tac ordered_for_two_labels) >>
            
            
            first_x_assum (strip_assume_tac o (Q.SPECL [‘INDEX_OF (x':string) (vars_consumed: string list)’])) >>
            rgs[PULL_FORALL] >>  
            first_x_assum (strip_assume_tac o (Q.SPECL [‘x'’, ‘vars_consumed’, ‘vars’, ‘r’, ‘edges’, ‘labels’, ‘n’, ‘n'’,
                                                        ‘nr’, ‘r'’, ‘q’,  ‘pred'’, ‘mv’, ‘b’])) >>
            gvs[] >>
            
            ‘n'≠nr’ by metis_tac[merge_edges_res] >>
            gvs[]
          ]
          ,
          
          (* nr ≠ x'0 *)
          (* we are working with a parent of a node that it's children gotten merged *)   
          gvs[mergable_def] >>
          
          (* we know that the parent's children are not random,
             before merge should be n' and after merge should be n *)
          ‘x'0 = n ∧ nr = n' ’ by (imp_res_tac merge_parent_change >> metis_tac[]) >>
          rgs[] >>
          
          simp[Once BDD_sem_cases] >>  gvs[ALOOKUP_ADELKEY] >>
          Cases_on ‘ALOOKUP (merge_edges edges n n') n’ >> gvs[] >|[
                   
              ‘ALOOKUP edges n' = NONE’ by (metis_tac [merge_lookup_none]) >>
              simp[Once EQ_SYM_EQ, Once BDD_sem_cases] >>


              (*************************)
              rgs[eq_vars_in_labels_def] >>
              rpt (BasicProvers.FULL_CASE_TAC >> rgs[]) >>
              gvs[from_formula_to_action_def] >>

              (* now contradiction *)
              ‘MEM n' (dom_range_edges edges)’ by imp_res_tac lookup_edges_in_domain >>
              rgs[BDD_WF_def, is_lookup_ntl_def] >>
              first_x_assum (strip_assume_tac o (Q.SPECL [‘n'’])) >>
              gvs[]
                 
        
                                                                                        
              ,
                
              PairCases_on ‘x'’ >> gvs[] >>
              ‘∃x'. ALOOKUP edges n = SOME x'’ by  (imp_res_tac merge_lookup_exists >> gvs[]) >>
              PairCases_on ‘x'’ >> gvs[] >>    
              Cases_on ‘ALOOKUP labels n'’ >> gvs[] >>
              Cases_on ‘x'’ >> gvs[] >|[
                       
                  ‘∃pair. ALOOKUP edges n = SOME pair’ by metis_tac [merge_lookup_exists] >>
                  ‘∃ x'' p''. ALOOKUP labels n = SOME (non_termn (SOME x'',p'')) ’ by metis_tac[WF_imp_non_leaf_lbl] >>
                  gvs[] >>
                  rgs[eq_vars_in_labels_def]
                        
                  ,
                        
                  Cases_on ‘p’ >> gvs[] >>
                  Cases_on ‘q’ >> gvs[] >|[
                           
                      ‘∃pair. ALOOKUP edges n = SOME pair’ by metis_tac [merge_lookup_exists] >>
                      ‘∃ x'' p''. ALOOKUP labels n = SOME (non_termn (SOME x'',p'')) ’ by metis_tac[WF_imp_non_leaf_lbl] >>
                      gvs[] >>
                      rgs[eq_vars_in_labels_def]

                      ,

                      (* ($var$(x'0'),x'1'') = (nl_old,nr_old)
                         (x'0,$var$(x'1')) =  (n1,n2)   *)
                      rename1 ‘SOME (nl_old,nr_old) = ALOOKUP edges n'’ >>
                      rename1 ‘ALOOKUP (merge_edges edges n n') n = SOME (n1,n2)’ >>
                      subgoal ‘∃ bool . ALOOKUP mv x' = SOME bool’>-
                       (  imp_res_tac consumed_dom_bdd_in_mv >> gvs[] ) >>
                              
                          Cases_on ‘bool’ >> (
                              
                              (* true and false sub branches, same solution*)
                              ‘n' ≠ n'' ∧ nl ≠ n''’ by (imp_res_tac lookup_edges_not_parent >> gvs[]) >>
                                  
                              qpat_x_assum ‘SOME (nl_old,nr_old) = ALOOKUP edges n'’
                                           (fn thm => assume_tac (SIMP_RULE (srw_ss()) [Once EQ_SYM_EQ] thm)) >>
                              ‘n' ≠ nl_old∧ n' ≠ nr_old’ by (imp_res_tac lookup_edges_not_parent >> gvs[]) >>
                              
                              (* we need to show that n1 = nl_old *)    
                              ‘ALOOKUP edges n = SOME (nl_old,nr_old)’ by gvs[] >>    
                              ‘n ≠ nl_old ∧ n ≠ nr_old’ by (imp_res_tac lookup_edges_not_parent >> gvs[]) >>   
                              ‘n1 = nl_old’ by imp_res_tac merge_replaces_stays_same >>
                              rgs[] >>
                              simp[Once EQ_SYM_EQ, Once BDD_sem_cases] >>
                              
                              
                              subgoal ‘THE (INDEX_OF x' vars_consumed) < THE (INDEX_OF x vars_consumed)’ >-
                               (imp_res_tac ordered_for_two_labels) >>
                               
                              (***********)
                              rgs[Once eq_vars_in_labels_def] >>
                              rpt (BasicProvers.FULL_CASE_TAC >> rgs[]) >>
                              (**********)
                                                        
                              first_x_assum (strip_assume_tac o (Q.SPECL [‘INDEX_OF (x':string) (vars_consumed: string list)’])) >>
                              gvs[PULL_FORALL] >>
                              first_x_assum (strip_assume_tac o (Q.SPECL [‘x'’, ‘vars_consumed’, ‘vars’, ‘r’, ‘edges’, ‘labels’, ‘n’,
                                                                          ‘n'’, ‘n’, ‘nr_old’, ‘n1’,  ‘r''’, ‘mv’, ‘b’, ‘rec’])) >>
                              rgs[] >>
                              
                              gvs[Once BDD_sem_cases] >>
                              simp[Once BDD_sem_cases] >>
                              gvs[ALOOKUP_ADELKEY] >>

                              (***********)
                              rgs[Once eq_vars_in_labels_def] >>
                              rpt (BasicProvers.FULL_CASE_TAC >> rgs[]) >>
                              gvs[Once BDD_sem_cases] >>
                              simp[Once BDD_sem_cases] >>
                              gvs[ALOOKUP_ADELKEY]
                              (**********)
                            )
                    ] 
                ]
            ]                                                      
        ]
        ,

        (* false case: removed comments, similar proof *)
         Cases_on ‘nl=x'1’ >> gvs[] >|[
          
          Cases_on ‘ALOOKUP edges nl’ >> gvs[] >|[

            ‘n'≠nl’ by metis_tac[merge_edges_res] >>
            metis_tac[mergable_correct_leaf]
            ,
            
            Cases_on ‘x'’ >> gvs[] >>
            ‘MEM nl (dom_range_edges edges)’ by imp_res_tac lookup_edges_in_domain >>
            ‘∃pred x'. ALOOKUP labels nl = SOME (non_termn (SOME x',pred))’ by
              (imp_res_tac WF_imp_non_leaf_lbl >> gvs[]) >>
            
            gvs[] >>
            subgoal ‘THE (INDEX_OF x' vars_consumed) < THE (INDEX_OF x vars_consumed)’ >-
             (imp_res_tac ordered_for_two_labels) >>
            
            
            first_x_assum (strip_assume_tac o (Q.SPECL [‘INDEX_OF (x':string) (vars_consumed: string list)’])) >>
            rgs[PULL_FORALL] >>  
            first_x_assum (strip_assume_tac o (Q.SPECL [‘x'’, ‘vars_consumed’, ‘vars’, ‘r’, ‘edges’, ‘labels’, ‘n’, ‘n'’,
                                                        ‘nl’, ‘r'’, ‘q’,  ‘pred'’, ‘mv’, ‘b’])) >>
            gvs[] >>
            
            ‘n'≠nl’ by metis_tac[merge_edges_res] >>
            gvs[]
          ]
          ,
          
          (* we are working with a parent of a node that it's children gotten merged *)   
          gvs[mergable_def] >>
          
          (* we know that the parent's children are not random,
             before merge should be n' and after merge should be n *)
          ‘x'1 = n ∧ nl = n' ’ by (imp_res_tac merge_parent_change >> metis_tac[]) >>
          rgs[] >>
          
          simp[Once BDD_sem_cases] >>  gvs[ALOOKUP_ADELKEY] >>
          Cases_on ‘ALOOKUP (merge_edges edges n n') n’ >> gvs[] >|[
                   
                ‘ALOOKUP edges n' = NONE’ by (metis_tac [merge_lookup_none]) >>
              simp[Once EQ_SYM_EQ, Once BDD_sem_cases] >>


              (*************************)
              rgs[eq_vars_in_labels_def] >>
              rpt (BasicProvers.FULL_CASE_TAC >> rgs[]) >>
              gvs[from_formula_to_action_def] >>

              (* now contradiction *)
              ‘MEM n' (dom_range_edges edges)’ by imp_res_tac lookup_edges_in_domain >>
              rgs[BDD_WF_def, is_lookup_ntl_def] >>
              first_x_assum (strip_assume_tac o (Q.SPECL [‘n'’])) >>
                gvs[]
                        
              ,
                
              PairCases_on ‘x'’ >> gvs[] >>
              ‘∃x'. ALOOKUP edges n = SOME x'’ by  (imp_res_tac merge_lookup_exists >> gvs[]) >>
              PairCases_on ‘x'’ >> gvs[] >>    
              Cases_on ‘ALOOKUP labels n'’ >> gvs[] >>
              Cases_on ‘x'’ >> gvs[] >|[
                       
                  ‘∃pair. ALOOKUP edges n = SOME pair’ by metis_tac [merge_lookup_exists] >>
                  ‘∃ x'' p''. ALOOKUP labels n = SOME (non_termn (SOME x'',p'')) ’ by metis_tac[WF_imp_non_leaf_lbl] >>
                  gvs[] >>
                  rgs[eq_vars_in_labels_def]
                  ,
                        
                  Cases_on ‘p’ >> gvs[] >>
                  Cases_on ‘q’ >> gvs[] >|[
                           
                      ‘∃pair. ALOOKUP edges n = SOME pair’ by metis_tac [merge_lookup_exists] >>
                      ‘∃ x'' p''. ALOOKUP labels n = SOME (non_termn (SOME x'',p'')) ’ by metis_tac[WF_imp_non_leaf_lbl] >>
                      gvs[] >>
                      rgs[eq_vars_in_labels_def]       
                      ,

                      rename1 ‘SOME (nl_old,nr_old) = ALOOKUP edges n'’ >>
                      rename1 ‘ALOOKUP (merge_edges edges n n') n = SOME (n1,n2)’ >>
                      subgoal ‘∃ bool . ALOOKUP mv x' = SOME bool’>-
                              (imp_res_tac consumed_dom_bdd_in_mv >> gvs[]) >>
                              
                          Cases_on ‘bool’ >> (
                              
                              (* true and false sub branches, same solution*)
                              ‘n' ≠ n'' ∧ nr ≠ n''’ by (imp_res_tac lookup_edges_not_parent >> gvs[]) >>
                                  
                              qpat_x_assum ‘SOME (nl_old,nr_old) = ALOOKUP edges n'’
                                           (fn thm => assume_tac (SIMP_RULE (srw_ss()) [Once EQ_SYM_EQ] thm)) >>
                              ‘n' ≠ nl_old∧ n' ≠ nr_old’ by (imp_res_tac lookup_edges_not_parent >> gvs[]) >>
                              
                              (* we need to show that n1 = nl_old *)    
                              ‘ALOOKUP edges n = SOME (nl_old,nr_old)’ by gvs[] >>    
                              ‘n ≠ nl_old ∧ n ≠ nr_old’ by (imp_res_tac lookup_edges_not_parent >> gvs[]) >>   
                              ‘n1 = nl_old’ by imp_res_tac merge_replaces_stays_same >>
                              rgs[] >>
                              simp[Once EQ_SYM_EQ, Once BDD_sem_cases] >>
                              
                              
                              subgoal ‘THE (INDEX_OF x' vars_consumed) < THE (INDEX_OF x vars_consumed)’ >-
                               (imp_res_tac ordered_for_two_labels) >>

                              (***********)
                              rgs[Once eq_vars_in_labels_def] >>
                              rpt (BasicProvers.FULL_CASE_TAC >> rgs[]) >>
                              (**********)
                             
                              first_x_assum (strip_assume_tac o (Q.SPECL [‘INDEX_OF (x':string) (vars_consumed: string list)’])) >>
                              gvs[PULL_FORALL] >>
                              first_x_assum (strip_assume_tac o (Q.SPECL [‘x'’, ‘vars_consumed’, ‘vars’, ‘r’, ‘edges’, ‘labels’, ‘n’,
                                                                          ‘n'’, ‘n’, ‘nr_old’, ‘n1’,  ‘r''’, ‘mv’, ‘b’])) >>
                              rgs[] >>
                              
                              gvs[Once BDD_sem_cases] >>
                              simp[Once BDD_sem_cases] >>
                              gvs[ALOOKUP_ADELKEY] >>
                              
                              (***********)
                              rgs[Once eq_vars_in_labels_def] >>
                              rpt (BasicProvers.FULL_CASE_TAC >> rgs[]) >>
                              gvs[Once BDD_sem_cases] >>
                              simp[Once BDD_sem_cases] >>
                              gvs[ALOOKUP_ADELKEY]
                                 (**********)
                                        
                            )
                    ] 
                ]
            ]                                                      
        ]
        
      ]
  ]
QED


 





             
           
Theorem Lemma3:
  ∀ labels vars vars_consumed n'' r edges n' n mv b rec.
    consumed_dom_bdd vars_consumed (r,edges,labels) ∧
    fv_in_BDD rec (r,edges,labels) (vars++vars_consumed) ∧
    mv_dom_vars mv (vars ⧺ vars_consumed) ∧
    BDD_ordered (r,edges,labels) vars_consumed ∧
    BDD_WF (r,edges,labels) ∧
    mergable (r,edges,labels) n n' ∧
    n'' ≠ n'
    ⇒
    BDD_sem rec (r,edges,labels) mv n'' b =
    BDD_sem rec (r,ADELKEY n' (merge_edges edges n n'), ADELKEY n' labels) mv n'' b 
Proof

  rpt strip_tac >>
      
  Cases_on ‘ALOOKUP edges n''’ >> gvs[] >|[
    assume_tac  mergable_correct_leaf >> 
    last_x_assum (strip_assume_tac o (Q.SPECL [‘labels’,‘n''’,‘r’, ‘edges’, ‘n'’, ‘n’, ‘mv’, ‘b’])) >>
    gvs[]
    ,
    PairCases_on ‘x’ >>

    subgoal ‘∃pred x'. ALOOKUP labels n'' = SOME (non_termn (SOME x',pred))’ >-
     (
     
     ‘MEM n'' (dom_range_edges edges)’ by imp_res_tac lookup_edges_in_domain >>
     imp_res_tac WF_imp_non_leaf_lbl >> gvs[]
     ) >>
    
    metis_tac[mergable_correct_internal]
  ]

QED




        

Theorem get_prop_delkey_none:        
  ∀ labels n'.
    get_prop (ADELKEY n' labels) n' = NONE
Proof
  Induct >>
  gvs[get_prop_def] >>
  rpt strip_tac >>
  gvs[ALOOKUP_ADELKEY] 
QED                        





        
Theorem merge_correct_verbose:        
  ∀ r edges labels vars vars_consumed n n' rec.
    correct_sem rec (r,edges,labels) (vars++vars_consumed)  ∧
    BDD_WF (r,edges,labels) ∧
    consumed_dom_bdd vars_consumed (r,edges,labels) ∧
    BDD_ordered (r,edges,labels) vars_consumed ∧
    fv_in_BDD rec (r,edges,labels) (vars++vars_consumed)  ∧
    mergable (r,edges,labels) n n'
    ==>
    correct_sem rec (merge (r,edges,labels) n n') (vars++vars_consumed)
Proof
  rpt strip_tac >>   
  simp[Once correct_sem_def] >>
  rpt strip_tac >>
  gvs[merge_def] >>

  Cases_on ‘n' = n''’ >> gvs[] >|[

    
    ‘get_prop (ADELKEY n' labels) n' = NONE’ by gvs[get_prop_delkey_none] >> 
    gvs[op_sem_def, get_prop_def] >>
    gvs[AllCaseEqs()]>>

    gvs[Once BDD_sem_cases]
    ,
    
    assume_tac Lemma3 >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘labels’, ‘vars’, ‘vars_consumed’, ‘n''’, ‘r’, ‘edges’, ‘n'’, ‘n’, ‘mv’, ‘b’, ‘rec’])) >>
    gvs[] >>


    gvs[correct_sem_def] >>
    res_tac >>
    
    gvs[get_prop_def]>> 
    gvs[Once BDD_sem_cases]>>
    
    gvs[ALOOKUP_ADELKEY] >>
    rgs[op_sem_def] >>
    gvs[AllCaseEqs()]
  ]
QED
 



        
Theorem merge_correct:        
  ∀ BDD vars vars_consumed n n' rec.
    correct_sem rec BDD (vars++vars_consumed)  ∧
    BDD_WF BDD ∧
    consumed_dom_bdd vars_consumed BDD ∧
    BDD_ordered BDD vars_consumed ∧
    fv_in_BDD rec BDD (vars++vars_consumed)  ∧
    mergable BDD n n'
    ==>
    correct_sem rec (merge BDD n n') (vars++vars_consumed)
Proof
  rpt strip_tac >>
  PairCases_on ‘BDD’ >>
  irule merge_correct_verbose >>
  gvs[]
QED








Theorem map_fst_merge_edges:
  ∀ edges n n'.
    MAP FST edges = MAP FST (merge_edges edges n n')
Proof
  Induct >-
   gvs[merge_edges_def] >>
  rpt strip_tac >>
  gvs[Once merge_edges_list_cons] >>
  PairCases_on ‘h’ >>
  gvs[merge_edges_def]
QED





Theorem merge_edges_snd_mem1:
  ∀l l' n n'.
    n≠n' ∧
    merge_edges l n n' = l' ⇒
    (¬MEM (n',n') (MAP SND l'))
Proof
  Induct >>                                               
  rw[merge_edges_def] >>
  gvs[] >>
  PairCases_on ‘h’ >> gvs[] >>
  
  gvs[MEM_MAP, ADELKEY_def, MEM_FILTER] >>
  rpt(BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  rpt strip_tac >>
  
  PairCases_on ‘y’ >>
  PairCases_on ‘y'’ >>
  gvs[] >>
  rpt(BasicProvers.FULL_CASE_TAC >> gvs[])
QED


Theorem merge_edges_snd_mem2:
  ∀l l' n n'.
    n≠n' ∧
    merge_edges l n n' = l' ⇒
    (¬MEM n' (MAP (\(a,c,b). b) l') ∧ ¬MEM n' (MAP (\(a,c,b). c) l'))
Proof
  Induct >>                                               
  rw[merge_edges_def] >>
  gvs[] >>
  PairCases_on ‘h’ >> gvs[] >>
  
  gvs[MEM_MAP, ADELKEY_def, MEM_FILTER] >>
  rpt(BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  rpt strip_tac >>
  
  PairCases_on ‘y’ >>
  PairCases_on ‘y'’ >>
  gvs[] >>
  rpt(BasicProvers.FULL_CASE_TAC >> gvs[])
QED

        

Theorem all_distinct_fst_merge_edges:
  ∀ r edges labels n n'.
    ALL_DISTINCT (MAP FST edges) =
    ALL_DISTINCT (MAP FST (merge_edges edges n n'))
Proof
metis_tac[map_fst_merge_edges]
QED


Theorem ALL_DISTINCT_MAP_ADELKEY:
  ∀ l n.
    ALL_DISTINCT (MAP FST l) ⇒
    ALL_DISTINCT (MAP FST (ADELKEY n l))
Proof
  Induct >>
  gvs[ADELKEY_def] >>
  rpt strip_tac >>
  rpt (BasicProvers.FULL_CASE_TAC >> rgs[]) >>
  PairCases_on ‘h’ >>
  gvs[ADELKEY_def, MEM_MAP] >>
  rpt strip_tac >>
  PairCases_on ‘y’ >>
  gvs[ADELKEY_def] >>
  gvs[MEM_FILTER]
QED      


Theorem edges_distinct_in_del_key:
  ∀ r edges labels n n' n''.
    ALL_DISTINCT (MAP FST edges) ⇒
    ALL_DISTINCT (MAP FST (ADELKEY n (merge_edges edges n' n'')))
Proof
  rpt strip_tac >>
  imp_res_tac all_distinct_fst_merge_edges >>
  first_x_assum (strip_assume_tac o (Q.SPECL [‘n''’, ‘n'’])) >>
  imp_res_tac ALL_DISTINCT_MAP_ADELKEY >>
  last_x_assum (strip_assume_tac o (Q.SPECL [‘n’]))
QED




Theorem merge_no_effect_on_unrelated_node_mem:
∀ r edges labels n n' .
  n ≠ n' ⇒
~ MEM n' (dom_range_edges (ADELKEY n' (merge_edges edges n n')))
Proof
  Induct_on ‘edges’ >>
  gvs[merge_edges_def, dom_range_edges_def, ADELKEY_def] >>
  rpt strip_tac >>
  rpt (BasicProvers.FULL_CASE_TAC >> rgs[]) >>
  PairCases_on ‘h’ >>
  
  gvs[MEM_MAP, ADELKEY_def, MEM_FILTER] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) 
QED



Theorem  distinct_mem_edges_triv:
  ∀ edges n n' n'' a b.
    ALL_DISTINCT (MAP FST edges) ∧
    MEM (n,n',n'') edges ∧
    MEM (n,a,b) edges ⇒
    (a=n' ∧ b=n'')
Proof
  Induct >>
  rpt strip_tac >>
  gvs[] >>
  res_tac >>
  gvs[MEM_MAP]
QED


        

Theorem distinct_mem_not_triv:
  ∀ edges n n' n''.
    ALL_DISTINCT (MAP FST edges) ∧
    MEM (n,n',n'') edges ⇒
    (~ ∃ a b . a≠n' ∧ b ≠ n'' ∧ MEM (n,a,b) edges)
Proof
  Induct >>
  rpt strip_tac >>
  gvs[] >>
  res_tac >>
  gvs[MEM_MAP] >>
  PairCases_on ‘h’ >> gvs[] >>
  metis_tac[distinct_mem_edges_triv]
QED

      



     
      
Theorem mem_edge_merge_then_unrelated_source:         
  ∀ edges n n' n'' y0 y1 y2.
    (MEM (n'',y1,y2) (merge_edges edges n n') ⇒
     ∃ v1 v2 . MEM (n'',v1,v2) edges) 
     
Proof
  
  rpt strip_tac >>
  gvs[merge_edges_def] >> gvs[] >>

  rpt(BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  gvs[MEM_MAP, ADELKEY_def, MEM_FILTER] >>
  
  PairCases_on ‘y’ >>
  gvs[] >>
  
  rpt(BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  gvs[MEM_MAP, ADELKEY_def, MEM_FILTER] >>
  
  srw_tac [SatisfySimps.SATISFY_ss][]
QED






Theorem merge_edges_mem_possibilites:
∀edges n n' k v1 v2.
  MEM (k,v1,v2) (merge_edges edges n n') ⇒
  ∃k' v1' v2'. MEM (k',v1',v2') edges ∧
               (k = k' ∨ k = n) ∧
               (v1 = v1' ∨ v1 = n ∨ v1 = v2') ∧
               (v2 = v2' ∨ v2 = n ∨ v2 = v1')
Proof

  rpt strip_tac >>
  gvs[merge_edges_def] >> gvs[] >>
  
  rpt(BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  gvs[MEM_MAP, ADELKEY_def, MEM_FILTER] >>
  
  PairCases_on ‘y’ >>
  gvs[] >>
  
  rpt(BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  gvs[MEM_MAP, ADELKEY_def, MEM_FILTER] >>
  
  srw_tac [SatisfySimps.SATISFY_ss][] >|[
    qexistsl_tac [‘k’, ‘n'’, ‘n'’] >> gvs[] ,
    qexistsl_tac [‘k’, ‘v1’, ‘n'’] >> gvs[] ,
    qexistsl_tac [‘k’, ‘n'’, ‘v2’] >> gvs[] ,
    qexistsl_tac [‘k’, ‘v1’, ‘v2’] >> gvs[]
  ]
QED







         
     
 






        
Definition dom_range_edges_alt_def:
  dom_range_edges_alt edges = 
    {n | ∃k v1 v2. MEM (k,v1,v2) edges ∧ (n = k ∨ n = v1 ∨ n = v2)}
End

Theorem dom_range_edges_equiv_alt:
  ∀edges. set (dom_range_edges edges) = dom_range_edges_alt edges
Proof
  rw[dom_range_edges_def, dom_range_edges_alt_def, EXTENSION] >>
  eq_tac >|[
    rw[] >>
    fs[MEM_nub, MEM_FLAT, MEM_MAP] >>
    PairCases_on ‘y’ >> rename1 ‘MEM (a,b,c) edges’ >> gvs[] >>
    qexistsl_tac [‘a’, ‘b’, ‘c’] >> 
     gvs[]
    ,
    rw[MEM_nub, MEM_FLAT, MEM_MAP] >>
    qexists_tac ‘[k; v1; v2]’ >> fs[] >>
    qexists_tac ‘(k,v1,v2)’ >> fs[]
  ]
QED



        
        
Theorem merge_adelkey_dom_range_subset_alt:
∀ edges n n' n''.
  n'' ≠ n' ∧ n ≠ n' ∧  n'' ≠ n ∧
  ALL_DISTINCT (MAP FST edges) ∧
  n'' ∈ dom_range_edges_alt (ADELKEY n' (merge_edges edges n n')) ⇒
  n'' ∈ dom_range_edges_alt edges
Proof
  rw[dom_range_edges_alt_def] >>
  fs[ADELKEY_def, MEM_FILTER, merge_edges_def, MEM_MAP] >>
  Cases_on `y` >> Cases_on `r` >> fs[] >>
  rename1 `MEM (a,b,c) edges` >>
  
  qexists_tac `a` >> qexists_tac `b` >> qexists_tac `c` >> fs[] >>
  
  (* Case analysis on merge transformation *)
  Cases_on `b = n' ∧ c = n'` >> fs[] >>
  Cases_on `b = n'` >> fs[] >>  
  Cases_on `c = n'` >> fs[] >> gvs[]                                 
QED



Definition dom_range_edges2_def:
  dom_range_edges2 edges =
    nub (MAP (λ(k,v1,v2). k) edges ++ MAP (λ(k,v1,v2). v1) edges ++ MAP (λ(k,v1,v2). v2) edges)
End


Theorem dom_range_edges1_2_eq:
  ∀ edges a.
    MEM a (dom_range_edges2 edges) = MEM a (dom_range_edges edges)
Proof
  
  Induct >> rpt strip_tac >>
  gvs[dom_range_edges_def, dom_range_edges2_def] >>
  PairCases_on ‘h’ >>
  Cases_on ‘a = h0’ >> gvs[] >>
  Cases_on ‘a = h1’ >> gvs[] >>
  Cases_on ‘a = h2’ >> gvs[] 
QED


        
Definition flat_edges_def:
  (flat_edges [] = []) /\
  (flat_edges ((k,v1,v2)::es) = 
   k :: v1 :: v2 :: flat_edges es)
End

Definition dom_range_edges3_def:
  dom_range_edges3 edges = nub (flat_edges edges)
End


Theorem dom_range_edges1_3_eq:
  ∀ edges n.
    MEM n (dom_range_edges3 edges) = MEM n (dom_range_edges edges)     
Proof
  Induct >>
  rpt strip_tac >>
  gvs[dom_range_edges3_def, dom_range_edges_def, flat_edges_def] >>
  PairCases_on ‘h’ >>
  gvs[dom_range_edges3_def, dom_range_edges_def, flat_edges_def] >>
  gvs[nub_def] >>
  Cases_on ‘n = h0 ∨ n = h1 ∨ n = h2’ >> gvs[]
QED


Theorem flat_edges_not_triv1:
  ∀ l n n'.
    n' ≠ n ∧
    ¬MEM n (flat_edges l) ⇒
    ¬MEM n (flat_edges (FILTER (λp. FST p ≠ n') l))
Proof
  Induct >> gvs[flat_edges_def, FILTER, MEM] >>
  rpt strip_tac >>
  PairCases_on ‘h’ >> 
  Cases_on ‘h0 ≠ n'’ >>
  gvs[flat_edges_def] >>
  metis_tac [] 
QED




Theorem mem_input_then_in_flattened:
  ∀ l n a b.
    MEM (n,a,b) l ⇒
    (MEM n (flat_edges l) ∧
     MEM a (flat_edges l) ∧
     MEM b (flat_edges l)
    )
Proof
  Induct >>
  rpt strip_tac >>
  gvs[flat_edges_def] >>
  PairCases_on ‘h’ >>
  gvs[flat_edges_def] >>
  res_tac >>
  gvs[]
QED



Theorem flat_edges_mem_triv1:
  ∀ l h0 h1 a b .
    MEM (h1,a,b) l ∧
    h1 ≠ h0  ⇒
    MEM a (flat_edges (FILTER (λp. FST p ≠ h0) l))
Proof
  Induct >-
   gvs[flat_edges_def] >>
  rpt strip_tac >>
  PairCases_on ‘h’ >>
  gvs[] >>
  gvs[flat_edges_def] >>
  Cases_on ‘h0'=h0’ >> gvs[] >|[
    res_tac
    ,
    gvs[flat_edges_def] >>
    metis_tac[]
  ]
QED




Theorem flat_edges_mem_triv2:
  ∀ l h0 h1 a b .
    ¬MEM h0 (MAP FST l) ∧
    MEM (h1,a,b) l ⇒
    (MEM a (flat_edges (FILTER (λp. FST p ≠ h0) l)) ∧
     MEM b (flat_edges (FILTER (λp. FST p ≠ h0) l)) ∧
     MEM h1 (flat_edges (FILTER (λp. FST p ≠ h0) l))
    )
Proof
  Induct >-
   gvs[flat_edges_def] >>
  rpt strip_tac >>
  PairCases_on ‘h’ >>
  gvs[flat_edges_def] >>
  Cases_on ‘h0'=h0’ >> 
  res_tac >> gvs[]
QED





Theorem flat_edges_mem_triv3:
  ∀ l h0 h1 a b .
    MEM (h1,a,b) l ∧
    h1 ≠ h0 ⇒
    MEM b (flat_edges (FILTER (λp. FST p ≠ h0) l))
Proof
  Induct >-
   gvs[flat_edges_def] >>
  rpt strip_tac >>
  PairCases_on ‘h’ >>
  gvs[] >>
  gvs[flat_edges_def] >>
  Cases_on ‘h0'=h0’ >> gvs[] >|[
    res_tac
    ,
    gvs[flat_edges_def] >>
    metis_tac[]
  ]
QED
        



     
Theorem flat_edges_mem_triv4:
  ∀ l k v1 v2 h0.
    MEM (k,v1,v2) l ∧
    (k ≠ h0) ⇒
    MEM k (flat_edges (FILTER (λp. FST p ≠ h0) l))
Proof
  Induct >-
   gvs[flat_edges_def] >>
  rpt strip_tac >>
  PairCases_on ‘h’ >>
  gvs[] >>
  gvs[flat_edges_def] >>
  Cases_on ‘h0'=h0’ >> gvs[] >|[
    res_tac
    ,
    gvs[flat_edges_def] >>
    metis_tac[]
  ]
QED



Theorem flat_edges_mem_triv5:
  ∀ l a n n' parent right.
    parent ≠ a ∧
    MEM (a,n,n') l ∧
    MEM (parent,n,right) l ⇒
    MEM n (flat_edges (FILTER (λp. FST p ≠ a) l))
Proof
  Induct >-
   gvs[flat_edges_def] >>
  rpt strip_tac >>
  PairCases_on ‘h’ >>
  gvs[] >>
  gvs[flat_edges_def] >|[
    imp_res_tac mem_input_then_in_flattened >>
    irule flat_edges_mem_triv1 >>
    srw_tac [SatisfySimps.SATISFY_ss][]
    ,
  Cases_on ‘h0=a’ >> gvs[] >|[
    res_tac
    ,
    gvs[flat_edges_def] >>
    metis_tac[]
      ]
  ]
QED


Theorem flat_edges_mem_triv6:
  ∀ l a n n' parent left.
    parent ≠ a ∧
    MEM (a,n,n') l ∧
    MEM (parent,left,n) l ⇒
    MEM n (flat_edges (FILTER (λp. FST p ≠ a) l))
Proof
  Induct >-
   gvs[flat_edges_def] >>
  rpt strip_tac >>
  PairCases_on ‘h’ >>
  gvs[] >>
  gvs[flat_edges_def] >|[
    imp_res_tac mem_input_then_in_flattened >>
    irule flat_edges_mem_triv3 >>
    srw_tac [SatisfySimps.SATISFY_ss][]
    ,
  Cases_on ‘h0=a’ >> gvs[] >|[
    res_tac
    ,
    gvs[flat_edges_def] >>
    metis_tac[]
      ]
  ]
QED



(* GOLDEN ONE *)
Theorem list_not_merged_flat_membership1:
  ∀ l n'' h0.
    ¬MEM h0 (MAP FST l) ∧
    n'' ≠ h0 ∧
    MEM n'' (flat_edges l) ⇒
    MEM n'' (flat_edges (FILTER (λp. FST p ≠ h0) l))
Proof
  Induct >>
  gvs[] >>
  rpt strip_tac >>
  PairCases_on ‘h’ >>
  gvs[] >>
  gvs[flat_edges_def] >>
  metis_tac[]
QED
         


Theorem list_not_merged_flat_membership2:
  ∀ l n' n'' a b.
    ALL_DISTINCT (MAP FST l) ∧
    MEM (n',a,b) l ∧ 
    (n'' ≠ a ∧ n'' ≠ b ∧ n'' ≠ n')  ⇒
    MEM n'' (flat_edges l) ⇒
    MEM n'' (flat_edges (FILTER (λp. FST p ≠ n') l))
        
Proof
  Induct >-
   gvs[flat_edges_def] >>
  rpt strip_tac >>
  PairCases_on ‘h’ >>
  gvs[] >|[
    
    gvs[flat_edges_def] >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘h0’, ‘n''’, ‘a’, ‘b’])) >>
    gvs[] >>
    Cases_on ‘MEM (h0,a,b) l’ >> gvs[] >>
    imp_res_tac list_not_merged_flat_membership1
    ,
    
    Cases_on ‘h0=n'’ >> gvs[] >|[
        imp_res_tac mem_triple_map_fst
        ,
        
        gvs[flat_edges_def] >>
        first_x_assum (strip_assume_tac o (Q.SPECL [‘n'’, ‘n''’, ‘a’, ‘b’])) >>
        gvs[]
           
      ]
  ]
QED





Theorem list_merged_flat_membership1:        
  ∀ l n'' a b h1 h2.
    ALL_DISTINCT (MAP FST l) ∧
    (h1 ≠ h2 ∧ h2 ≠ n'')∧
    MEM (h1,a,b) l ∧
    MEM (h2,a,b) l ⇒
    MEM n'' (flat_edges l) ⇒
    MEM n'' (flat_edges (FILTER (λp. FST p ≠ h2) l))
Proof  
 Induct >-
  gvs[flat_edges_def] >>
 rpt strip_tac >>
 PairCases_on ‘h’ >>
 gvs[] >|[
    gvs[flat_edges_def] >>
    Cases_on ‘n'' = a ∨ n'' = b’ >> gvs[] >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘n''’, ‘a’, ‘b’, ‘n''’, ‘h2’])) >>
    metis_tac[list_not_merged_flat_membership2]
    ,
    gvs[flat_edges_def] >>

    first_x_assum (strip_assume_tac o (Q.SPECL [‘a’, ‘a’, ‘b’, ‘h1’, ‘h0’])) >>
    gvs[] >>
    
    Cases_on ‘MEM (h0,a,b) l’ >> gvs[] >>
    imp_res_tac mem_triple_map_fst >> gvs[] >|[
        imp_res_tac flat_edges_mem_triv1 >> gvs[]
        ,
        imp_res_tac flat_edges_mem_triv2 >> gvs[]
        ,

        
        Cases_on ‘n'' = a’ >-
         metis_tac[flat_edges_mem_triv1,flat_edges_mem_triv2] >>
        
        Cases_on ‘n''=b’ >-
         metis_tac[flat_edges_mem_triv1,flat_edges_mem_triv2] >>

        assume_tac list_not_merged_flat_membership1 >> 
        first_x_assum (strip_assume_tac o (Q.SPECL [‘l’, ‘n''’, ‘h0’])) >>
        gvs[]
      ]
    ,
    
    Cases_on ‘h0=h2’ >> gvs[] >|[
        imp_res_tac mem_triple_map_fst
        ,
        
        gvs[flat_edges_def] >>
        metis_tac[]
      ]
  ]
QED





Theorem merge_edges_membership:
  ∀ l l' n n' a b h.
    (a ≠ n' ∧ b ≠ n') ∧
    MEM (n,a,b) l ∧
    merge_edges l h n' = l' ⇒
    MEM (n,a,b) l'
Proof
  Induct_on ‘l’ >>
  rpt strip_tac >-
   gvs[merge_edges_def, MEM_MAP] >>
  rgs[Once merge_edges_list_cons] >|[
    PairCases_on ‘h’ >>
    gvs[] >>
    DISJ1_TAC >>
    simp[merge_edges_def]
    ,
    gvs[]
  ]
QED



Theorem head_mem_not_changed_in_merge:
  ∀ l l' n n' a b c.
    ALL_DISTINCT (MAP FST l') ∧
    MEM (a,b,c) l' ∧
    merge_edges l' n n' = l ⇒
    ∃ b' c' . MEM (a,b',c') l
Proof
  rpt gen_tac >> strip_tac >>
  imp_res_tac mem_triple_map_fst >>
  imp_res_tac map_fst_merge_edges >>
              
  gvs[MEM_MAP] >>
  fs[merge_edges_def] >>
  
  qexists_tac ‘if b = n' then n else b’ >>
  qexists_tac ‘if c = n' then n else c’ >>
  fs[] >>
  
  Cases_on ‘b=n'’ >> gvs[] >>
  Cases_on ‘c=n'’ >> gvs[] >>
  Cases_on ‘c=b’ >> gvs[] >>
  PairCases_on ‘y’ >> gvs[] >>
  
  gvs[MEM_MAP] >>

  FIRST [
      qexists_tac ‘(y0,b,b)’>> gvs[] >> decide_tac,
      qexists_tac ‘(y0,b,c)’>> gvs[]
    ]
QED


        

Theorem merge_normalize_for_mergable_nodes_exsists:
  ∀ edges t h0 h1 h2 a b n.
    ALL_DISTINCT (MAP FST edges) ∧
    (h0 ≠ a ∧ h0 ≠ b ) ∧
    (∀y. h0 = FST y ⇒ ¬MEM y t) ∧
    MEM (h0,a,b) edges ∧
    merge_edges edges n h0 = (h0,h1,h2)::t  ⇒
    ∃ t' . merge_edges ((h0,a,b)::t') n h0 = ((h0,h1,h2)::t) ∧ h1 = a ∧ h2 = b
Proof
  Cases_on ‘edges’ >> gvs[] >>
  rpt strip_tac >>
  gvs[Once merge_edges_list_cons] >>
  simp[Once merge_edges_list_cons] >>
  qexists_tac ‘t’ >> gvs[] >>
  rgs[ Once $ GSYM merge_edges_list_cons] >>
  
  gvs[Once merge_edges_list_normalize] >>
  gvs[merge_edges_def] >>
  
  PairCases_on ‘h’ >>
  gvs[MEM_MAP]
QED




Theorem merge_normalize_for_mergable_nodes_concrete:
  ∀ edges t h0 h1 h2 a b n.
    ALL_DISTINCT (MAP FST edges) ∧
    (h0 ≠ a ∧ h0 ≠ b ) ∧
    (∀y. h0 = FST y ⇒ ¬MEM y t) ∧
    MEM (h0,a,b) edges ∧
    merge_edges edges n h0 = (h0,h1,h2)::t  ⇒
    merge_edges ((h0,a,b)::TL edges) n h0 = ((h0,h1,h2)::t) ∧ h1 = a ∧ h2 = b
Proof
  Cases_on ‘edges’ >> gvs[] >>
  rpt strip_tac >>
  gvs[Once merge_edges_list_cons] >>
  simp[Once merge_edges_list_cons] >>
  rgs[ Once $ GSYM merge_edges_list_cons] >>
  
  gvs[Once merge_edges_list_normalize] >>
  gvs[merge_edges_def] >>
  
  PairCases_on ‘h’ >>
  gvs[MEM_MAP]
QED

                                                                         

                                
                                                
Theorem dom_range_edges3_imp_adel_key_mem:
  ∀ edges root labels vars n n' n''  a b.
    n'' ≠ n' ∧ n ≠ n' ∧
    BDD_ordered (root,edges,labels) vars ∧
    ALL_DISTINCT (MAP FST edges) ∧
    MEM (n,a,b) edges ∧
    MEM (n',a,b) edges ∧
    MEM n (dom_range_edges3 edges) ∧
    MEM n'' (dom_range_edges3 (merge_edges edges n n')) ⇒
    MEM n'' (dom_range_edges3 (ADELKEY n' (merge_edges edges n n')))
Proof
            
  rpt strip_tac >>
  
  ‘(n ≠ a ∧ n' ≠ a ∧ n ≠ b ∧ n' ≠ b)’ by cheat >>
  ‘ ALL_DISTINCT (MAP FST (merge_edges edges n n')) ’ by metis_tac [all_distinct_fst_merge_edges] >>

  gvs[dom_range_edges3_def] >>
  
  Cases_on ‘(merge_edges edges n n') = []’ >-
   gvs[flat_edges_def] >>
  Cases_on ‘(merge_edges edges n n')’ >-
   gvs[flat_edges_def] >>
  PairCases_on ‘h’ >>
  
  
  gvs[MEM_MAP, ADELKEY_def, MEM_FILTER] >>
  rpt(BasicProvers.FULL_CASE_TAC >> gvs[]) >|[
    
    gvs[flat_edges_def] >>
    Cases_on ‘n'' = h0 ∨ n'' = h1 ∨ n'' = h2’ >> gvs[] >>
    
    Cases_on ‘edges’ >> gvs[] >|[
      
      ‘(if a = n' ∧ b = n' then (h0,h0)
        else if a = n' then (h0,b)
        else if b = n' then (a,h0)
        else (a,b)) =
       (h1,h2)’ by gvs[merge_edges_def] >>
      
      
      Cases_on ‘a = n' ∧ b = n'’ >> gvs[] >>
      Cases_on ‘a = n'’ >> gvs[] >>
      Cases_on ‘b = n'’ >> gvs[] >>
      
      Cases_on ‘n'' = h0 ∨ n'' = a ∨ n'' = b’ >> gvs[] >>
      
      ‘n = h0’ by gvs[merge_edges_def] >>
      gvs[] >>
      
      subgoal ‘MEM (n',a,b) t ’ >- ( rgs[Once merge_edges_list_normalize] >>
                                     metis_tac[merge_edges_membership] ) >>
      
      irule list_not_merged_flat_membership2 >> gvs[] >>
      srw_tac [SatisfySimps.SATISFY_ss][]
              
      ,
      
      ‘(if a = n' ∧ b = n' then (h0,h0)
        else if a = n' then (h0,b)
        else if b = n' then (a,h0)
        else (a,b)) =
       (h1,h2)’ by gvs[merge_edges_def] >>
      
      Cases_on ‘a = n' ∧ b = n'’ >> gvs[] >>
      Cases_on ‘a = n'’ >> gvs[] >>
      Cases_on ‘b = n'’ >> gvs[] >>
      
      ‘n' = h0’ by gvs[merge_edges_def] >>
      
      subgoal ‘MEM (n',a,b) t ’ >- ( rgs[Once merge_edges_list_normalize] >>
                                     metis_tac[merge_edges_membership] ) >>
      
      irule list_not_merged_flat_membership2 >> gvs[] >>
      srw_tac [SatisfySimps.SATISFY_ss][]
      ,
      
      PairCases_on ‘h’ >>
      
      ‘(if h1' = n' ∧ h2' = n' then (n,n)
        else if h1' = n' then (n,h2')
        else if h2' = n' then (h1',n)
        else (h1',h2')) =
       (h1,h2)’ by rgs[Once merge_edges_def] >>
      
      Cases_on ‘h1' = n' ∧ h2' = n'’ >> rgs[] >>
      Cases_on ‘h1' = n'’ >> rgs[] >>
      Cases_on ‘h2' = n'’ >> rgs[] >> gvs[] >|[
          
          ‘h0'=h0’ by gvs[merge_edges_def] >>
          rgs[Once merge_edges_list_normalize] >>
          subgoal ‘MEM (h1,a,b) t ’ >- ( metis_tac[merge_edges_membership] ) >>
          subgoal ‘MEM (h1',a,b) t ’ >- ( metis_tac[merge_edges_membership] ) >>
          rgs[flat_edges_def] >>
          metis_tac[list_merged_flat_membership1]
          ,
          ‘h0'=h0’ by gvs[merge_edges_def] >>
          rgs[Once merge_edges_list_normalize] >>
          subgoal ‘MEM (h1,a,b) t ’ >- ( metis_tac[merge_edges_membership] ) >>
          subgoal ‘MEM (h1',a,b) t ’ >- ( metis_tac[merge_edges_membership] ) >>
          rgs[flat_edges_def] >>
          metis_tac[list_merged_flat_membership1]
          ,
          ‘h0'=h0’ by gvs[merge_edges_def] >>
          rgs[Once merge_edges_list_normalize] >>
          subgoal ‘MEM (h2,a,b) t ’ >- ( metis_tac[merge_edges_membership] ) >>
          subgoal ‘MEM (h2',a,b) t ’ >- ( metis_tac[merge_edges_membership] ) >>
          rgs[flat_edges_def] >>
          metis_tac[list_merged_flat_membership1]
          ,
          ‘h0'=h0’ by gvs[merge_edges_def] >>                        
          rgs[Once merge_edges_list_normalize] >>
          subgoal ‘MEM (n,a,b) t ’ >- ( metis_tac[merge_edges_membership] ) >>
          subgoal ‘MEM (n',a,b) t ’ >- (  metis_tac[merge_edges_membership] ) >>

          rgs[flat_edges_def] >|[

          irule list_merged_flat_membership1 >> gvs[] >>
          qexistsl_tac [‘a’,‘b’, ‘h1’] >>
          gvs[]
          ,
          irule list_merged_flat_membership1 >> gvs[] >>
          qexistsl_tac [‘a’,‘b’, ‘h2’] >>
          gvs[]
          ,
          Cases_on ‘n=n''’ >> gvs[] >|[
              irule list_not_merged_flat_membership2 >> gvs[] >>
              srw_tac [SatisfySimps.SATISFY_ss][]
              ,
              irule list_merged_flat_membership1 >> gvs[] >>
              qexistsl_tac [‘a’,‘b’, ‘n’] >>
              gvs[] 
            ]                  
            ]
        ]
    ] 
                                
    ,
    
    
    (* because of distinct we know that h1 and h2 are equal to a b from merge def*)
    assume_tac merge_normalize_for_mergable_nodes_concrete >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘edges’, ‘t’, ‘h0’, ‘h1’, ‘h2’, ‘a’, ‘b’, ‘n’])) >>
    gvs[] >>

    
    ‘¬ MEM (h0,a,b) t’ by gvs[] >> (* from ∀y. h0 = FST y ⇒ ¬MEM y t*)
    ‘¬MEM h0 (MAP FST t)’ by gvs[MEM_MAP] >>
    
    
    Cases_on ‘edges = []’ >> gvs[] >>
    Cases_on ‘edges’ >> gvs[]  >|[
        ‘h0=n’ by gvs[merge_edges_def] >> gvs[]
        ,
        rgs[Once merge_edges_list_normalize] >>
        gvs[flat_edges_def] >|[
            (* since n ≠ h0 assumption0, then n node is a member*)
            irule flat_edges_mem_triv1 >> gvs[] >>
            qexistsl_tac [‘b’,‘n’] >> gvs[] >>
            irule merge_edges_membership >>
            qexistsl_tac [‘n’,‘t'’, ‘h0’] >> gvs[] 
            ,
            irule flat_edges_mem_triv3 >> gvs[] >> 
            qexistsl_tac [‘a’,‘n’] >> gvs[] >>
            irule merge_edges_membership >>
            qexistsl_tac [‘n’,‘t'’, ‘h0’] >> gvs[] 
            ,
            irule list_not_merged_flat_membership1 >>
            gvs[]
          ]
        ,
        rgs[Once merge_edges_list_normalize] >>

        irule list_not_merged_flat_membership1 >>
        rgs[] >>
              
        rgs[flat_edges_def] >>
        (subgoal ‘MEM (n,a,b) t ’ >- ( metis_tac[merge_edges_membership] ) >>
        metis_tac[mem_input_then_in_flattened])
      ]
  ]
QED                                          
                                             

Theorem merge_edges_delete_some:
  ∀ edges n n' x.
    n ≠ n' ∧
    ALOOKUP (merge_edges edges n n') n = SOME x ⇒
    ALOOKUP (ADELKEY n' (merge_edges edges n n')) n = SOME x
Proof
  rw[] >>
  fs[ALOOKUP_ADELKEY]
QED



Theorem mem_dom_normalize_or:
  ∀ l h n''.
    MEM n'' (dom_range_edges (h++l)) = (MEM n'' (dom_range_edges h) ∨ MEM n'' (dom_range_edges l))
Proof
  rw[dom_range_edges_def]
QED


Theorem mem_dom_normalize_h_or:
  ∀ l h n''.
    MEM n'' (dom_range_edges (h::l)) = (MEM n'' (dom_range_edges [h]) ∨ MEM n'' (dom_range_edges l))
Proof
  rw[dom_range_edges_def]
QED



Theorem all_distinct_dom_range_edges:
  ∀ l . ALL_DISTINCT (dom_range_edges l)
Proof
  rw[dom_range_edges_def]
QED
        
Theorem all_distinct_dom_range3_edges:
  ∀ l . ALL_DISTINCT (dom_range_edges3 l)
Proof
  rw[dom_range_edges3_def]
QED


Theorem all_distinct_mem_cases:
  ∀ l h a. ALL_DISTINCT (h::l) ⇒
       ((MEM a l ∧ a ≠ h) ∨ ( ¬ MEM a l ∧ a = h) ∨  ¬ MEM a (h::l) ) 
Proof
  Induct >>
  gvs[MEM] >>
  rpt strip_tac >>
  gvs[] >>
  res_tac >> gvs[] >>
  Cases_on ‘a=h’ >> gvs[]          
QED



        

Theorem mem_edges_imp_mem_merge_h:
∀ h n n' n''.
  n ≠ n' ∧ n'' ≠ n'  ∧
   MEM n'' (dom_range_edges [h]) ⇒
   MEM n'' (dom_range_edges (merge_edges [h] n n'))
Proof
  rpt strip_tac >>
  PairCases_on ‘h’ >>
  gvs[dom_range_edges_def] >>
  gvs[merge_edges_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> rgs[])
QED

        
Theorem not_mem_edges_imp_mem_merge_h1:
∀ h n n' n''.
  n ≠ n' ∧ n'' ≠ n'  ∧
  MEM n (dom_range_edges [h]) ∧
  ¬ MEM n'' (dom_range_edges [h]) ⇒
  ¬ MEM n'' (dom_range_edges (merge_edges [h] n n'))
Proof
  rpt strip_tac >>
  PairCases_on ‘h’ >>
  gvs[dom_range_edges_def] >>
  gvs[merge_edges_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> rgs[])
QED


        
        
Theorem mem_edges_imp_mem_merge_imp1:     
  ∀ r edges labels n n' n''.
    n ≠ n' ∧ n'' ≠ n' ∧
    MEM n'' (dom_range_edges edges) ⇒
    MEM n'' (dom_range_edges (merge_edges edges n n'))
Proof
  
  Induct_on ‘edges’ >-
   gvs[dom_range_edges_def] >>
  rpt strip_tac >>
  
  rgs[Once merge_edges_list_cons] >>
  rw[mem_dom_normalize_or] >>
  
  qpat_x_assum ‘MEM n'' (dom_range_edges (h::edges))’
               (fn thm => assume_tac (SIMP_RULE (srw_ss()) [Once mem_dom_normalize_h_or] thm)) >>
  rw[] >>
  rgs[mem_edges_imp_mem_merge_h]
QED                    
        
                                                        
    

Theorem MEM_MAP_triple:
  ∀f l x. MEM x (MAP f l) ⇔ ∃y. MEM y l ∧ x = f y
Proof
  gvs[MEM_MAP] >>
  metis_tac[]
QED

Theorem MEM_FLAT_triple:
  ∀ll x. MEM x (FLAT ll) ⇔ ∃l. MEM l ll ∧ MEM x l
Proof
  rw[MEM_FLAT]
QED

(* Key lemma: what does it mean for an element to be in dom_range_edges *)
Theorem MEM_dom_range_edges:
  ∀edges x. MEM x (dom_range_edges edges) ⇔ 
           ∃a b c. MEM (a,b,c) edges ∧ (x = a ∨ x = b ∨ x = c)
Proof
  rw[dom_range_edges_def] >>
  rw[MEM_FLAT_triple, MEM_MAP_triple] >>
  eq_tac 
  >- (strip_tac >>
      Cases_on ‘y’ >> Cases_on ‘r’ >> fs[] >>
      qexists_tac ‘q’ >> qexists_tac ‘q'’ >> qexists_tac ‘r'’ >>
      rw[] >> fs[MEM])
  >- (strip_tac >>
      qexists_tac ‘(λ(k,v1,v2). [k; v1; v2]) (a,b,c)’ >> gvs[] >>
      qexists_tac ‘(a,b,c)’ >>
      rw[] >> fs[MEM])
QED



Theorem not_mem_edges_imp_mem_merge_imp1: 
  ∀ r edges labels n n' n''.
    n ≠ n' ∧ n'' ≠ n' ∧
    MEM n (dom_range_edges edges) ∧
    ¬MEM n'' (dom_range_edges edges) ⇒
    ¬MEM n'' (dom_range_edges (merge_edges edges n n'))
Proof
  rw[] >>
  CCONTR_TAC >>
  fs[] >>

  ‘∃a b c. MEM (a,b,c) (merge_edges edges n n') ∧ 
           (n'' = a ∨ n'' = b ∨ n'' = c)’ by metis_tac[MEM_dom_range_edges] >>

  fs[merge_edges_def, MEM_MAP] >>
  Cases_on ‘y’ >> Cases_on ‘r’ >> fs[] >>
  rename1 ‘MEM (a0,b0,c0) edges ’>>
  rw[] >|[
    (* case a *)
     metis_tac[MEM_dom_range_edges]
    ,
    (* case b *)
    Cases_on ‘b0 = n' ∧ c0 = n'’ >|[
        gvs[]
        ,
        Cases_on ‘b0 = n' ∧ c0 = n'’ >> gvs[] >>
        Cases_on ‘b0 = n'’ >> gvs[] >>
        Cases_on ‘c0 = n'’ >> gvs[] >>
        metis_tac[MEM_dom_range_edges]
      ]
    ,
    (* case c *)
        Cases_on ‘b0 = n' ∧ c0 = n'’ >|[
        gvs[]
        ,
        Cases_on ‘b0 = n' ∧ c0 = n'’ >> gvs[] >>
        Cases_on ‘b0 = n'’ >> gvs[] >>
        Cases_on ‘c0 = n'’ >> gvs[] >>
        metis_tac[MEM_dom_range_edges]
      ]
  ]
QED

                    


Theorem ADELKEY_cons_h:
  ∀ l h n'.
    ADELKEY n' (h::l) = ADELKEY n' [h] ++ ADELKEY n' l
Proof
  rw[ADELKEY_def]
QED


Theorem ADELKEY_normalize_append:
  ∀ l h n'.
    ADELKEY n' (h++l) = ADELKEY n' h ++ ADELKEY n' l
Proof
  rw[ADELKEY_def, FILTER_APPEND]
QED

        
                 
Theorem dom_range_edges_adelkey_normalize_imp1:
  ∀ h l n' n''.
    n'' ≠ n' ⇒
    MEM n'' (dom_range_edges (ADELKEY n' l)) ⇒
    MEM n'' (dom_range_edges (ADELKEY n' (h::l)))
Proof
  rw[Once ADELKEY_cons_h] >>
  rw[mem_dom_normalize_or]
QED


        

Theorem dom_range_edges_adelkey_normalize_imp2:
  ∀ h l n' n''.
    n'' ≠ n' ∧
    ADELKEY n' [h] ≠ [] ∧
    MEM n'' (dom_range_edges [h]) ⇒
    MEM n'' (dom_range_edges (ADELKEY n' (h::l)))
Proof
  rpt strip_tac >>
  PairCases_on ‘h’ >>  
  gvs[dom_range_edges_def, ADELKEY_def, merge_edges_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[])

QED        




Theorem neg_merge_edges_triv1:           
  ∀ h0 h1 h2 n'.
  h0 ≠ n' ⇒
  ADELKEY n' (merge_edges [(h0,h1,h2)] h0 n') ≠ []
Proof
  rpt strip_tac >>
  gvs[dom_range_edges_def, ADELKEY_def, merge_edges_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) 
QED



      
Theorem dom_range_edges_not_mem_imp_del:        
  ∀ l n' n''.
    ¬ MEM n'' (dom_range_edges l) ⇒
    ¬ MEM n'' (dom_range_edges (ADELKEY n' l))
Proof
  Induct >>
  gvs[dom_range_edges_def, ADELKEY_def] >>
  rpt strip_tac >>
  Cases_on ‘FST h ≠ n'’ >> gvs[]
QED

 

Theorem look_some_in_delkey_imp_og:
  ∀ labels n n'.
    n ≠ n' ⇒
    (lookup_is_some (ADELKEY n labels) n' ⇔
       lookup_is_some labels n')
Proof
  Induct >>
  rpt strip_tac >>
  gvs[lookup_is_some_def, ALOOKUP_ADELKEY]
QED


Theorem alookup_delkey_imp_og:
  ∀ l n n' x.
    n ≠ n' ⇒
    (ALOOKUP (ADELKEY n l) n' = SOME x ) ⇒
    (ALOOKUP l n' = SOME x)
Proof
  Induct >>
  rpt strip_tac >>
  gvs[lookup_is_some_def, ALOOKUP_ADELKEY]
QED


Theorem delkey_alookup_imp_og:
  ∀ l n n' x.
    n ≠ n' ⇒
    (ALOOKUP l n' = SOME x) ⇒
             (ALOOKUP (ADELKEY n l) n' = SOME x )
Proof
Induct >>
rpt strip_tac >>
gvs[lookup_is_some_def, ALOOKUP_ADELKEY]
QED
        



Theorem merge_edges_elim_same_helper_l:
  ∀ h n n' n1 n2 n1' n2'.
    n1 ≠ n ∧    
    ALOOKUP (merge_edges [h] n n') n = SOME (n1,n2) ∧
    ALOOKUP [h] n = SOME (n1',n2') ⇒
    (n1' = n1)
Proof
  rpt strip_tac >>
  PairCases_on ‘h’ >>
  rpt strip_tac >>
  gvs[merge_edges_def] >>
  rgs[AllCaseEqs()] >>
  gvs[]
QED




Theorem merge_edges_elim_same_l:        
  ∀ edges l n n' n1 n2 n1' n2'.        
    n1 ≠ n ∧
    ALOOKUP (merge_edges edges n n') n = SOME (n1,n2) ∧
    ALOOKUP edges n = SOME (n1',n2') ⇒
    n1'=n1 
Proof
  Induct >-
   gvs[] >>
  rpt strip_tac >>
  
  rfs[Once merge_edges_list_cons] >>
  
  PairCases_on ‘h’ >>
  rfs[Once ALOOKUP_APPEND] >>
  
  rgs[] >>
  rgs[AllCaseEqs()] >>
                    
  rw[Once merge_edges_def] >>
  rgs[Once merge_edges_def] >>
  rgs[] >>
  rgs[AllCaseEqs()] >>
  
  res_tac >>
  metis_tac[merge_Theorem1]
QED


(****************************************************)
(****************************************************)
(****  merge_nodes delete from range      ***********)
(********  while ADELKEY from the domain ************)
(****************************************************)
(****************************************************)


val simp_easy_cases_tac = PairCases_on ‘h’ >>
                          gvs[dom_range_edges_def, ADELKEY_def, merge_edges_def] >>
                          rpt (BasicProvers.FULL_CASE_TAC >> gvs[]);

    
Theorem lookup_none_h_tail:
  ∀ edges h n'.
  ALOOKUP (h::edges) n' = NONE ⇒
  FST h ≠ n' ∧ ALOOKUP edges n' = NONE
Proof
    rw[ALOOKUP_def] >>
    PairCases_on ‘h’ >>
    gvs[] >>
    gvs[AllCaseEqs()]
QED


        
        
Theorem merge_imp_adel_key_case_key:
  ∀ edges n n' n''.
    n ≠ n' ∧ n'' ≠ n' ∧
    edges ≠ [] ∧
    MEM n'' (MAP (λ(k,v1,v2). k) (merge_edges edges n n')) ⇒
    MEM n'' (MAP (λ(k,v1,v2). k) (ADELKEY n' (merge_edges edges n n')))
Proof
  Induct >-
   gvs[merge_edges_def] >>
  rpt strip_tac >>
  
  rgs[Once merge_edges_list_cons] >>
  simp [Once merge_edges_list_cons] >>
  simp[Once ADELKEY_normalize_append] >>
  gvs[mem_dom_normalize_or] >|[
    
    simp_easy_cases_tac    
    ,
    Cases_on ‘edges’ >> gvs[] >>
    gvs[merge_edges_def]
  ]
QED


Theorem merge_edges_none_v1_both:
  ∀ edges n n' n''.
    n'' ≠ n' ∧
    ALL_DISTINCT (MAP FST edges) ∧
    ALOOKUP edges n' = NONE ∧
    MEM n'' (MAP (λ(k,v1,v2). v1) (merge_edges edges n n')) ∧
    ALOOKUP edges n = NONE ⇒
    MEM n'' (MAP (λ(k,v1,v2). v1) (ADELKEY n' (merge_edges edges n n')))
Proof
     Induct >>
     rpt strip_tac >-
      gvs[merge_edges_def] >>
     simp_easy_cases_tac
QED



Theorem dom_range_edges3_imp_adel_key_mem_none:
  ∀ edges n n' n''.
    n'' ≠ n' ∧
    ALOOKUP edges n' = NONE ∧
    MEM n (dom_range_edges3 edges) ∧
    MEM n'' (dom_range_edges3 (merge_edges edges n n'))
    ⇒
    MEM n'' (dom_range_edges3 (ADELKEY n' (merge_edges edges n n')))
Proof
  rw[] >>
  gvs[dom_range_edges3_def] >>
  gvs[MEM_MAP, ADELKEY_def, MEM_FILTER] >>
  rpt(BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  irule list_not_merged_flat_membership1 >> gvs[] >>
  gvs[ALOOKUP_NONE] >>
  metis_tac [map_fst_merge_edges]
QED


Theorem dom_range_edges_imp_adel_key_mem_none:
  ∀ edges n n' n''.
    n'' ≠ n' ∧
    ALOOKUP edges n' = NONE ∧
    MEM n (dom_range_edges edges) ∧
    MEM n'' (dom_range_edges (merge_edges edges n n'))
    ⇒
    MEM n'' (dom_range_edges (ADELKEY n' (merge_edges edges n n')))
Proof
  fs[GSYM dom_range_edges1_3_eq] >>
  metis_tac[dom_range_edges3_imp_adel_key_mem_none]
QED       
    



Theorem dom_range_edges_imp_adel_key_mem:
  ∀edges root labels vars n n' n'' a b.
    n'' ≠ n' ∧ n ≠ n' ∧ BDD_ordered (root,edges,labels) vars ∧
    ALL_DISTINCT (MAP FST edges) ∧
    MEM (n,a,b) edges ∧ MEM (n',a,b) edges ∧
    MEM n (dom_range_edges edges) ∧
    MEM n'' (dom_range_edges (merge_edges edges n n')) ⇒
    MEM n'' (dom_range_edges (ADELKEY n' (merge_edges edges n n')))
Proof
  fs[GSYM dom_range_edges1_3_eq] >>
  metis_tac[dom_range_edges3_imp_adel_key_mem]
QED


    
Theorem merge_edges_preserve_nodes:
  ∀ edges n n' n'' root labels vars.
    n'' ≠ n' ∧ n ≠ n' ∧
    BDD_ordered (root,edges,labels) vars ∧
    ALL_DISTINCT (MAP FST edges) ∧
    ALOOKUP edges n = ALOOKUP edges n' ∧
    MEM n (dom_range_edges edges) ∧
    MEM n'' (dom_range_edges (merge_edges edges n n')) ⇒
    MEM n'' (dom_range_edges (ADELKEY n' (merge_edges edges n n')))
Proof

  rpt strip_tac >>
  Cases_on ‘ALOOKUP edges n’ >|[
    
    irule dom_range_edges_imp_adel_key_mem_none >>
    gvs[]
    ,
    
    ‘ALL_DISTINCT (MAP FST (merge_edges edges n n'))’ by gvs[GSYM all_distinct_fst_merge_edges] >>           
    PairCases_on ‘x’ >> 
    ‘MEM (n,x0,x1) edges’ by gvs[ALOOKUP_MEM] >>
    ‘MEM (n',x0,x1) edges’ by gvs[ALOOKUP_MEM] >>
    metis_tac[dom_range_edges_imp_adel_key_mem] 
  ]
QED



 

Theorem mergable_wf_labels_edges_same:          
∀ r edges labels n n' vars_consumed.
  ALL_DISTINCT (MAP FST edges) ∧
  BDD_ordered (r,edges,labels) vars_consumed ∧
  mergable (r,edges,labels) n n' ∧
  ( ∀n. MEM n (dom_range_edges edges) ⇔ MEM n (MAP FST labels)) ⇒
  (∀n''. MEM n'' (dom_range_edges (ADELKEY n' (merge_edges edges n n'))) ⇔
           MEM n'' (MAP FST (ADELKEY n' labels)))
Proof
  rw[mergable_def] >>
  Cases_on ‘n'' = n'’ >> gvs[] >|[
    gvs[merge_no_effect_on_unrelated_node_mem] >>
    gvs[ADELKEY_def, MEM_MAP, MEM_FILTER]
    ,
    gvs[eq_vars_in_labels_def] >>
    rpt(BasicProvers.FULL_CASE_TAC >> gvs[]) >>
    imp_res_tac ALOOKUP_MEM >>
    imp_res_tac mem_fst_snd >>
    gvs[] >>
    ‘MEM n (dom_range_edges edges)’ by gvs[] >>
    ‘MEM n' (dom_range_edges edges)’ by gvs[] >>
    ‘MEM n'' (dom_range_edges edges) ⇔ MEM n'' (MAP FST labels)’ by gvs[] >>

    (* for all three subgoals *)
    (
    Cases_on ‘MEM n'' (dom_range_edges edges)’  >|[
        ‘MEM n'' (dom_range_edges edges)’ by gvs[] >>
        ‘MEM n'' (dom_range_edges (merge_edges edges n n'))’  by metis_tac[mem_edges_imp_mem_merge_imp1] >>
        
        (* we know that merge_edges does not touch the domain, just the range ...
           deleting a key n' will be from the domain...
           but we know that they key that we deleted indeed has a copy in n in edges
         *)
        
        subgoal ‘MEM n'' (dom_range_edges (ADELKEY n' (merge_edges edges n n')))’ >-
         (
         irule merge_edges_preserve_nodes >>
         srw_tac [SatisfySimps.SATISFY_ss][]
         )>>
         
        ‘MEM n'' (MAP FST (ADELKEY n' labels))’ by metis_tac[mem_imp_adelkey_mem] >>
        gvs[]
        ,
        
        ‘¬MEM n'' (dom_range_edges (merge_edges edges n n'))’
          by imp_res_tac not_mem_edges_imp_mem_merge_imp1 >>
        gvs[] >>
        
        ‘~ MEM n'' (dom_range_edges (ADELKEY n' (merge_edges edges n n')))’ by
          gvs[dom_range_edges_not_mem_imp_del] >>
        gvs[] >>
        
        ‘¬MEM n'' (MAP FST (ADELKEY n' labels))’ by metis_tac[not_mem_imp_adelkey_mem] 
      ]
    ) ] 
QED


        
        
Theorem mergable_wf_internals_some:
  ∀ r edges labels n n'.
    (∀n''.  MEM n'' (MAP FST labels) ⇒
            (lookup_is_some edges n'' ⇔ is_lookup_internal labels n'')) ⇒
    (∀n''.  MEM n'' (MAP FST (ADELKEY n' labels)) ⇒
                
            (lookup_is_some (ADELKEY n' (merge_edges edges n n')) n'' ⇔
               is_lookup_internal (ADELKEY n' labels) n''))
Proof

rpt strip_tac >>
Cases_on ‘n'' = n'’ >> gvs[] >| [
    gvs[ADELKEY_def, MEM_MAP, MEM_FILTER]
    ,
    ‘MEM n'' (MAP FST labels)’ by metis_tac[adelkey_mem_imp_mem] >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘n''’])) >>
    
    gvs[look_some_in_delkey_imp_og] >>
    gvs[lookup_is_some_def] >>

    Cases_on ‘(∃y. ALOOKUP (merge_edges edges n n') n'' = SOME y)’ >> gvs[] >|[
             
        ‘∃x'. ALOOKUP edges n'' = SOME x'’ by metis_tac[merge_lookup_exists] >>
        gvs[is_lookup_internal_def] >>
        metis_tac[delkey_alookup_imp_og]
        ,
        
        Cases_on ‘ALOOKUP (merge_edges edges n n') n''’ >> gvs[] >>
        ‘ALOOKUP edges n'' = NONE’ by metis_tac[merge_lookup_none] >>

        gvs[is_lookup_internal_def] >>
        rpt strip_tac >>
            
        Cases_on ‘ALOOKUP (ADELKEY n' labels) n''’ >> gvs[] >>
        Cases_on ‘ALOOKUP labels n''’ >> gvs[] >>
                 
        gvs[map_fst_merge_edges, ALOOKUP_NONE] >>
        
        imp_res_tac alookup_delkey_imp_og >>
        ‘ALOOKUP labels n'' = SOME (non_termn (SOME x,p))’ by metis_tac[alookup_delkey_imp_og] >>
        gvs[]
          ]                                  
      ]
QED
        



        
Theorem adelkey_merge_none_imp_edges_none:
  ∀ edges n n' n''.
    n'' ≠ n' ∧
    ALOOKUP (ADELKEY n' (merge_edges edges n n')) n'' = NONE ⇒
    ALOOKUP edges n'' = NONE
Proof
  rw[] >>
  fs[ALOOKUP_ADELKEY] >>
  gvs[] >>
  metis_tac[merge_lookup_none] 
QED


                        

    
Theorem mergable_wf_leafs_some:
  ∀ r edges labels n n'.
    (∀n''.
       MEM n'' (MAP FST labels) ⇒
       (ALOOKUP edges n'' = NONE ⇔
          is_lookup_ntl labels n'' ∨ ∃p b. ALOOKUP labels n'' = SOME (termn (b,p)))) ⇒
          
    (∀n''.
       MEM n'' (MAP FST (ADELKEY n' labels)) ⇒
       (ALOOKUP (ADELKEY n' (merge_edges edges n n')) n'' = NONE ⇔
          is_lookup_ntl (ADELKEY n' labels) n'' ∨
          ∃p b. ALOOKUP (ADELKEY n' labels) n'' = SOME (termn (b,p))))
Proof

  rpt strip_tac >>
  Cases_on ‘n'' = n'’ >> gvs[] >| [
    gvs[ADELKEY_def, MEM_MAP, MEM_FILTER]
    ,
    ‘MEM n'' (MAP FST labels)’ by metis_tac[adelkey_mem_imp_mem] >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘n''’])) >>
    
    gvs[look_some_in_delkey_imp_og] >>

    Cases_on ‘ALOOKUP (ADELKEY n' (merge_edges edges n n')) n'' = NONE’ >> gvs[] >|[
        
        ‘ALOOKUP edges n'' = NONE’ by metis_tac[adelkey_merge_none_imp_edges_none] >>
        gvs[] >|[
          fs[ALOOKUP_ADELKEY] >>
          gvs[is_lookup_ntl_def] >>
          metis_tac[delkey_alookup_imp_og]
          ,
          Cases_on ‘ALOOKUP (ADELKEY n' (merge_edges edges n n')) n''’ >> gvs[] >>
          fs[ALOOKUP_ADELKEY] >>
          gvs[is_lookup_ntl_def] >>
          ‘∃x'. ALOOKUP edges n'' = SOME x'’ by metis_tac[merge_lookup_exists] >>
          Cases_on ‘ALOOKUP edges n''’ >> gvs[] >>
          fs[ALOOKUP_ADELKEY]   
        ]
        ,
        Cases_on ‘ALOOKUP (ADELKEY n' (merge_edges edges n n')) n''’ >> gvs[] >>
        fs[ALOOKUP_ADELKEY] >>
        gvs[is_lookup_ntl_def] >>
        ‘∃x'. ALOOKUP edges n'' = SOME x'’ by metis_tac[merge_lookup_exists] >>
        Cases_on ‘ALOOKUP edges n''’ >> gvs[] >>
        fs[ALOOKUP_ADELKEY]
        
      ]
  ]
QED







Theorem merge_edges_adelkey_empty_imp_cases:
  ∀edges n n'.
    ADELKEY n' (merge_edges edges n n') = [] ⇒
    EVERY (λe. FST e = n') edges
Proof
  Induct >> rw[] >>
  
  rename1 ‘h::t’ >>
  fs[merge_edges_def, ADELKEY_def, MAP] >>
  Cases_on ‘h’ >> Cases_on ‘r’ >> fs[] >>
  rpt (BasicProvers.full_case_tac >> gvs[]) >>
  
  rw[] >> res_tac >> gvs[]
QED


        

Theorem wf_non_empty_after_merge:
  ∀r edges labels n n'.
    ALL_DISTINCT (MAP FST edges) ∧
    edges ≠ [] ∧
    mergable (r,edges,labels) n n' ⇒
    ADELKEY n' (merge_edges edges n n') ≠ []
Proof
  rpt gen_tac >> strip_tac >>
  fs [mergable_def] >>
  
  (* case analysis on ALOOKUP results *)
  Cases_on ‘ALOOKUP edges n’ >> Cases_on ‘ALOOKUP edges n'’ >> fs[] >| [

    (* case both nodes have no edges *)
    fs[merge_edges_def, ADELKEY_def] >>
    Induct_on ‘edges’ >> rw[] >>
    PairCases_on ‘h’ >>  fs[]
    ,
    
    (* Case 4: Both have edges *)
    subgoal ‘∃e1 e2. MEM e1 edges ∧ MEM e2 edges ∧
                     FST e1 = n ∧ FST e2 = n'’ >- (
      imp_res_tac ALOOKUP_MEM >>
      PairCases_on ‘x’ >> gvs[] >>
      qexistsl_tac [‘(n,x0,x1)’, ‘(n',x0,x1)’] >> fs[]
      ) >>
    
      
    Cases_on ‘e1 = e2’ >| [
        (* same edge would mean n = n' - contradiction *)
        metis_tac[]
        ,
        
        (* different edges - show e1 remains *)
        ‘FST e1 ≠ n'’ by fs[] >>
        subgoal ‘MEM (let (a,(b,c)) = e1 in
                        (a, if b = n' ∧ c = n' then (n,n)
                            else if b = n' then (n,c)
                            else if c = n' then (b,n)
                            else (b,c))) (merge_edges edges n n')’ >- (
          gvs[merge_edges_def] >>
          gvs[MEM_MAP] >>
          qexists_tac ‘e1’ >> fs[] >> rw[]
          ) >>
          
        PairCases_on ‘e1’ >> rename1 ‘(src, (a,b))’ >>
        ‘src ≠ n'’ by fs[] >>
        fs[] >>
        fs[ADELKEY_def, FILTER_NEQ_NIL] >>
        qexists_tac ‘(src,
                      if a = n' ∧ b = n' then (n,n)
                      else if a = n' then (n,b)
                      else if b = n' then (a,n)
                      else (a,b))’ >> fs[]
                                        
      ]
  ]
QED

  



                                

(*********************************)
(*        MERGE  WFness          *)
(*********************************)        
Theorem merge_wf_preservation:        
  ∀ BDD n n' vars.
    BDD_ordered BDD vars ∧
    BDD_WF BDD ∧
    consumed_dom_bdd vars BDD ∧
    mergable BDD n n'
    ==>
    BDD_WF (merge BDD n n') 
Proof
  rpt strip_tac >>
  PairCases_on ‘BDD’ >>
  rename1 ‘(r,edges,labels)’ >>

  (* when there are no edges is simply wrong to do any optimizations *)
  Cases_on ‘edges = []’ >-
   (gvs[mergable_def, eq_vars_in_labels_def] >>
   gvs[BDD_WF_def]) >>

          
  gvs[BDD_WF_def, merge_def] >>
                  
  (* show that edges are distinct *)
  ‘∀n'' n n'.
     ALL_DISTINCT (MAP FST (ADELKEY n'' (merge_edges edges n n')))’
    by (imp_res_tac edges_distinct_in_del_key >> gvs[]) >>

  (* show that labels are distinct *)
  ‘∀n. ALL_DISTINCT (MAP FST (ADELKEY n labels))’
    by imp_res_tac ALL_DISTINCT_MAP_ADELKEY >> gvs[] >>

  ‘∀n''.  MEM n'' (dom_range_edges (ADELKEY n' (merge_edges edges n n'))) ⇔
          MEM n'' (MAP FST (ADELKEY n' labels))’ by imp_res_tac mergable_wf_labels_edges_same >> gvs[] >>

  imp_res_tac mergable_wf_internals_some >> gvs[] >>

  imp_res_tac mergable_wf_leafs_some >> gvs[] >> rw[] >>
  
  imp_res_tac wf_non_empty_after_merge
     
QED


                    

           
Theorem order_hold_for_merge: 
  ∀ r edges labels n n' n'' nl vars.
    BDD_WF (r,edges,labels) ∧
    mergable (r,edges,labels) n n' ⇒
    (
    (order_hold labels vars n'' n' ⇒ order_hold (ADELKEY n' labels) vars n'' n)
    ∧
    ( order_hold labels vars n'' nl ⇒ order_hold (ADELKEY n' labels) vars n'' nl)
    ) 
Proof
  rw[order_hold_def] >>
  rpt strip_tac >>
  gvs[mergable_def,ALOOKUP_ADELKEY,BDD_WF_def] >>
  gvs[eq_vars_in_labels_def] >>
  rpt (BasicProvers.full_case_tac >> gvs[])
QED





(*********************************)
(*       MERGE  Order            *)
(*********************************)       
Theorem merge_order_preservation:
  ∀ BDD n n' vars.
    BDD_ordered BDD vars ∧
    BDD_WF BDD ∧
    mergable BDD n n'
    ⇒
    BDD_ordered (merge BDD n n') vars 
Proof
  rpt strip_tac >>
                                                
  PairCases_on ‘BDD’ >>
  rename1 ‘(r,edges,labels)’ >>
  
  Cases_on ‘edges=[]’ >-
   (simp[BDD_ordered_def, merge_def, merge_edges_def] >>
    rpt strip_tac >> gvs[ADELKEY_def]) >>
  
  gvs[BDD_ordered_def, merge_def] >>
  rpt gen_tac >> strip_tac >>
  rename1 ‘ALOOKUP (ADELKEY n' (merge_edges edges n n')) n'' = SOME (nl,nr)’ >>
  
  Cases_on ‘n''=n'’ >> gvs[]  >|[

    simp[order_hold_def] >>
    rw[] >>
    gvs[ALOOKUP_ADELKEY]
    ,
    gvs[ALOOKUP_ADELKEY] >>
    ‘∃x'. ALOOKUP edges n'' = SOME x'’ by metis_tac[merge_lookup_exists] >>
    PairCases_on ‘x'’ >>
    rename1 ‘(nl',nr')’ >>
    
    (* according to the definition of nerge_edges, a parent of n' will have n' replaced by n,
       if not it stays the same ... *)
    rpt strip_tac >|[
        (* the left part*)
        
        Cases_on ‘nl=nl'’ >> gvs[]  >|[
          (* unaffected by the merge*)
          first_x_assum (strip_assume_tac o (Q.SPECL [‘n''’, ‘nl’, ‘nr'’])) >>
          gvs[] >>
          metis_tac[order_hold_for_merge]
          ,
          (* afftected by the merge, i.e. a parent of n' left node *)
          ‘nl'=n' ∧ nl=n’ by metis_tac[merge_parent_change] >>
          first_x_assum (strip_assume_tac o (Q.SPECL [‘n''’, ‘n'’, ‘nr'’])) >>
          gvs[] >>
          metis_tac [order_hold_for_merge]
        ]
        ,
        (* the right part*)
        Cases_on ‘nr=nr'’ >> gvs[]  >|[
            first_x_assum (strip_assume_tac o (Q.SPECL [‘n''’, ‘nl'’, ‘nr’])) >>
            gvs[] >>
            metis_tac[order_hold_for_merge]
            ,
            ‘nr'=n' ∧ nr=n’ by metis_tac[merge_parent_change] >>
            first_x_assum (strip_assume_tac o (Q.SPECL [‘n''’, ‘nl'’, ‘n'’])) >>
            gvs[] >>
            metis_tac [order_hold_for_merge]
          ]
      ]
                    
  ]
QED
                                




(*********************************)
(*       MERGE  Misc             *)
(*********************************) 

(* valid for merge and eliminate *)
Theorem merge_fv_final_preservation:                                
  ∀ BDD n n' vars rec.
    fv_in_BDD rec BDD vars  ⇒
    fv_in_BDD rec (merge BDD n n') vars
Proof

  rpt strip_tac >>
  PairCases_on ‘BDD’ >>
  rename1 ‘(r,edges,labels)’ >>
  
  fs[fv_in_BDD_def, merge_def, fv_in_labels_def] >>
  rpt strip_tac >>
  
  Cases_on ‘n''=n’ >> gvs[ALOOKUP_ADELKEY] >>
  res_tac
QED

        
(* valid for merge and eliminate *)
Theorem merge_consumed_dom_final_preservation:
  ∀ BDD n n' vars.
    consumed_dom_bdd vars BDD ⇒
    consumed_dom_bdd vars (merge BDD n n')
Proof

 rpt strip_tac >>
  PairCases_on ‘BDD’ >>
  rename1 ‘(r,edges,labels)’ >>
  
  fs[consumed_dom_bdd_def, merge_def] >>
  rpt strip_tac >>
  
  Cases_on ‘n''=n’ >> gvs[ALOOKUP_ADELKEY] >>
  res_tac
QED



val _ = export_theory ();

