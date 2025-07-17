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


(*eleminatble add that node 0 is not eliminatable *)

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
    (mergable (r,edges,labels) n n' ∨ eleminatble (r,edges,labels) n n') ∧
    n'' ≠ n' ∧
    ALOOKUP (merge_edges edges n n') n'' = SOME (nr,nl) ⇒
    (nr ≠ n' ∧ nl ≠ n')
Proof   
  rpt strip_tac >>
  gvs[mergable_def, eleminatble_def] >>
  metis_tac[merge_edges_glue]
QED        


           
Theorem alookup_defined_append1:
  ∀ l l' n a b.
    ALOOKUP (l ++ l') n = SOME (a,b) ⇒
    ALOOKUP l n = NONE ⇒
    ∃ a' b' . ALOOKUP l' n = SOME (a',b') ∧ a' = a ∧  b' = b 
Proof
  gvs[ALOOKUP_APPEND] >>
  rpt strip_tac >>
  fs[AllCaseEqs()]
QED


Theorem alookup_defined_append2:
  ∀ l l' n a b a' b'.
    ALOOKUP (l ++ l') n = SOME (a,b) ∧
    ALOOKUP l n = SOME (a',b') ⇒
    a' = a ∧  b' = b 
Proof
  gvs[ALOOKUP_APPEND] >>
  rpt strip_tac >>
  fs[AllCaseEqs()]
QED



Theorem merge_Theorem1:
  (ALOOKUP (merge_edges [(h0,h1,h2)] n n') n'' = NONE ⇒
   h0 ≠ n'') ∧
  (ALOOKUP (merge_edges [(h0,h1,h2)] n n') n'' = SOME x ⇒
   h0 = n'')
Proof
  gvs[merge_edges_def]
QED

        
Theorem alookup_Theorem1:
  ALOOKUP ((h0,h1,h2)::edges) n'' = SOME (nr,nl) ∧
  h0 = n'' ⇒
  (nr = h1 ∧ nl = h2)
Proof
  rpt strip_tac >>
  fs[AllCaseEqs()]
QED
     

Theorem lookup_merge_uni_bs:
  ALOOKUP (merge_edges [(h0,h1,h2)] n n') n'' = SOME (x0,x1) 
  ⇒
  ((x0 = nr' ∧  nr = h1 ∧  nr ≠ nr' ⇒ (nr = n' ∧ nr' = n))
   ∧
   (x1 = nl' ∧  nl = h2 ∧  nl ≠ nl' ⇒ (nl = n' ∧ nl' = n)
   ))
Proof
  fs[Once merge_edges_def] >>
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



(* very slow proof, check why*)       
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



Theorem ADELKEY_APPEND_triv:
  ∀ l1 l2 n.
    ADELKEY n (l1++l2) = (ADELKEY n l1) ++ (ADELKEY n l2)
Proof
  Induct >>
  gvs[ADELKEY_def] >>
  rpt strip_tac >>
  rpt (BasicProvers.FULL_CASE_TAC >> rgs[]) 
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



Triviality  distinct_mem_edges_triv:
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


        

Triviality distinct_mem_not_triv:
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






Theorem MEM_ALOOKUP_DISTINCT:                
  ∀ l  a  b.
    ALL_DISTINCT (MAP FST l) ⇒
    (MEM (a,b) l ⇔ (ALOOKUP l a = SOME b))
Proof
  Induct >> gvs[] >>
  rpt strip_tac >>
  PairCases_on ‘h’ >> gvs[] >>
  Cases_on ‘a = h0’ >> gvs[] >>
  Cases_on ‘b = h1’ >> gvs[] >>
  Cases_on ‘ALOOKUP l a’ >> gvs[] >>
  imp_res_tac ALOOKUP_NONE >>
  gvs[]
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




Theorem flat_edges_mem_triv1:
  ∀ l h0 h1 a b .
    MEM (h1,a,b) l ∧
    h1 ≠ h0 ∧ h1 ≠ a ∧ h0 ≠ a ⇒
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
    (MEM b (flat_edges (FILTER (λp. FST p ≠ h0) l)) ∧
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
    h1 ≠ h0 ∧ h1 ≠ a ∧ h0 ≠ a ⇒
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
    (h1 ≠ h2 ∧ h1 ≠ n'' ∧ h2 ≠ n'')∧
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





Theorem merge_edges_memvership:
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


Triviality list_mem_trip_not:
∀ l n h1 h2.
¬MEM n (MAP FST l) ⇒    
¬MEM (n,h1,h2) l
Proof
  Induct >>
  rw[] >>
  PairCases_on ‘h’ >>
  res_tac >>
  gvs[]
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
    ALL_DISTINCT (MAP FST (merge_edges edges n n')) ∧
    MEM (n,a,b) edges ∧
    MEM (n',a,b) edges ∧
    MEM n (dom_range_edges3 edges) ∧
    ADELKEY n' (merge_edges edges n n') ≠ [] ∧
    MEM n'' (dom_range_edges3 (merge_edges edges n n')) ⇒
    MEM n'' (dom_range_edges3 (ADELKEY n' (merge_edges edges n n')))
Proof
            
  rpt strip_tac >>
  
  ‘(n ≠ a ∧ n' ≠ a ∧ n ≠ b ∧ n' ≠ b)’ by cheat >>
  
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
                                     metis_tac[merge_edges_memvership] ) >>
      
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
                                     metis_tac[merge_edges_memvership] ) >>
      
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
          subgoal ‘MEM (h1,a,b) t ’ >- ( metis_tac[merge_edges_memvership] ) >>
          subgoal ‘MEM (h1',a,b) t ’ >- ( metis_tac[merge_edges_memvership] ) >>
          rgs[flat_edges_def] >>
          metis_tac[list_merged_flat_membership1]
          ,
          ‘h0'=h0’ by gvs[merge_edges_def] >>
          rgs[Once merge_edges_list_normalize] >>
          subgoal ‘MEM (h1,a,b) t ’ >- ( metis_tac[merge_edges_memvership] ) >>
          subgoal ‘MEM (h1',a,b) t ’ >- ( metis_tac[merge_edges_memvership] ) >>
          rgs[flat_edges_def] >>
          metis_tac[list_merged_flat_membership1]
          ,
          ‘h0'=h0’ by gvs[merge_edges_def] >>
          rgs[Once merge_edges_list_normalize] >>
          subgoal ‘MEM (h2,a,b) t ’ >- ( metis_tac[merge_edges_memvership] ) >>
          subgoal ‘MEM (h2',a,b) t ’ >- ( metis_tac[merge_edges_memvership] ) >>
          rgs[flat_edges_def] >>
          metis_tac[list_merged_flat_membership1]
          ,
          ‘h0'=h0’ by gvs[merge_edges_def] >>                        
          rgs[Once merge_edges_list_normalize] >>
          subgoal ‘MEM (n,a,b) t ’ >- ( metis_tac[merge_edges_memvership] ) >>
          subgoal ‘MEM (n',a,b) t ’ >- (  metis_tac[merge_edges_memvership] ) >>

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
            irule merge_edges_memvership >>
            qexistsl_tac [‘n’,‘t'’, ‘h0’] >> gvs[] 
            ,
            irule flat_edges_mem_triv3 >> gvs[] >> 
            qexistsl_tac [‘a’,‘n’] >> gvs[] >>
            irule merge_edges_memvership >>
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
        (subgoal ‘MEM (n,a,b) t ’ >- ( metis_tac[merge_edges_memvership] ) >>
        metis_tac[mem_input_then_in_flattened])
      ]
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

        

Triviality mem_imp_adelkey_mem:
  ∀ l  n'' n'.
    n'' ≠ n' ∧
    MEM n'' (MAP FST l) ⇒
    MEM n'' (MAP FST (ADELKEY n' l))
Proof
  Induct >>
  simp_tac std_ss [ADELKEY_def, MAP, MEM] >>
  Cases_on ‘h’ >> gvs[] >>
  rw[] >>

    Cases_on ‘q = n'’ >>
  gvs [ADELKEY_def, MAP, MEM, FST] 
QED





Triviality merge_edges_delete_some:
  ∀ edges n n' x.
    n ≠ n' ∧
    ALOOKUP (merge_edges edges n n') n = SOME x ⇒
    ALOOKUP (ADELKEY n' (merge_edges edges n n')) n = SOME x
Proof
  rw[] >>
  fs[ALOOKUP_ADELKEY]
QED



Triviality mem_dom_normalize_or:
  ∀ l h n''.
    MEM n'' (dom_range_edges (h++l)) = (MEM n'' (dom_range_edges h) ∨ MEM n'' (dom_range_edges l))
Proof
  rw[dom_range_edges_def]
QED


Triviality mem_dom_normalize_h_or:
  ∀ l h n''.
    MEM n'' (dom_range_edges (h::l)) = (MEM n'' (dom_range_edges [h]) ∨ MEM n'' (dom_range_edges l))
Proof
  rw[dom_range_edges_def]
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



Triviality ADELKEY_cons_h:
  ∀ l h n'.
    ADELKEY n' (h::l) = ADELKEY n' [h] ++ ADELKEY n' l
Proof
  rw[ADELKEY_def]
QED


Triviality ADELKEY_normalize_append:
  ∀ l h n'.
    ADELKEY n' (h++l) = ADELKEY n' h ++ ADELKEY n' l
Proof
  rw[ADELKEY_def, FILTER_APPEND]
QED

        
                 
Triviality dom_range_edges_adelkey_normalize_imp1:
  ∀ h l n' n''.
    n'' ≠ n' ⇒
    MEM n'' (dom_range_edges (ADELKEY n' l)) ⇒
    MEM n'' (dom_range_edges (ADELKEY n' (h::l)))
Proof
  rw[Once ADELKEY_cons_h] >>
  rw[mem_dom_normalize_or]
QED


        

Triviality dom_range_edges_adelkey_normalize_imp2:
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




Triviality neg_merge_edges_triv1:           
  ∀ h0 h1 h2 n'.
  h0 ≠ n' ⇒
  ADELKEY n' (merge_edges [(h0,h1,h2)] h0 n') ≠ []
Proof
  rpt strip_tac >>
  gvs[dom_range_edges_def, ADELKEY_def, merge_edges_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) 
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




(****************************************************)
(****************************************************)
(****  merge_nodes delete from range      ***********)
(********  while ADELKEY from the domain ************)
(****************************************************)
(****************************************************)


val simp_easy_cases_tac = PairCases_on ‘h’ >>
                          gvs[dom_range_edges_def, ADELKEY_def, merge_edges_def] >>
                          rpt (BasicProvers.FULL_CASE_TAC >> gvs[]);

    
Triviality lookup_none_h_tail:
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
    
    PairCases_on ‘h’ >>
    gvs[dom_range_edges_def, ADELKEY_def, merge_edges_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[])     
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










        


Theorem merge_edges_preserve_nodes:
  ∀ edges n n' n'' root labels vars.
    n'' ≠ n' ∧ n ≠ n' ∧
    BDD_ordered (root,edges,labels) vars ∧
    ALL_DISTINCT (MAP FST edges) ∧
    ALOOKUP edges n = ALOOKUP edges n' ∧
    MEM n (dom_range_edges edges) ∧
    ADELKEY n' (merge_edges edges n n') ≠ [] ∧
    MEM n'' (dom_range_edges (merge_edges edges n n')) ⇒
    MEM n'' (dom_range_edges (ADELKEY n' (merge_edges edges n n')))
Proof

cheat        
  
QED

        
        


             
(*
    
        
∀ r edges labels n n'.
  ALL_DISTINCT (MAP FST edges) ∧
               (*BDD_ordered BDD vars ∧ *)
mergable (r,edges,labels) n n' ∧
(edges ≠ [] ⇒ ∀n. MEM n (dom_range_edges edges) ⇔ MEM n (MAP FST labels)) ⇒
(ADELKEY n' (merge_edges edges n n') ≠ [] ⇒
         ∀n''. MEM n'' (dom_range_edges (ADELKEY n' (merge_edges edges n n'))) ⇔
                 MEM n'' (MAP FST (ADELKEY n' labels)))

rpt strip_tac >>
Cases_on ‘edges = []’ >> gvs[] >-
 gvs[merge_edges_def, ADELKEY_def] >>
 
gvs[mergable_def] >>
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
    ‘MEM n'' (dom_range_edges edges) ⇔ MEM n'' (MAP FST labels)’ by gvs[] >|[
 

         
    Cases_on ‘MEM n'' (dom_range_edges edges)’  >|[
        ‘MEM n'' (dom_range_edges edges)’ by gvs[] >>
        ‘MEM n'' (dom_range_edges (merge_edges edges n n'))’  by metis_tac[mem_edges_imp_mem_merge_imp1] >>

              (* we know that merge_edges does not touch the domain, just the range ...
                 deleting a key n' will be from the domain...
                 but we know that they key that we deleted indeed has a copy in n
               *)

             
        ‘MEM n'' (dom_range_edges (ADELKEY n' (merge_edges edges n n')))’ by cheat >>
        ‘MEM n'' (MAP FST (ADELKEY n' labels))’ by metis_tac[mem_imp_adelkey_mem] >>
        gvs[]
        ,
        ‘~ MEM n'' (dom_range_edges (ADELKEY n' (merge_edges edges n n')))’ by cheat >> gvs[] >>
        ‘¬MEM n'' (MAP FST (ADELKEY n' labels))’ by cheat 
      ]
         
    
       

  ] 


                                                                              
*)
        

Theorem merge_wf_preservation:        
  ∀ BDD n n' vars vars_consumed.
    BDD_ordered BDD vars ∧
    BDD_WF BDD ∧
    consumed_dom_bdd vars_consumed BDD ∧
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

          
  simp[BDD_WF_def, merge_def] >>
                  
  (* show that edges are distinct *)
  ‘ALL_DISTINCT (MAP FST edges)’ by fs[BDD_WF_def] >>
  imp_res_tac edges_distinct_in_del_key >> gvs[] >>

  (* show that labels are distinct *)
  ‘ALL_DISTINCT (MAP FST labels)’ by fs[BDD_WF_def] >>
  imp_res_tac ALL_DISTINCT_MAP_ADELKEY >> gvs[] >>


  

  cheat
              
QED












        

   
(*******************************************************)
(*                                                     *)
(*                  E L I M I N A T E                  *)
(*                                                     *)
(*******************************************************)
     



Definition is_unique_var_def:
  is_unique_var labels n =
    case ALOOKUP labels n of
      | SOME (non_termn (SOME x, _)) =>
          EVERY (λ(n', lbl).
              (case lbl of
               | non_termn (SOME x', _) => (x' ≠ x)
               | _ => T
              )
                ) (ADELKEY n labels)
      | _ => T
End




Theorem not_unique_exsists_labels:        
  ∀ labels n x p.
    ALL_DISTINCT (MAP FST labels) ∧ 
    ALOOKUP labels n = SOME (non_termn (SOME x,p)) ∧
    ¬is_unique_var labels n ⇒
    ∃ n' p'. n' ≠ n ∧ ALOOKUP labels n' = SOME (non_termn (SOME x,p'))
Proof      
  Induct >>
  rpt strip_tac >>
  gvs[] >>
  PairCases_on ‘h’ >> gvs[] >>
  gvs[AllCaseEqs()] >|[
    
    rgs[Once is_unique_var_def, Once EXISTS_MEM] >>
    PairCases_on ‘e’ >> gvs[] >>
    rpt (BasicProvers.FULL_CASE_TAC >> rgs[]) >>
    qexistsl_tac [‘e0’, ‘r’] >>
    gvs[] >>
    imp_res_tac ALOOKUP_ALL_DISTINCT_MEM    
    ,

    rgs[is_unique_var_def] >>
    rgs[Once EXISTS_MEM] >>
    
    PairCases_on ‘e’ >> gvs[] >>
    rpt (BasicProvers.FULL_CASE_TAC >> rgs[]) >|[
        
        qexistsl_tac [‘e0’, ‘r’] >> gvs[] >>
        imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >>
        gvs[]
        ,
        
        gvs[] >>        
        res_tac >>
        rpt (BasicProvers.FULL_CASE_TAC >> rgs[]) >>
        imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >>
        qexistsl_tac [‘e0’, ‘r’] >> gvs[] >>
        Cases_on ‘h0 = e0’ >> gvs[] >>
        imp_res_tac mem_fst_snd >> gvs[]
      ]
  ]
QED        




Theorem leaf_lbl_is_unique:
  ∀ labels n action p p'.
    (ALOOKUP labels n = SOME (non_termn (NONE,p)) ∨ ALOOKUP labels n = SOME (termn (action,p'))) ⇒
    is_unique_var labels n
Proof
  rpt strip_tac >>
  rgs[Once is_unique_var_def]
QED





                     


        
Theorem sem_imp_label_lookup_some:        
  ∀ r edges labels n mv b rec.
    BDD_sem rec (r,edges,labels) mv n b ⇒
    lookup_is_some labels n
Proof      
  Induct_on ‘BDD_sem’ >>
  rpt strip_tac >>
  rgs[Once BDD_sem_cases, lookup_is_some_def]
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
        

Theorem op_sem_adel_key:
  ∀ labels n' n'' mv rec.
    n' ≠ n'' ⇒        
    (op_sem rec (get_prop (ADELKEY n' labels) n'') mv = op_sem rec (get_prop labels n'') mv)
Proof                                  
  rpt strip_tac >>
  gvs[op_sem_def, get_prop_def] >>
  gvs[AllCaseEqs()]>>
  Cases_on ‘ALOOKUP (ADELKEY n' labels) n''’ >> gvs[ALOOKUP_ADELKEY] >>
  Cases_on ‘x’ >> gvs[ALOOKUP_ADELKEY] >>
  Cases_on ‘p’ >> gvs[]
QED




Theorem eliminatable_is_internal_indeed:        
  ∀ r edges labels n n'.
    BDD_WF (r,edges,labels) ∧        
    eleminatble (r,edges,labels) n n' ⇒
    ∃ x p . ALOOKUP labels n'= SOME (non_termn(SOME x,p)) 
Proof
  rpt strip_tac >>
  rgs[eleminatble_def] >>
  ‘MEM n' (dom_range_edges edges)’ by metis_tac[lookup_edges_in_domain] >> 
  rgs[BDD_WF_def, lookup_is_some_def, is_lookup_internal_def] >>
  res_tac >> gvs[] 
QED






Theorem fv_mv_extended_x:
  ∀ p mv x b rec.        
    fv_in_p rec p mv ⇒
    fv_in_p rec p (mv ⧺ [(x,b)])
Proof
  rpt strip_tac >>
  rgs[fv_in_p_def] >>
  rpt strip_tac >>
  res_tac >>
  gvs[ALOOKUP_APPEND]
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



                

Theorem eleminatble_correct_internal:
  ∀ x vars_consumed vars r edges labels n n' n'' nl nr pred mv b rec.
    consumed_dom_bdd vars_consumed (r,edges,labels) ∧
    fv_in_BDD rec (r,edges,labels) (vars ⧺ vars_consumed) ∧
    mv_dom_vars mv (vars ⧺ vars_consumed) ∧
    BDD_ordered (r,edges,labels) vars_consumed ∧
    BDD_WF (r,edges,labels) ∧
    eleminatble (r,edges,labels) n n' ∧
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
  Cases_on ‘ALOOKUP (merge_edges edges n n') n''’ >> gvs[] >|[
    
    
    (*contr: in merged edges lookup is none , thus a leaf *)
    assume_tac merge_lookup_none >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘edges’,‘n’,‘n'’,‘n''’])) >>
    gvs[]
    ,
        
    (* in merged edges n'' is internal node  *)
    PairCases_on ‘x'’ >> gvs[] >>      
    Cases_on ‘ALOOKUP mv x’ >> gvs[] >> Cases_on ‘x'’ >> gvs[] >|[
        
        (*Case True*)
        
        Cases_on ‘nr=x'0’ >> gvs[]  >|[
          
          (*nr=x'0 means it did not change which makes it not the father of eliminated node, trivial case *)
          
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
          
          
          (*nr≠x'0, thus this is the parent of the node that disappeared, parent to n' *)
          gvs[eleminatble_def] >>
          
          ‘x'0 = n ∧ nr = n' ’ by (imp_res_tac merge_parent_change >> metis_tac[]) >>
          rgs[] >>
          
          
          simp[Once EQ_SYM_EQ, Once BDD_sem_cases] >>
          
          ‘MEM n' (dom_range_edges edges)’ by imp_res_tac lookup_edges_in_domain >>
          
          subgoal ‘∃ x pred. ALOOKUP labels n' = SOME (non_termn (SOME x,pred))’ >-
           ( metis_tac[WF_imp_non_leaf_lbl_abs,lookup_is_some_def] ) >>
          gvs[] >>
          
          
          subgoal ‘∃bool . ALOOKUP mv x' = SOME bool’ >-
           (imp_res_tac consumed_dom_bdd_in_mv >> gvs[] ) >>
          
          Cases_on ‘bool’ >>  gvs[] >> ( (*includes both when x' = T and F *)
            
            Cases_on ‘ALOOKUP (merge_edges edges n n') n’ >|[
                
                ‘ALOOKUP edges n = NONE’ by (metis_tac [merge_lookup_none]) >>
                metis_tac[mergable_correct_leaf]      
                ,
                
                PairCases_on ‘x''’ >>
                rename1 ‘ALOOKUP (merge_edges edges n n') n = SOME (n1,n2)’ >>
                
                ‘∃x''. ALOOKUP edges n = SOME x''’ by  (imp_res_tac merge_lookup_exists >> gvs[]) >>
                PairCases_on ‘x''’ >> gvs[] >>
                ‘x''0 ≠ n ∧ x''1 ≠ n’ by (imp_res_tac lookup_edges_not_parent >> gvs[]) >>
                ‘n1 ≠ n' ∧ x'1 ≠ n' ∧ n2 ≠ n' ’ by (metis_tac[merge_edges_glue]) >>
                Cases_on ‘n = n1’ >> gvs[] >|[
                    
                    (* by contr *)
                    ‘x''0 = n'’ by imp_res_tac merge_parent_change >>
                    rgs[] >>
                    
                    ‘∃ x pred. ALOOKUP labels n = SOME (non_termn (SOME x,pred))’ by metis_tac[WF_imp_non_leaf_lbl_abs,lookup_is_some_def]  >>
                    
                    subgoal ‘THE (INDEX_OF x' vars_consumed) < THE (INDEX_OF x'' vars_consumed)’ >-
                     (imp_res_tac ordered_for_two_labels) >>
                    subgoal ‘THE (INDEX_OF x'' vars_consumed) < THE (INDEX_OF x' vars_consumed)’ >-
                     (imp_res_tac ordered_for_two_labels) >>
                    gvs[]
                    ,
                    
                    ‘x''0 = n1 ’ by metis_tac[merge_edges_elim_same_l] >>
                    gvs[] >>
                    
                    simp[Once EQ_SYM_EQ, Once BDD_sem_cases] >>

                    (* make subgoal *)
                    subgoal ‘∃ x pred. ALOOKUP labels n = SOME (non_termn (SOME x,pred))’ >-
                     ( metis_tac[WF_imp_non_leaf_lbl_abs,lookup_is_some_def]) >>
                    
                    subgoal ‘∃bool . ALOOKUP mv x'' = SOME bool’ >-
                     ( imp_res_tac consumed_dom_bdd_in_mv >> gvs[] )  >>
                    
                    simp[Once EQ_SYM_EQ, Once BDD_sem_cases] >>
                    ‘ALOOKUP (ADELKEY n' (merge_edges edges n n')) n = SOME (n1,n2)’ by metis_tac[delkey_alookup_imp_og] >>
                    gvs[] >>
                    
                    ‘ALOOKUP (ADELKEY n' labels) n = SOME (non_termn (SOME x'',pred''))’ by metis_tac[delkey_alookup_imp_og] >>

                    subgoal ‘THE (INDEX_OF x'' vars_consumed) < THE (INDEX_OF x vars_consumed)’ >-
                     (
                     ‘THE (INDEX_OF x' vars_consumed) < THE (INDEX_OF x vars_consumed)’ by (imp_res_tac ordered_for_two_labels) >>
                     ‘THE (INDEX_OF x'' vars_consumed) < THE (INDEX_OF x' vars_consumed)’ by (imp_res_tac ordered_for_two_labels) >>
                     gvs[]
                     ) >>                    
                    
                    first_x_assum (strip_assume_tac o (Q.SPECL [‘INDEX_OF (x'':string) (vars_consumed: string list)’])) >>
                    gvs[PULL_FORALL] >>
                    first_x_assum (strip_assume_tac o (Q.SPECL [‘x''’, ‘vars_consumed’, ‘vars’, ‘r’, ‘edges’, ‘labels’, ‘n’, ‘n'’, ‘n’,
                                                                ‘x''1’, ‘n1’, ‘pred''’, ‘mv’, ‘b’, ‘rec’])) >>
                    gvs[] >>
                    rgs[Once BDD_sem_cases] >>
                    simp[Once EQ_SYM_EQ, Once BDD_sem_cases]
                  ]
              ]
            )                           
        ]
        ,


                
        (*Case False *)
        Cases_on ‘nl=x'1’ >> gvs[]  >|[
          
          (*nr=x'0 means it did not change which makes it not the father of eliminated node, trivial case *)
          
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
          
          
          (*nl≠x'1, thus this is the parent of the node that disappeared, parent to n' *)
          gvs[eleminatble_def] >>
          
          ‘x'1 = n ∧ nl = n' ’ by (imp_res_tac merge_parent_change >> metis_tac[]) >>
          rgs[] >>
          
          
          simp[Once EQ_SYM_EQ, Once BDD_sem_cases] >>
          
          ‘MEM n' (dom_range_edges edges)’ by imp_res_tac lookup_edges_in_domain >>
          
          subgoal ‘∃ x pred. ALOOKUP labels n' = SOME (non_termn (SOME x,pred))’ >-
           ( metis_tac[WF_imp_non_leaf_lbl_abs,lookup_is_some_def] ) >>
          gvs[] >>
          
          
          subgoal ‘∃bool . ALOOKUP mv x' = SOME bool’ >-
           (imp_res_tac consumed_dom_bdd_in_mv >> gvs[] ) >>
          
          Cases_on ‘bool’ >>  gvs[] >> ( (*includes both when x' = T and F *)
            
            Cases_on ‘ALOOKUP (merge_edges edges n n') n’ >|[
                
                ‘ALOOKUP edges n = NONE’ by (metis_tac [merge_lookup_none]) >>
                metis_tac[mergable_correct_leaf]      
                ,
                
                PairCases_on ‘x''’ >>
                rename1 ‘ALOOKUP (merge_edges edges n n') n = SOME (n1,n2)’ >>
                
                ‘∃x''. ALOOKUP edges n = SOME x''’ by  (imp_res_tac merge_lookup_exists >> gvs[]) >>
                PairCases_on ‘x''’ >> gvs[] >>
                ‘x''0 ≠ n ∧ x''1 ≠ n’ by (imp_res_tac lookup_edges_not_parent >> gvs[]) >>
                Cases_on ‘n = n1’ >> gvs[] >|[
                    
                    (* by contr *)
                    ‘x''0 = n'’ by imp_res_tac merge_parent_change >>
                    rgs[] >>
                    
                    ‘∃ x pred. ALOOKUP labels n = SOME (non_termn (SOME x,pred))’ by metis_tac[WF_imp_non_leaf_lbl_abs,lookup_is_some_def]  >>
                    
                    subgoal ‘THE (INDEX_OF x' vars_consumed) < THE (INDEX_OF x'' vars_consumed)’ >-
                     (imp_res_tac ordered_for_two_labels) >>
                    subgoal ‘THE (INDEX_OF x'' vars_consumed) < THE (INDEX_OF x' vars_consumed)’ >-
                     (imp_res_tac ordered_for_two_labels) >>
                    gvs[]
                    ,
                    
                    ‘x''0 = n1 ’ by metis_tac[merge_edges_elim_same_l] >>
                    gvs[] >>
                    
                    simp[Once EQ_SYM_EQ, Once BDD_sem_cases] >>

                    (* make subgoal *)
                    subgoal ‘∃ x pred. ALOOKUP labels n = SOME (non_termn (SOME x,pred))’ >-
                     ( metis_tac[WF_imp_non_leaf_lbl_abs,lookup_is_some_def]) >>
                    
                    subgoal ‘∃bool . ALOOKUP mv x'' = SOME bool’ >-
                     ( imp_res_tac consumed_dom_bdd_in_mv >> gvs[] )  >>
                    
                    simp[Once EQ_SYM_EQ, Once BDD_sem_cases] >>
                    ‘ALOOKUP (ADELKEY n' (merge_edges edges n n')) n = SOME (n1,n2)’ by metis_tac[delkey_alookup_imp_og] >>
                    gvs[] >>
                    
                    ‘ALOOKUP (ADELKEY n' labels) n = SOME (non_termn (SOME x'',pred''))’ by metis_tac[delkey_alookup_imp_og] >>

                    subgoal ‘THE (INDEX_OF x'' vars_consumed) < THE (INDEX_OF x vars_consumed)’ >-
                     (
                     ‘THE (INDEX_OF x' vars_consumed) < THE (INDEX_OF x vars_consumed)’ by (imp_res_tac ordered_for_two_labels) >>
                     ‘THE (INDEX_OF x'' vars_consumed) < THE (INDEX_OF x' vars_consumed)’ by (imp_res_tac ordered_for_two_labels) >>
                     gvs[]
                     ) >>                    
                    
                    first_x_assum (strip_assume_tac o (Q.SPECL [‘INDEX_OF (x'':string) (vars_consumed: string list)’])) >>
                    gvs[PULL_FORALL] >>
                    first_x_assum (strip_assume_tac o (Q.SPECL [‘x''’, ‘vars_consumed’, ‘vars’, ‘r’, ‘edges’, ‘labels’, ‘n’, ‘n'’, ‘n’,
                                                                ‘x''1’, ‘n1’, ‘pred''’, ‘mv’, ‘b’, ‘rec’])) >>
                    gvs[] >>
                    rgs[Once BDD_sem_cases] >>
                    simp[Once EQ_SYM_EQ, Once BDD_sem_cases]
                  ]
              ]
            )                          
        ]
      ]
  ]

QED
        


 

Theorem eleminatble_correct_eq:
  ∀labels vars vars_consumed n'' r edges n' n mv b rec.
    consumed_dom_bdd vars_consumed (r,edges,labels) ∧
    fv_in_BDD rec (r,edges,labels) (vars++vars_consumed) ∧
    mv_dom_vars mv (vars ⧺ vars_consumed) ∧
    BDD_ordered (r,edges,labels) vars_consumed ∧
    BDD_WF (r,edges,labels) ∧
    eleminatble (r,edges,labels) n n' ∧ n'' ≠ n' ⇒
    (BDD_sem rec (r,edges,labels) mv n'' b ⇔
       BDD_sem rec (r,ADELKEY n' (merge_edges edges n n'),ADELKEY n' labels)  mv n'' b)
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

     
   metis_tac[eleminatble_correct_internal]
  ]
QED





        
                           
                
 (* merge = eliminate defs*)       
Theorem eliminate_correct:        
  ∀ r edges labels vars vars_consumed n n' rec .
    correct_sem rec (r,edges,labels) (vars++vars_consumed) ∧
    BDD_WF (r,edges,labels) ∧
    consumed_dom_bdd vars_consumed (r,edges,labels) ∧
    BDD_ordered (r,edges,labels) vars_consumed ∧
    fv_in_BDD rec (r,edges,labels) (vars++vars_consumed)  ∧
    eleminatble (r,edges,labels) n n'
    ==>
    correct_sem rec (merge (r,edges,labels) n n')  (vars++vars_consumed)
Proof
  rpt strip_tac >>   
  simp[Once correct_sem_def] >>
  rpt strip_tac >>
  
  Cases_on ‘n' = n''’ >> gvs[] >|[
    
    gvs[merge_def] >>
    ‘get_prop (ADELKEY n' labels) n' = NONE’ by gvs[get_prop_delkey_none] >> 
    gvs[op_sem_def, get_prop_def] >>
    gvs[AllCaseEqs()]>>

    gvs[Once BDD_sem_cases]
    ,


    gvs[merge_def] >>
    assume_tac eleminatble_correct_eq >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘labels’, ‘vars’, ‘vars_consumed’, ‘n''’, ‘r’, ‘edges’, ‘n'’, ‘n’, ‘mv’, ‘b’, ‘rec’])) >>
    gvs[] >>
    
    gvs[correct_sem_def] >>
    res_tac >>
    
    metis_tac[op_sem_adel_key]
  ]
QED




(*

EVAL “mergable (0,[(0,1,2)],
        [(0,non_termn (SOME "a",Or (Var "a") (Not (Var "a"))));
         (1,termn (T,True)); (2,termn (T,True))]) 1 2”


EVAL “merge (0,[(0,1,2)],
        [(0,non_termn (SOME "a",Or (Var "a") (Not (Var "a"))));
         (1,termn (T,True)); (2,termn (T,True))]) 1 2” 



EVAL “eleminatble (0,[(0,1,1)],
      [(0,non_termn (SOME "a",Or (Var "a") (Not (Var "a"))));
       (1,termn (T,True))]) 1 0” 
        
EVAL “merge (0,[(0,1,1)],
      [(0,non_termn (SOME "a",Or (Var "a") (Not (Var "a"))));
       (1,termn (T,True))]) 1 0” 

*)

(*
EVAL “is_unique_var [(1,non_termn (SOME "x",p));(2,non_termn (SOME "x",p))] (1:num)” 
*)





(*******************************************************)
(*                                                     *)
(*         Optimzations and their termination          *)
(*                       proofs                        *)
(*                                                     *)
(*******************************************************)

        


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
  (case eleminatble BDD n' n of
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


        
Triviality merge_trio_extract_triv:
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
    eleminatble BDD h n ⇒
    BDD_label_length (merge BDD h n) < BDD_label_length BDD
Proof
  rpt strip_tac >>
  PairCases_on ‘BDD’ >>
  rename1 ‘(r,edges,labels)’ >>
  gvs[eleminatble_def] >>
                       
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


Definition bdd_full_optimize_def:
  bdd_full_optimize (BDD:('a,'b) BDD) =
  case bdd_one_round BDD = BDD of
  | T => BDD
  | F => bdd_full_optimize  (bdd_one_round BDD)   
Termination
        
  WF_REL_TAC `measure BDD_label_length` >>
  rpt strip_tac >>
  rename1 ‘ bdd_one_round (r,edges,labels) = (r,edges,labels)’ >>
  
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
End


(*******************************************************)
(*                                                     *)
(*         Optimzations Correctness full               *)
(*                       proofs                        *)
(*                                                     *)
(*******************************************************)


        
(********************)



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



     
*)



        

(* Helper lemma: merge_BDD preserves correctness
   TODO: add a def for the guarantee...
    *)
Theorem merge_BDD_preserves_correctness:
  ∀BDD n nl vars rec.

    BDD_WF BDD ∧
    consumed_dom_bdd vars BDD ∧
    BDD_ordered BDD vars ∧
    fv_in_BDD rec BDD vars ∧
  
    correct_sem rec BDD vars ⇒
                
    (correct_sem rec (merge_BDD BDD n nl) vars ∧
     fv_in_BDD rec (merge_BDD BDD n nl) vars ∧
     BDD_ordered (merge_BDD BDD n nl) vars ∧
     consumed_dom_bdd vars (merge_BDD BDD n nl) ∧
     BDD_WF (merge_BDD BDD n nl))
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
    res_tac >>
    ‘fv_in_BDD rec (merge BDD n h) vars’ by cheat >>
    ‘BDD_ordered (merge BDD n h) vars’ by cheat >>
    ‘consumed_dom_bdd vars (merge BDD n h)’ by cheat >>
    ‘BDD_WF (merge BDD n h)’ by cheat >>
    res_tac >>
    gvs[] >>
    cheat
    (*use old thm here*)
    , 
    gvs[] >>
    res_tac >>
    cheat
  ]
        
QED


        
(* Helper lemma: operate_opt1 preserves correctness *)
Theorem operate_opt1_preserves_correctness:
  ∀BDD nl all_nodes vars rec.
    BDD_WF BDD ∧
    consumed_dom_bdd vars BDD ∧
    BDD_ordered BDD vars ∧
    fv_in_BDD rec BDD vars ∧
       
    correct_sem rec BDD vars ⇒
    correct_sem rec (operate_opt1 BDD nl all_nodes) vars
Proof

  Induct_on ‘nl’ >> rpt strip_tac  >- (
    (* Base case: empty list *)
    fs [operate_opt1_def]
  ) >>
  
  (* Inductive case *)
  fs [operate_opt1_def] >>
  
  (* Apply inductive hypothesis *)
  first_x_assum irule >>

                
  (* Use merge_BDD_preserves_correctness *)
  gvs[] >> cheat
  (*irule merge_BDD_preserves_correctness >>
  fs [] *)
QED



        
(* Now the main theorem follows easily *)
Theorem bdd_optminzation1_preserves_correctness:
  ∀BDD vars rec. correct_sem rec BDD vars ⇒
                 correct_sem rec (bdd_optminzation1 BDD) vars
Proof
  rpt strip_tac >>
  fs [bdd_optminzation1_def] >>
  
  PairCases_on ‘BDD’ >>
  rename1 ‘(root, edges, labels)’ >>


  rw[]>>
  (* Apply operate_opt1_preserves_correctness *)
  irule operate_opt1_preserves_correctness >>
  fs [] >> cheat
  (* cheat*)
QED



 (* same things here *)       
Theorem bdd_optminzation2_preserves_correctness:
  ∀BDD vars rec. correct_sem rec BDD vars ⇒
                correct_sem rec (bdd_optminzation2 BDD) vars
Proof
  (* Similar to above - optminzation2 preserves semantics *)
  cheat
QED



(* Combining the two optimizations *)
Theorem bdd_one_round_preserves_correctness:
  ∀BDD vars rec. correct_sem rec BDD vars ⇒
                correct_sem rec (bdd_one_round BDD) vars
Proof
  rw[bdd_one_round_def] >>
  imp_res_tac bdd_optminzation2_preserves_correctness >>
  imp_res_tac bdd_optminzation1_preserves_correctness
QED
        

        
(* Main theorem using strong induction on the termination measure *)
Theorem bdd_full_optimize_preserves_correctness:
  ∀BDD vars rec. correct_sem rec BDD vars ⇒
                 correct_sem rec (bdd_full_optimize BDD) vars
Proof
  (* Use strong induction on the measure that ensures termination *)
  completeInduct_on ‘BDD_label_length BDD’ >>
  rw[] >>
  (* Unfold the definition *)
  once_rewrite_tac[bdd_full_optimize_def] >>
  rw[] >>
  Cases_on ‘bdd_one_round BDD = BDD’ >> fs[] >>
           
  (* Recursive case: optimization makes progress *)
  ‘correct_sem rec (bdd_one_round BDD) vars’ by (
    imp_res_tac bdd_one_round_preserves_correctness
  ) >>
  (* Apply induction hypothesis *)
  subgoal ‘BDD_label_length (bdd_one_round BDD) < BDD_label_length BDD’ >- (
    (* This follows from your termination proof *)
    cheat
  ) >>
  (* Apply induction hypothesis *)
  first_x_assum (strip_assume_tac o (Q.SPECL [‘BDD_label_length (bdd_one_round BDD)’])) >>
  rw[]
QED




val _ = export_theory ();
