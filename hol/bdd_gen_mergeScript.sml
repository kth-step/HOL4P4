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
       

    

(* fails *)                                                
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
              simp[Once EQ_SYM_EQ, Once BDD_sem_cases] 
              ,
                
              PairCases_on ‘x'’ >> gvs[] >>
              ‘∃x'. ALOOKUP edges n = SOME x'’ by  (imp_res_tac merge_lookup_exists >> gvs[]) >>
              PairCases_on ‘x'’ >> gvs[] >>    
              Cases_on ‘ALOOKUP labels n'’ >> gvs[] >>
              Cases_on ‘x'’ >> gvs[] >|[
                       
                  ‘∃pair. ALOOKUP edges n = SOME pair’ by metis_tac [merge_lookup_exists] >>
                  ‘∃ x'' p''. ALOOKUP labels n = SOME (non_termn (SOME x'',p'')) ’ by metis_tac[WF_imp_non_leaf_lbl] >>
                  gvs[]
                  ,
                        
                  Cases_on ‘p’ >> gvs[] >>
                  Cases_on ‘q’ >> gvs[] >|[
                           
                      ‘∃pair. ALOOKUP edges n = SOME pair’ by metis_tac [merge_lookup_exists] >>
                      ‘∃ x'' p''. ALOOKUP labels n = SOME (non_termn (SOME x'',p'')) ’ by metis_tac[WF_imp_non_leaf_lbl] >>
                      gvs[]        
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
                               
                             
                              first_x_assum (strip_assume_tac o (Q.SPECL [‘INDEX_OF (x':string) (vars_consumed: string list)’])) >>
                              gvs[PULL_FORALL] >>
                              first_x_assum (strip_assume_tac o (Q.SPECL [‘x'’, ‘vars_consumed’, ‘vars’, ‘r’, ‘edges’, ‘labels’, ‘n’,
                                                                          ‘n'’, ‘n’, ‘nr_old’, ‘n1’,  ‘r'’, ‘mv’, ‘b’])) >>
                              rgs[] >>
                              
                              gvs[Once BDD_sem_cases] >>
                              simp[Once BDD_sem_cases] >>
                              gvs[ALOOKUP_ADELKEY]
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
              simp[Once EQ_SYM_EQ, Once BDD_sem_cases] 
              ,
                
              PairCases_on ‘x'’ >> gvs[] >>
              ‘∃x'. ALOOKUP edges n = SOME x'’ by  (imp_res_tac merge_lookup_exists >> gvs[]) >>
              PairCases_on ‘x'’ >> gvs[] >>    
              Cases_on ‘ALOOKUP labels n'’ >> gvs[] >>
              Cases_on ‘x'’ >> gvs[] >|[
                       
                  ‘∃pair. ALOOKUP edges n = SOME pair’ by metis_tac [merge_lookup_exists] >>
                  ‘∃ x'' p''. ALOOKUP labels n = SOME (non_termn (SOME x'',p'')) ’ by metis_tac[WF_imp_non_leaf_lbl] >>
                  gvs[]
                  ,
                        
                  Cases_on ‘p’ >> gvs[] >>
                  Cases_on ‘q’ >> gvs[] >|[
                           
                      ‘∃pair. ALOOKUP edges n = SOME pair’ by metis_tac [merge_lookup_exists] >>
                      ‘∃ x'' p''. ALOOKUP labels n = SOME (non_termn (SOME x'',p'')) ’ by metis_tac[WF_imp_non_leaf_lbl] >>
                      gvs[]        
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
                               
                             
                              first_x_assum (strip_assume_tac o (Q.SPECL [‘INDEX_OF (x':string) (vars_consumed: string list)’])) >>
                              gvs[PULL_FORALL] >>
                              first_x_assum (strip_assume_tac o (Q.SPECL [‘x'’, ‘vars_consumed’, ‘vars’, ‘r’, ‘edges’, ‘labels’, ‘n’,
                                                                          ‘n'’, ‘n’, ‘nr_old’, ‘n1’,  ‘r'’, ‘mv’, ‘b’])) >>
                              rgs[] >>
                              
                              gvs[Once BDD_sem_cases] >>
                              simp[Once BDD_sem_cases] >>
                              gvs[ALOOKUP_ADELKEY]
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


        

Theorem fv_in_labels_preserved:        
  ∀ r edges labels keys n n' varslist rec. 
    mergable (r,edges,labels) n n' ∧        
    fv_in_labels rec (ADELKEY n' labels) varslist  ⇒         
    fv_in_labels rec labels varslist
Proof
  rpt strip_tac >>
  gvs[fv_in_labels_def] >>
  rpt strip_tac >>
  Cases_on ‘n'' = n'’ >|[
    rgs[mergable_def] >>
    gvs[ALOOKUP_ADELKEY] >>
    res_tac >> gvs[]
    ,
    gvs[ALOOKUP_ADELKEY] >>
    res_tac >> gvs[]            
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





        
Theorem merge_correct:        
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





                     
(*       
Theorem mv_dom_bdd_eliminate_preserved:
  ∀ r edges labels keys n n' mv.
    ALL_DISTINCT (MAP FST labels) ∧
    eleminatble (r,edges,labels) n n' ∧
    ~is_unique_var labels n' ∧
    mv_dom_bdd mv (merge (r,edges,labels) n n') ⇒
    mv_dom_bdd mv (r,edges,labels)
Proof

  rpt strip_tac >>
  gvs[merge_def] >>
  gvs[mv_dom_bdd_def] >>
  rpt strip_tac >>
  Cases_on ‘n'' = n'’ >> gvs[] >|[
    rgs[eleminatble_def] >>
    gvs[ALOOKUP_ADELKEY] >>
    imp_res_tac not_unique_exsists_labels >>
    res_tac >> gvs[]
    ,
    gvs[ALOOKUP_ADELKEY] >>
    res_tac >> gvs[]            
  ]
QED

*)

        
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



(*
Theorem mv_dom_bdd_del_element_added:
  ∀ r labels edges mv n n' x p b'.  
    ALOOKUP labels n' = SOME (non_termn (SOME x,p)) ∧        
    mv_dom_bdd mv (r,ADELKEY n' (merge_edges edges n n'),ADELKEY n' labels) ⇒
    mv_dom_bdd (mv ⧺ [(x,b')]) (r,edges,labels)
Proof
  rpt strip_tac >>
  gvs[mv_dom_bdd_def] >>
  rpt strip_tac >>
  Cases_on ‘n'' = n'’ >>
  rgs[mergable_def] >>
  gvs[ALOOKUP_ADELKEY] >>
  res_tac >> gvs[] >>
  
  Cases_on ‘n=n'’ >>
  gvs[lookup_is_some_def] >>
  
  gvs[ALOOKUP_APPEND] >>
  gvs[AllCaseEqs()]>>
  Cases_on ‘ALOOKUP mv x’ >> gvs[]              
QED
*)


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


       

val _ = export_theory ();
