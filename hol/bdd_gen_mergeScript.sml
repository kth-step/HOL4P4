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
     
val _ = new_theory "bdd_gen_merge";


Definition mergable_def:        
mergable ((r,edges,labels):('a,'b)BDD)  n n' = 
(n≠n' ∧ ALOOKUP edges n = ALOOKUP edges n' ∧
 ALOOKUP labels n = ALOOKUP labels n' ∧ ALOOKUP labels n'  ≠ NONE )
End


        
Definition merge_edges_def:
  merge_edges (edges:edges) n n' =
   MAP (\(a,b,c). ( a, if (b=n' ∧ c=n') then (n,n)
                 else if (b=n') then (n,c)
                 else if (c=n') then (b,n)
                     else (b,c))) edges 
End



Definition merge_def:
  merge ((r,edges,labels):('a,'b)BDD) n n' =
  let edges' = merge_edges (edges:edges) n n' in
    let edges'' = ADELKEY n' edges' in
      let labels' = ADELKEY n' labels in
          (r,edges'',labels')
End






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
    mergable  (r,edges,labels) n n' ∧
    n'' ≠ n' ∧
    ALOOKUP (merge_edges edges n n') n'' = SOME (nr,nl) ⇒
    (nr ≠ n' ∧ nl ≠ n')
Proof   
  rpt strip_tac >>
  gvs[mergable_def] >>
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

        
(*
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
gvs[Once merge_edges_list_cons] >>
fs[ALOOKUP_APPEND] >>
Cases_on ‘ALOOKUP (merge_edges [h] n n') n’ >> gvs[] >|[
    PairCases_on ‘h’ >>
    imp_res_tac merge_Theorem1 >>
    rgs[Once ALOOKUP_def] >>
    metis_tac[]
    ,
    metis_tac[merge_replaces_stays_same_singular]
  ]
)
                                                       
QED
*)


(* very low proof, check why*)       
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
  ∀ x vars_consumed  r edges labels n n' n'' nl nr pred mv b rec.
    consumed_dom_bdd vars_consumed (r,edges,labels) ∧ 
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
            
            assume_tac  mergable_correct_leaf >> 
            last_x_assum (strip_assume_tac o (Q.SPECL [‘labels’,‘nr’,‘r’, ‘edges’, ‘n'’,
                                                       ‘n’, ‘mv’, ‘b’])) >>
            
            ‘n'≠nr’ by metis_tac[merge_edges_res] >>
            gvs[]
               
            ,
            
            Cases_on ‘x'’ >> gvs[] >>
            
            subgoal ‘∃pred x'. ALOOKUP labels nr = SOME (non_termn (SOME x',pred))’ >-
             (
             ‘MEM nr (dom_range_edges edges)’ by imp_res_tac lookup_edges_in_domain >>
             imp_res_tac WF_imp_non_leaf_lbl >> gvs[]
             ) >>
            
            gvs[] >>
            
            
            subgoal ‘THE (INDEX_OF x' vars_consumed) < THE (INDEX_OF x vars_consumed)’ >-(
              rgs[Once BDD_ordered_def] >>
              first_x_assum (strip_assume_tac o (Q.SPECL [‘n''’,‘nr’,‘nl’])) >>
              gvs[order_hold_def] >>
                                  
              gvs[consumed_dom_bdd_def] >>
              res_tac >>
              imp_res_tac MEM_INDEX_OF >>   
                                  
              last_x_assum (strip_assume_tac o (Q.SPECL [‘i'’, ‘i’])) >>
              gvs[]  
              ) >>

            gvs[] >>
            first_x_assum (strip_assume_tac o (Q.SPECL [‘INDEX_OF (x':string) (vars_consumed: string list)’])) >>
            gvs[] >>
                  
            first_x_assum (strip_assume_tac o (Q.SPECL [‘x'’, ‘vars_consumed’])) >>
            gvs[] >>

          
            first_x_assum (strip_assume_tac o (Q.SPECL [‘r’, ‘edges’, ‘labels’, ‘n’, ‘n'’, ‘nr’, ‘r'’, ‘q’,  ‘pred'’, ‘mv’, ‘b’])) >>
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
                      Cases_on ‘ALOOKUP mv x'’ >> gvs[] >|[
                          cheat
                          ,
                          Cases_on ‘x''’ >> gvs[] >|[
                              (* true *)
                              ‘n' ≠ n'' ∧ nl ≠ n''’ by (imp_res_tac lookup_edges_not_parent >> gvs[]) >>
                              
                              qpat_x_assum ‘SOME ($var$(x'0'),x'1'') = ALOOKUP edges n'’ (fn thm => assume_tac (SIMP_RULE (srw_ss()) [Once EQ_SYM_EQ] thm)) >>
                              ‘n' ≠ $var$(x'0') ∧ n' ≠ x'1''’ by (imp_res_tac lookup_edges_not_parent >> gvs[]) >>
                              
                              (* we need to show that x'0 = $var$(x'0') *)    
                              ‘ALOOKUP edges n = SOME ($var$(x'0'),x'1'')’ by gvs[] >>    
                              ‘n ≠ $var$(x'0') ∧ n ≠ x'1''’ by (imp_res_tac lookup_edges_not_parent >> gvs[]) >>   
                              ‘x'0 = $var$(x'0')’ by imp_res_tac merge_replaces_stays_same >>
                              rgs[] >>
                              simp[Once EQ_SYM_EQ, Once BDD_sem_cases] >>
                              
                              
                              subgoal ‘THE (INDEX_OF x' vars_consumed) < THE (INDEX_OF x vars_consumed)’ >-
                               (
                               rgs[Once BDD_ordered_def] >>
                               first_x_assum (strip_assume_tac o (Q.SPECL [‘n''’,‘n'’,‘nl’])) >>
                               gvs[order_hold_def] >>
                               
                               gvs[consumed_dom_bdd_def] >>
                               res_tac >>
                               imp_res_tac MEM_INDEX_OF >>   
                               
                               first_x_assum (strip_assume_tac o (Q.SPECL [‘i’, ‘i'’])) >>
                               gvs[]  
                              
                               ) >>
                               
                              gvs[] >>
                              first_x_assum (strip_assume_tac o (Q.SPECL [‘INDEX_OF (x':string) (vars_consumed: string list)’])) >>
                              gvs[] >>
                              first_x_assum (strip_assume_tac o (Q.SPECL [‘x'’, ‘vars_consumed’])) >>
                              gvs[] >>
                              first_x_assum (strip_assume_tac o (Q.SPECL [‘r’, ‘edges’, ‘labels’, ‘n’, ‘n'’, ‘n’, ‘x'1''’, ‘x'0’,  ‘r'’, ‘mv’, ‘b’])) >>
                              rgs[] >>
                              
                              gvs[Once BDD_sem_cases] >>
                              simp[Once BDD_sem_cases] >> gvs[ALOOKUP_ADELKEY]
                              ,
                              cheat
                              
                              
                            ]
                        ]
                    ] 
                ]
            ]
                                                                   
                                                                   
        ]
        ,
        cheat
        
      ]
  ]
QED


 


          





             
             
Theorem Lemma3:
  ∀ labels vars_consumed n'' r edges n' n mv b rec.
    consumed_dom_bdd vars_consumed (r,edges,labels) ∧
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



                                                              
        
Theorem merge_correct:        
  ∀ r edges labels vars_consumed n n' rec .
    correct_sem rec (r,edges,labels) ∧
    BDD_WF (r,edges,labels) ∧
    consumed_dom_bdd vars_consumed (r,edges,labels) ∧
    BDD_ordered (r,edges,labels) vars_consumed ∧           
    mergable (r,edges,labels) n n'
    ==>
    correct_sem rec (merge (r,edges,labels) n n')
Proof
  rpt strip_tac >>   
  simp[Once correct_sem_def] >>
  rpt strip_tac >>
  gvs[merge_def] >>

  Cases_on ‘n' = n''’ >> gvs[] >|[

    
    ‘get_prop (ADELKEY n' labels) n' = NONE’ by cheat >> 
    gvs[op_sem_def, get_prop_def] >>
      gvs[AllCaseEqs()]>>

    ‘BDD_sem rec
     (r,ADELKEY n' (merge_edges edges n n'),ADELKEY n' labels) mv n' (NONE)’ by cheat >>
    imp_res_tac BDD_sem_determ
    ,
    
    assume_tac Lemma3 >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘labels’, ‘vars_consumed’, ‘n''’, ‘r’, ‘edges’, ‘n'’, ‘n’, ‘mv’, ‘b’, ‘rec’])) >>
    gvs[] >>


    ‘mv_dom_bdd mv (r,edges,labels)’ by cheat >>
    gvs[correct_sem_def] >>
    res_tac >>
    
    gvs[get_prop_def]>> 
    gvs[Once BDD_sem_cases]>>
    
    gvs[ALOOKUP_ADELKEY] >>
    rgs[op_sem_def] >>
    gvs[AllCaseEqs()]>>
    cheat

  ]
QED
 




    

        



   
(*******************************************************)
(*                                                     *)
(*                  E L I M I N A T E                  *)
(*                                                     *)
(*******************************************************)

Definition eleminatble_def:        
eleminatble ((r,edges,labels):('a,'b)BDD)  n n' = 
(n≠n' ∧ ALOOKUP edges n' = SOME (n,n) )
End


(*******************************************************)
(*    Definition of eliminate is the same as  merge    *)
(*******************************************************)

(*         
Definition eliminate_edges_def:
  eliminate_edges (edges:edges) n n' =
   MAP (\(a,b,c). ( a, if (b=n' ∧ c=n') then (n,n)
                 else if (b=n') then (n,c)
                 else if (c=n') then (b,n)
                     else (b,c))) edges 
End



Definition eliminate_def:
  eliminate ((r,edges,labels):BDD) n n' =
  let edges' = merge_edges (edges:edges) n n' in
    let edges'' = ADELKEY n' edges' in
      let labels' = ADELKEY n' labels in
          (r,edges'',labels')
End



       
EVAL “eleminatble (1,[(0,1,5);(1,2,2);(2,3,4)],[]) 2 1”
EVAL “eliminate_edges [(0,1,5);(1,2,2);(2,3,4)] 2 1”
EVAL “eliminate (1,[(0,1,5);(1,2,2);(2,3,4)],[]) 2 1”


mergable_def     
EVAL “mergable (0,[(0,1,5);(1,2,2);(5,2,2)],[(1,x);(5,x)]) 1 5”
EVAL “merge_edges [(0,1,5);(1,2,2);(5,2,2)] 1 5”

EVAL “eleminatble (0,[(0,1,5);(1,2,2);(5,2,2)],[(1,x);(5,x)]) 2 1”
EVAL “eliminate_edges [(0,1,5);(1,2,2);(5,2,2)] 2 1”
EVAL “eliminate (0,[(0,1,5);(1,2,2);(5,2,2)],[(1,x);(5,x)]) 2 1”


EVAL “eleminatble (0,[(1,2,2)],[(1,x);(5,x)]) 2 1”
EVAL “eliminate_edges [(1,2,2)] 2 1”
EVAL “eliminate (0,[(1,2,2)],[(1,x);(5,x)]) 2 1”


EVAL “eleminatble (0,[(1,2,2);(2,3,4)],[(1,x);(5,x)]) 2 1”
EVAL “eliminate_edges [(1,2,2);(2,3,4)] 2 1”
EVAL “eliminate (0,[(1,2,2);(2,3,4)],[(1,x);(5,x)]) 2 1”



EVAL “eleminatble (0,[(1,2,2)],[(1,x);(5,x)]) 2 1”
EVAL “eliminate_edges [(1,2,2)] 2 1”
EVAL “eliminate (0,[(1,2,2)],[(1,x);(5,x)]) 2 1”

     
*)


 


        

val _ = export_theory ();
