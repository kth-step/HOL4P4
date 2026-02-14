open HolKernel boolLib simpLib Parse bossLib;

open listTheory;
open alistTheory;
open rich_listTheory;

open p4_auxTheory;
open bdd_auxTheory;     
open bdd_genTheory;  
open bdd_gen_wfTheory;   
open bdd_gen_orderTheory;

     
val _ = new_theory "bdd_gen_correct";



(* TODO: figure out how to put all of those in one file *)
    
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



val imp_res_tac_body = 
(imp_res_tac mk_body_map1 >>
 imp_res_tac mk_body_map2 >>
 imp_res_tac mk_body_map3 >>
 imp_res_tac mk_body_map4 >>
 imp_res_tac mk_body_map5 >>
 imp_res_tac mk_body_map6);




val imp_res_tac_distinct = 
(imp_res_tac all_distinct_leaves >>
 imp_res_tac all_distinct_leaves_labels >>
 imp_res_tac all_distinct_ntl >>
 imp_res_tac all_distinct_sub >>
 imp_res_tac all_distinct_simp >>
 imp_res_tac all_distinct_determine >>
 imp_res_tac all_distinct_mk_edges >>
 imp_res_tac all_distinct_non_term_leaf_updt >>
 imp_res_tac all_distinct_mk_labels
);





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




Definition node_in_BDD_def:
  node_in_BDD n ((r,edges,labels):('a,'b)BDD) =
     MEM n (dom_range_edges edges)
End


Theorem consumed_dom_bdd_in_mv:        
  ∀ vars_consumed vars mv r edges labels n x p.
    consumed_dom_bdd vars_consumed (r,edges,labels) ∧
    mv_dom_vars mv (vars ++ vars_consumed) ∧
    ALOOKUP labels n = SOME (non_termn (SOME x,p)) ⇒
    ∃b . ALOOKUP mv x = SOME b
Proof
  rpt strip_tac >>
  gvs[consumed_dom_bdd_def] >>
  res_tac >>
  gvs[mv_dom_vars_def, lookup_is_some_def] >>
  res_tac
QED


Theorem fv_mv_tracking_single:
  ∀ mv vars rec p mv.        
    mv_dom_vars mv vars ∧
    fv_in_vars rec p vars ⇒
    fv_in_p rec p mv
Proof
  rpt strip_tac >>
  gvs[fv_in_p_def, fv_in_vars_def, mv_dom_vars_def, lookup_is_some_def] >>
  rpt strip_tac >>
  res_tac
QED

            
        
(* Labels index of parent and child are ordered in the consumed list *)
Theorem ordered_for_two_labels:
  ∀ r edges labels n n' n'' vars_consumed x x' x'' n'' p p' p''.
    ALOOKUP edges n = SOME (n',n'') ∧
    consumed_dom_bdd vars_consumed (r,edges,labels) ∧        
    BDD_ordered (r,edges,labels) vars_consumed ∧
    ALOOKUP labels n = SOME (non_termn (SOME x,p)) ⇒
    ((ALOOKUP labels n' = SOME (non_termn (SOME x',p')) ⇒
      THE (INDEX_OF x' vars_consumed) < THE (INDEX_OF x vars_consumed))
     ∧
     (ALOOKUP labels n'' = SOME (non_termn (SOME x'',p'')) ⇒
      THE (INDEX_OF x'' vars_consumed) < THE (INDEX_OF x vars_consumed)))
Proof
  rpt strip_tac >>
  rgs[Once BDD_ordered_def]>>
  first_x_assum (strip_assume_tac o (Q.SPECL [‘n’,‘n'’, ‘n''’])) >| [
    ‘MEM x' vars_consumed ∧ MEM x vars_consumed’ by (rgs[Once consumed_dom_bdd_def] >> res_tac >> fs[]) >>
    ‘∃i. INDEX_OF x vars_consumed = SOME i’ by (imp_res_tac MEM_INDEX_OF >> gvs[] )>>
    ‘∃i'. INDEX_OF x' vars_consumed = SOME i'’ by (imp_res_tac MEM_INDEX_OF >> gvs[]) >>
    gvs[order_hold_def] 
    ,
    ‘MEM x'' vars_consumed ∧ MEM x vars_consumed’ by (rgs[Once consumed_dom_bdd_def] >> res_tac >> fs[]) >>
    ‘∃i. INDEX_OF x vars_consumed = SOME i’ by (imp_res_tac MEM_INDEX_OF >> gvs[] )>>
    ‘∃i''. INDEX_OF x'' vars_consumed = SOME i''’ by (imp_res_tac MEM_INDEX_OF >> gvs[]) >>
    gvs[order_hold_def] 
  ]                                                                 
QED



(* The semantics are deterministic *)
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


    
Theorem BDD_sem_not_eq:
  ∀ n r edges labels mv b rec n' n'' x p b'.
    ALOOKUP edges n = SOME (n',n'') ∧
    ALOOKUP labels n = SOME (non_termn (SOME x,p)) ∧
    ALOOKUP mv x = SOME T ∧
    BDD_sem rec (r,edges,labels) mv n b ∧
    ~ BDD_sem rec (r,edges,labels) mv n b' ⇒
    b' ≠ b
Proof
 Induct_on ‘BDD_sem’ >>        
 rpt strip_tac >>
 rgs[Once BDD_sem_cases] >>
 gvs[] >>

 rgs[Once BDD_sem_cases] >>
 gvs[] 
QED




                                
(* in the intermidiate layer, there exsists a final answer *)
Theorem BDD_sem_exsists_inter:
  ∀ vars_consumed x' r edges labels mv n n' n'' p b rec vars.            
    BDD_ordered (r,edges,labels) vars_consumed ∧
    mv_dom_vars mv (vars++vars_consumed) ∧
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

      ‘∃b . ALOOKUP mv x'' = SOME b’ by (imp_res_tac consumed_dom_bdd_in_mv >> metis_tac[]) >>
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
        
        ‘∃b . ALOOKUP mv x'' = SOME b’ by (imp_res_tac consumed_dom_bdd_in_mv >> metis_tac[]) >>
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



(* exsists indeed an answer to the semantics *)       
Theorem BDD_sem_exsists:
  ∀ BDD mv n vars_consumed vars rec.
    BDD_ordered BDD vars_consumed ∧
    mv_dom_vars mv (vars ++ vars_consumed)  ∧
    consumed_dom_bdd vars_consumed BDD ∧
    node_in_BDD n BDD ∧  
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
    imp_res_tac consumed_dom_bdd_in_mv >> metis_tac[]
     ) >>

    metis_tac [BDD_sem_exsists_inter]
  ]
QED



Theorem inner_edges_are_same_exists:
  ∀ r edges labels r' edges' labels' h c c' n n' n'' rec.
    BDD_WF (r',edges',labels') ∧
    body_of_mk rec (r,edges,labels) h c = SOME ((r',edges',labels'),c') ∧
    ALOOKUP edges n = SOME (n',n'') ⇒
    (∃ n1 n2. ALOOKUP edges' n = SOME (n1,n2) ∧ (n'=n1 ∧ n''=n2))
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



Theorem ntls_labels_and_prop_comp:
  ∀ r edges labels r' edges' labels' h c c' n x p p' rec.
    BDD_WF (r',edges',labels') ∧
    body_of_mk rec (r,edges,labels) h c = SOME ((r',edges',labels'),c') ∧
    ALOOKUP labels n = SOME (non_termn (NONE,p)) ∧
    ALOOKUP labels' n = SOME (non_termn (SOME x,p'))⇒
    (x=h ∧ p=p')
Proof
  rpt strip_tac >>
  gvs[body_of_mk_def] >>
  gvs[AllCaseEqs()]>>
  body_of_mk_pred_tac >>
  (                 
  Cases_on ‘ALOOKUP (non_term_leaf_updt labels h) n’ >> rgs[] >|[ 
      imp_res_tac lookup_ntl_updt_none >>
      rgs[]
      ,
      imp_res_tac lookup_labels_in_updt_none >>
      first_x_assum (strip_assume_tac o (Q.SPECL [‘h’])) >>
      rgs[ALOOKUP_APPEND] >>
    rgs[]
    ]
  )
QED




Theorem fv_in_labels_preserved:
  ∀ r edges labels r' edges' labels' h c c' vars rec.
    fv_in_labels rec labels' vars ∧
    BDD_WF (r',edges',labels') ∧
    body_of_mk rec (r,edges,labels) h c = SOME ((r',edges',labels'),c') ⇒
    fv_in_labels rec labels vars
Proof                       
  rpt strip_tac >>
  rgs[fv_in_labels_def] >>
  rpt strip_tac >>
  
  gvs[body_of_mk_def] >>
  gvs[AllCaseEqs()]>>
  body_of_mk_pred_tac >>
  
  Cases_on ‘ALOOKUP (non_term_leaf_updt labels h) n’ >-
   (imp_res_tac lookup_ntl_updt_none >> gvs[]) >>
  
  Cases_on ‘opx’ >>
  
  imp_res_tac lookup_labels_in_updt >>
  imp_res_tac lookup_labels_in_updt_none >>
  first_x_assum (strip_assume_tac o (Q.SPECL [‘h’])) >|[
    
    subgoal ‘ALOOKUP (non_term_leaf_updt labels h ⧺ new_labels) n = SOME (non_termn (SOME h,p))’ >-
     (
     rgs[BDD_WF_def] >>
     rgs[ALOOKUP_APPEND, ALL_DISTINCT_APPEND] 
     ) >> res_tac
          
    ,
    subgoal ‘ALOOKUP (non_term_leaf_updt labels h ⧺ new_labels) n = SOME (non_termn (SOME x',p))’ >-
     (
     rgs[BDD_WF_def] >>
     rgs[ALOOKUP_APPEND, ALL_DISTINCT_APPEND] 
     ) >> res_tac
  ]
QED                                                           




(* we do not need this theorem, it is useless now
Theorem mv_dom_bdd_preserved:
  ∀ r edges labels r' edges' labels' h c c' mv rec vars.
    mv_dom_vars mv vars ∧
    BDD_WF (r',edges',labels') ∧
    body_of_mk rec (r,edges,labels) h c = SOME ((r',edges',labels'),c') ⇒
    mv_dom_vars mv vars
Proof                 
                 
  rpt strip_tac >>
  rgs[mv_dom_vars_def] >>
  rpt strip_tac >>
  
  gvs[body_of_mk_def] >>
  gvs[AllCaseEqs()]>>
  body_of_mk_pred_tac >>
           
  Cases_on ‘ALOOKUP (non_term_leaf_updt labels h) n’ >-
   (imp_res_tac lookup_ntl_updt_none >> gvs[]) >>
    
  imp_res_tac lookup_labels_in_updt >>
  first_x_assum (strip_assume_tac o (Q.SPECL [‘h’])) >>
    
    subgoal ‘ALOOKUP (non_term_leaf_updt labels h ⧺ new_labels) n = SOME (non_termn (SOME x,p))’ >-
     (
     rgs[BDD_WF_def] >>
     rgs[ALOOKUP_APPEND, ALL_DISTINCT_APPEND] 
     ) >> res_tac
QED                   
*)


(* when making a new body, the new edges in the new layer indeed has no children *)        
Theorem mk_body_new_edges_none:
  ∀r edges labels r' edges' labels' h c c' n n' n'' rec.
    BDD_WF (r',edges',labels') ∧
    BDD_WF (r,edges,labels) ∧
    body_of_mk rec (r,edges,labels) h c = SOME ((r',edges',labels'),c') ∧
    ALOOKUP edges' n = SOME (n',n'') ∧
    ALOOKUP edges n = NONE ⇒
    (ALOOKUP edges' n' = NONE ∧ ALOOKUP edges' n'' = NONE)
Proof
  rpt strip_tac >>
  gvs[body_of_mk_def] >>
  gvs[AllCaseEqs()]>>
  body_of_mk_pred_tac >>
  
  
  ‘ALOOKUP new_edges n = SOME (n',n'')’ by gvs[ALOOKUP_APPEND] >>
  
  ‘MEM n (dom_range_edges (edges ++ new_edges))’ by gvs[lookup_edges_in_domain] >>
  
  ‘ ∃x p. ALOOKUP (non_term_leaf_updt labels h ⧺ new_labels) n =
          SOME (non_termn (SOME x,p))’ by
    (imp_res_tac WF_imp_non_leaf_lbl_abs >>
     gvs[lookup_is_some_def] >>
     metis_tac[]) >>
  
  simp[ALOOKUP_APPEND] >>
  simp[AllCaseEqs()]  >|[
    (* for n' *)
    ‘MEM n' (MAP FST new_labels)’ by imp_res_tac in_range_of_new_edges_in_dom_new_labels >>
    ‘MEM n' (dom_range_edges (new_edges))’ by imp_res_tac lookup_edges_in_domain >>
    ‘MEM n' (dom_range_edges (edges ++ new_edges))’ by gvs[dom_range_edges_in_append] >>
    Cases_on ‘ALOOKUP (edges ⧺ new_edges) n'’ >|[
      rgs[ALOOKUP_APPEND] >>
      rgs[AllCaseEqs()]
      ,
      PairCases_on ‘x'’ >>
      rename1 ‘ALOOKUP (edges ⧺ new_edges) n' = SOME (n1',n2')’ >>
      subgoal ‘is_lookup_internal (non_term_leaf_updt labels h ⧺ new_labels) n'’ >-
       (
       imp_res_tac WF_imp_non_leaf_lbl_abs >>
       rgs[lookup_is_some_def, is_lookup_internal_def]
       ) >>
      
      rgs[is_lookup_internal_def] >>
      res_tac >>
      
      qpat_x_assum ‘ALOOKUP (non_term_leaf_updt labels h ⧺ new_labels) n' =
                    SOME (non_termn (SOME x',p'))’ (fn thm => assume_tac (SIMP_RULE (srw_ss()) [ALOOKUP_APPEND] thm)) >>
      rgs[AllCaseEqs()] >|[
          ‘ALL_DISTINCT (MAP FST simp_leaves')’ by (rgs[BDD_WF_def] >> imp_res_tac_distinct) >>
          imp_res_tac new_labels_are_not_internal 
          ,
          rgs[BDD_WF_def] >>
          rgs[ALL_DISTINCT_APPEND] >>
          imp_res_tac ALOOKUP_MEM >>
          imp_res_tac mem_fst_snd >>
          gvs[]
        ]
    ]
                                                
    ,
    (* for n'' *)
    ‘MEM n'' (MAP FST new_labels)’ by imp_res_tac in_range_of_new_edges_in_dom_new_labels >>
    ‘MEM n'' (dom_range_edges (new_edges))’ by imp_res_tac lookup_edges_in_domain >>
    ‘MEM n'' (dom_range_edges (edges ++ new_edges))’ by gvs[dom_range_edges_in_append] >>
    Cases_on ‘ALOOKUP (edges ⧺ new_edges) n''’ >|[
        rgs[ALOOKUP_APPEND] >>
        rgs[AllCaseEqs()]
        ,
        PairCases_on ‘x'’ >>
        rename1 ‘ALOOKUP (edges ⧺ new_edges) n'' = SOME (n1',n2')’ >>
        subgoal ‘is_lookup_internal (non_term_leaf_updt labels h ⧺ new_labels) n''’ >-
         (
         imp_res_tac WF_imp_non_leaf_lbl_abs >>
         rgs[lookup_is_some_def, is_lookup_internal_def]
         ) >>
        
        rgs[is_lookup_internal_def] >>
        res_tac >>
        
        qpat_x_assum ‘ALOOKUP (non_term_leaf_updt labels h ⧺ new_labels) n'' =
                      SOME (non_termn (SOME x',p'))’
                     (fn thm => assume_tac (SIMP_RULE (srw_ss()) [ALOOKUP_APPEND] thm)) >>
        rgs[AllCaseEqs()] >|[
            ‘ALL_DISTINCT (MAP FST simp_leaves')’ by (rgs[BDD_WF_def] >> imp_res_tac_distinct) >>
            imp_res_tac new_labels_are_not_internal 
            ,
            rgs[BDD_WF_def] >>
            rgs[ALL_DISTINCT_APPEND] >>
            imp_res_tac ALOOKUP_MEM >>
            imp_res_tac mem_fst_snd >>
            gvs[]
          ]
      ]                                       
  ]
QED



(* when edges are empty, then root makes a correct BDD *)        
Theorem edges_empty_correct_ntl:
  ∀r edges labels r' edges' labels' mv n n' n'' x p c c' p' h rec vars mv.
    prop1 rec ∧
    prop2 rec ∧
    range_c c ((r,edges,labels):('a,'b) BDD) ∧
    BDD_WF (r,edges,labels) ∧
    body_of_mk rec (r,edges,labels) h c = SOME ((r',edges',labels'),c') ∧
    ALOOKUP edges' n = SOME (n',n'') ∧
    ALOOKUP labels' n = SOME (non_termn (SOME x,p)) ∧
    fv_in_labels rec labels vars ∧
    mv_dom_vars mv vars ∧
    edges = [] ⇒
    ((ALOOKUP mv x = SOME T ∧
      ALOOKUP labels' n' = SOME p' ⇒
      (from_formula_to_action rec p' mv = op_sem rec (SOME p) mv))
     ∧
     (ALOOKUP mv x = SOME F ∧
      ALOOKUP labels' n'' = SOME p' ⇒
      (from_formula_to_action rec p' mv = op_sem rec (SOME p) mv)))
Proof
  
  rpt strip_tac >>
  ‘∃ p' . labels = [(r,p')]’ by gvs[BDD_WF_def] >>
  gvs[] >>
  
  rgs[body_of_mk_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> rgs[]) >>
  
  rename1 ‘getLeaves [] r' = SOME leaves’ >>
  rename1 ‘getLabels [(r',p'')] leaves = SOME leaves_labels’ >>
  rename1 ‘extract_nontermn leaves_labels = SOME ntl’ >>
  
  ‘∃ leaves_sub . leaves_pred_sub rec ntl h = leaves_sub’ by gvs[] >>
  ‘∃ simp_leaves . simp_pred_list rec leaves_sub = simp_leaves’ by gvs[] >>
  ‘∃ simp_leaves' . determine_termn_list rec simp_leaves = simp_leaves'’ by gvs[] >>
  ‘∃ new_edges . mk_new_edges simp_leaves' c = new_edges’ by gvs[] >>
  ‘∃ new_labels . mk_new_labels simp_leaves' c = new_labels’ by gvs[] >>
  rgs[] >>
  
  Cases_on ‘leaves’ >> rgs[getLeaves_def, getLabels_def] >>
  Cases_on ‘leaves_labels’ >> rgs[] >> PairCases_on ‘h''’ >> rgs[extract_nontermn_def] >>
  Cases_on ‘h''1’ >> rgs[]  >>
  
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[leaves_pred_sub_def]) >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[simp_pred_list_def, mk_new_labels_def]) >>
  rgs[simp_pred_list_def] >>
  rgs[leaves_pred_sub_def, determine_termn_def, simp_pred_list_def,
      determine_termn_list_def, mk_new_edges_def, mk_new_labels_def, non_term_leaf_updt_def,
      from_formula_to_action_def, op_sem_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[fv_in_labels_def]) >>
  
  gvs[BDD_WF_def, range_c_def, dom_range_edges_def] >>
  
  imp_res_tac fv_mv_tracking_single >>

  gvs[prop2_def] >>
  res_tac >>
  gvs[prop1_def] >>
  res_tac >>
  gvs[]
QED

    

Theorem leaves_pred_sub_alookup_some:
  ∀ ntl leaves_sub rec p h n.          
    ALOOKUP ntl n = SOME p ∧
    leaves_pred_sub rec ntl h = leaves_sub ⇒
    ALOOKUP leaves_sub n = SOME (h, rec.sub p h T, rec.sub p h F) 
Proof
  Induct >>
  rpt strip_tac >>
  imp_res_tac mk_body_map2 >>
  gvs[leaves_pred_sub_def] >>
  PairCases_on ‘h’ >> 
  rgs[AllCaseEqs()] 
QED
                                       


Theorem simp_pred_list_alookup_some:
  ∀ leaves_sub simp_leaves rec n h pt pf.
    ALOOKUP leaves_sub n = SOME (h,pt,pf) ∧
    simp_pred_list rec leaves_sub = simp_leaves ⇒
    ALOOKUP simp_leaves n = SOME (h, rec.simp pt, rec.simp pf) 
Proof
  Induct >>
  rpt strip_tac >>
  imp_res_tac mk_body_map3 >>
  gvs[simp_pred_list_def] >>
  PairCases_on ‘h’ >> 
  rgs[AllCaseEqs()] 
QED



Theorem determine_termn_list_alookup_some:
  ∀ simp_leaves simp_leaves' rec n h ptsimp pfsimp.
    ALOOKUP simp_leaves n = SOME (h,ptsimp,pfsimp) ∧ 
    determine_termn_list rec simp_leaves = simp_leaves' ⇒
    ALOOKUP simp_leaves' n = SOME (h, determine_termn rec ptsimp, determine_termn rec pfsimp) 
Proof
  Induct >>
  rpt strip_tac >>
  imp_res_tac mk_body_map4 >>
  gvs[determine_termn_list_def] >>
  PairCases_on ‘h’ >> 
  rgs[AllCaseEqs()] 
QED



Theorem lookup_new_edges_not_more_than_c:
  ∀ simp_leaves' c n n' n''.       
    ALOOKUP (mk_new_edges simp_leaves' c) n = SOME (n',n'') ⇒
    (n' >= c ∧ n'' >= c)
Proof
  Induct >>
  gvs[mk_new_edges_def] >>
  rpt strip_tac >>
  PairCases_on ‘h’ >>
  gvs[mk_new_edges_def] >>
  rgs[AllCaseEqs()]  >>
  res_tac >>
  gvs[]
QED




Theorem mk_new_labels_contains_prop:
  ∀ simp_leaves' new_edges new_labels ptsimp_det pfsimp_det n n' n'' h c.
    c > n ∧
    ALOOKUP new_edges n = SOME (n',n'') ∧
    ALOOKUP simp_leaves' n = SOME (h, ptsimp_det ,  pfsimp_det) ∧
    mk_new_edges simp_leaves' c = new_edges ∧
    mk_new_labels simp_leaves' c = new_labels ⇒
    (ALOOKUP new_labels n' = SOME ptsimp_det ∧
     ALOOKUP new_labels n'' = SOME pfsimp_det)     
Proof
  
  Induct >>
  rpt strip_tac >>
  imp_res_tac mk_body_map5 >-
   gvs[mk_new_edges_def, mk_new_labels_def, ALOOKUP_def] >-
   gvs[mk_new_edges_def, mk_new_labels_def, ALOOKUP_def] >>

  imp_res_tac all_distinct_mk_edges >>
  imp_res_tac all_distinct_mk_labels >>
  imp_res_tac in_range_of_new_edges_in_dom_new_labels >>
  
  PairCases_on ‘h’ >>
  rgs[AllCaseEqs()] >> 
  gvs[mk_new_edges_def, mk_new_labels_def] >>
  
  imp_res_tac lookup_new_edges_not_more_than_c >>
  gvs[] >>
  rgs[AllCaseEqs()] >> 
  res_tac >>
  gvs[]                          
QED


      
Theorem body_return_in_decision_str_conv:
  ∀ simp_leaves' leaves_sub ntl simp_leaves new_edges new_labels n n' n'' p p' p'' h c rec.
    c > n ∧
    ALOOKUP ntl n = SOME p ∧
    ALOOKUP new_edges n = SOME (n',n'') ∧
    leaves_pred_sub rec ntl h = leaves_sub ∧ 
    simp_pred_list rec leaves_sub = simp_leaves ∧
    determine_termn_list rec simp_leaves = simp_leaves' ∧
    mk_new_edges simp_leaves' c = new_edges ∧
    mk_new_labels simp_leaves' c = new_labels ⇒
    ((ALOOKUP new_labels n' = SOME p'
    ⇒
    ALOOKUP new_labels n' = SOME (determine_termn rec (rec.simp (rec.sub p h T))))
     ∧
     (ALOOKUP new_labels n'' = SOME p''
      ⇒
      ALOOKUP new_labels n'' = SOME (determine_termn rec (rec.simp (rec.sub p h F))))
    )       
Proof
  
  rpt strip_tac >>
  ‘ALOOKUP leaves_sub n = SOME (h,rec.sub p h T,rec.sub p h F)’ by imp_res_tac leaves_pred_sub_alookup_some >>
  imp_res_tac simp_pred_list_alookup_some >>
  ‘ALOOKUP simp_leaves' n =
   SOME
   (h,determine_termn rec (rec.simp (rec.sub p h T)),
    determine_termn rec (rec.simp (rec.sub p h F)))’ by imp_res_tac determine_termn_list_alookup_some >>
  
  imp_res_tac mk_new_labels_contains_prop 
QED



Theorem statements_structs_correctness_new_layer:
  ∀ simp_leaves' leaves_sub ntl simp_leaves new_edges new_labels n n' n'' p p' p'' h c mv  rec.     
    c > n ∧
    prop1 rec ∧
    prop2 rec ∧
    fv_in_p rec p mv ∧
    
    ALOOKUP ntl n = SOME p ∧
    ALOOKUP new_edges n = SOME (n',n'') ∧
    leaves_pred_sub rec ntl h = leaves_sub ∧ 
    simp_pred_list rec leaves_sub = simp_leaves ∧
    determine_termn_list rec simp_leaves = simp_leaves' ∧
    mk_new_edges simp_leaves' c = new_edges ∧
    mk_new_labels simp_leaves' c = new_labels ⇒
                  
    ((ALOOKUP mv h = SOME T ∧ ALOOKUP new_labels n' = SOME p' ⇒
      from_formula_to_action rec p' mv = op_sem rec (SOME p) mv)
     ∧
     (ALOOKUP mv h = SOME F ∧ ALOOKUP new_labels n'' = SOME p' ⇒
      from_formula_to_action rec p' mv = op_sem rec (SOME p) mv))
Proof
  
  rpt strip_tac >>
  assume_tac body_return_in_decision_str_conv >>
  first_x_assum (strip_assume_tac o (Q.SPECL [‘simp_leaves'’, ‘leaves_sub’, ‘ntl’, ‘simp_leaves’, ‘new_edges’, ‘new_labels’, ‘n’,
                                              ‘n'’, ‘n''’, ‘p’, ‘p'’, ‘p'’, ‘h’, ‘c’, ‘rec’])) >>
  rgs[] >>
  
  rgs[from_formula_to_action_def, op_sem_def] >>
  rgs[determine_termn_def] >>
  rgs[AllCaseEqs()]>>
  rgs[prop1_def] >>
  rgs[prop2_def] >>
  res_tac
QED




Theorem alookup_agrees_on_new_labels_after_update:
  ∀ r edges labels new_edges new_labels x n p.
    BDD_WF (r,edges ⧺ new_edges,non_term_leaf_updt labels x ⧺ new_labels) ∧
    ALOOKUP (non_term_leaf_updt labels x ⧺ new_labels) n = SOME p ∧
    MEM n (MAP FST new_labels) ⇒
    ALOOKUP new_labels n = SOME p
Proof
  rpt strip_tac >>
  ‘ALL_DISTINCT (MAP FST new_labels)’ by (rgs[BDD_WF_def, ALL_DISTINCT_APPEND]) >>
  ‘∃ elem. ALOOKUP new_labels n = SOME elem’ by (imp_res_tac distinct_mem_lookup_local >> gvs[]) >>
  ‘¬MEM n (MAP FST (non_term_leaf_updt labels x))’ by (rgs[BDD_WF_def] >> imp_res_tac all_distinct_mem_not) >>
  rgs[ALOOKUP_APPEND] >>
  Cases_on ‘ALOOKUP (non_term_leaf_updt labels x) n’ >> imp_res_tac ALOOKUP_MEM >> 
  imp_res_tac mem_fst_snd >>
  rgs[]
QED




Theorem now_internal_lbl_was_leaf_in_labels_verbose:
  ∀ r edges labels new_edges new_labels x h n p.
    BDD_WF (r,edges,labels) ∧
    ALOOKUP (non_term_leaf_updt labels h ⧺ new_labels) n = SOME (non_termn (SOME x,p)) ∧
    MEM n (dom_range_edges edges) ∧ ALOOKUP edges n = NONE ⇒
    (ALOOKUP labels n = SOME (non_termn (NONE,p))) ∧ h=x
Proof
  rpt strip_tac >>
  ‘∃ p_old. ALOOKUP labels n = SOME (non_termn (NONE,p_old))’ by
    (imp_res_tac now_internal_lbl_was_leaf_in_labels >> gvs[]) >>
  
  imp_res_tac lookup_labels_in_updt_none >>
  first_x_assum (strip_assume_tac o (Q.SPECL [‘h’])) >>     
  
  rgs[BDD_WF_def] >> rgs[ALL_DISTINCT_APPEND,ALOOKUP_APPEND]
QED


   

Theorem body_correctness_new_layer:       
  ∀ r edges labels r' edges' labels' mv n n' n'' x p c c' b vars h rec .
    prop1 rec ∧ prop2 rec ∧ 
          
    BDD_WF (r,edges,labels) ∧
           
    fv_in_BDD rec (r,edges,labels) vars ∧
    mv_dom_vars mv vars ∧
              
    range_c c (r,edges,labels) ∧
     
    body_of_mk rec (r,edges,labels) h c = SOME ((r',edges',labels'),c') ∧
    BDD_sem rec (r',edges',labels') mv n b ∧
    ALOOKUP edges' n = SOME (n',n'') ∧
    ALOOKUP labels' n = SOME (non_termn (SOME x,p)) ∧
    ALOOKUP edges n = NONE ⇒
    b = op_sem rec (SOME p) mv
Proof
  rpt strip_tac >>
  imp_res_tac WFness_range_c_inter >>
  ‘BDD_WF (r',edges',labels')’ by imp_res_tac WFness_translation_inter >>
  
  ‘ALOOKUP edges' n' = NONE’ by imp_res_tac mk_body_new_edges_none >>
  ‘ALOOKUP edges' n'' = NONE’ by imp_res_tac mk_body_new_edges_none >>
  
  Cases_on ‘MEM n (dom_range_edges edges)’ >|[
    (* if n is in range of edges, and became in domain of edges' ,
       then indeed it is a leaf, thus it has been through the body,
       which entails that that exact n is correct*)
    
    gvs[body_of_mk_def] >>
    gvs[AllCaseEqs()]>>
    body_of_mk_pred_tac >>
    
    (*n is in leaves, then indeed in leaves labels *)
    
    ‘ALL_DISTINCT (MAP FST edges) ’ by (rgs[BDD_WF_def] >> imp_res_tac_distinct) >>
    
    ‘MEM n leaves’ by imp_res_tac leaves_in_get_leaves >>
    
    ‘(ALOOKUP labels n = SOME (non_termn (NONE,p))) ∧ h=x’ by (imp_res_tac now_internal_lbl_was_leaf_in_labels_verbose >> gvs[]) >>
    rgs[] >>
    
    ‘ALOOKUP ntl n = SOME p’ by imp_res_tac leaves_in_ntl_lemma >>
    ‘ALL_DISTINCT (MAP FST labels)’ by (rgs[BDD_WF_def] >> imp_res_tac_distinct) >>
    ‘ALOOKUP leaves_labels n = SOME (non_termn (NONE,p))’ by imp_res_tac leaves_labels_same_in_labels_some >>
    ‘ALOOKUP new_edges n = SOME (n',n'')’ by gvs[ALOOKUP_APPEND] >>
    
    (* we also know that the new label for the new leafs are in new_labels*)
    
    subgoal ‘fv_in_p rec p mv’ >-
     (rgs[fv_in_BDD_def, fv_in_labels_def] >> res_tac >>  imp_res_tac fv_mv_tracking_single) >>
    
    subgoal ‘c > n’ >- (
    rgs[range_c_def, EVERY_MEM] >>
    imp_res_tac ALOOKUP_MEM >>
    imp_res_tac mem_fst_snd >>
    rgs[]
    ) >>
    
    rgs[Once BDD_sem_cases] >>
    rgs[Once BDD_sem_cases] >|[
      
      ‘MEM n' (MAP FST new_labels)’ by imp_res_tac in_range_of_new_edges_in_dom_new_labels >>
      ‘ALOOKUP new_labels n' = SOME p'’ by imp_res_tac alookup_agrees_on_new_labels_after_update >>
      
      assume_tac statements_structs_correctness_new_layer >>
      first_x_assum (strip_assume_tac o (Q.SPECL [‘simp_leaves'’, ‘leaves_sub’, ‘ntl’, ‘simp_leaves’, ‘new_edges’,
                                                  ‘new_labels’, ‘n’, ‘n'’, ‘n''’, ‘p’, ‘p'’, ‘p''’,
                                                  ‘h’, ‘c’, ‘mv’, ‘rec’])) >> 
      rgs[]
      ,
      ‘MEM n'' (MAP FST new_labels)’ by imp_res_tac in_range_of_new_edges_in_dom_new_labels >>
      ‘ALOOKUP new_labels n'' = SOME p'’ by imp_res_tac alookup_agrees_on_new_labels_after_update >>
      
      assume_tac statements_structs_correctness_new_layer >>
      first_x_assum (strip_assume_tac o (Q.SPECL [‘simp_leaves'’, ‘leaves_sub’, ‘ntl’, ‘simp_leaves’, ‘new_edges’,
                                                  ‘new_labels’, ‘n’, ‘n'’, ‘n''’, ‘p’, ‘p'’, ‘p''’,
                                                  ‘h’, ‘c’, ‘mv’, ‘rec’])) >> 
      rgs[]
    ]
                              
    ,
    (* if n is not in edges, it means either the edges are empty so we work with root,
       otherwise by contradiction*)

    rgs[Once BDD_sem_cases] >>
    rgs[Once BDD_sem_cases] >>  
    (Cases_on ‘edges = []’  >|[
        (* then we should prove the root*)                  
        assume_tac edges_empty_correct_ntl >>
        first_x_assum (strip_assume_tac o (Q.SPECL [‘r’, ‘edges’, ‘labels’, ‘r'’, ‘edges'’, ‘labels'’, ‘mv’, ‘n’, ‘n'’,
                                                    ‘n''’, ‘x’, ‘p’, ‘c’, ‘c'’, ‘p'’, ‘h’, ‘rec’, ‘vars’])) >>
        gvs[fv_in_BDD_def]
       
        ,
        gvs[body_of_mk_def] >>
        gvs[AllCaseEqs()]>>
        body_of_mk_pred_tac >>
        
        imp_res_tac get_leaves_in_nodes >>
        ‘ALOOKUP leaves_labels n = NONE’ by imp_res_tac not_in_leaves_not_in_res >>
        subgoal ‘ALOOKUP new_edges n = NONE’ >-
         (
         imp_res_tac_body >>
         rgs[ALOOKUP_NONE] >>
         imp_res_tac extract_nonterm_mem_neg >>
         gvs[]
         ) >>
        
        gvs[ALOOKUP_APPEND] >> gvs[]
      ])
  ]

QED



Theorem bdd_sem_imp_up:
  ∀ r edges labels n n' n'' x pred b' rec mv.
    ALOOKUP edges n = SOME (n',n'') ∧
    ALOOKUP labels n  = SOME (non_termn (SOME x ,pred)) ∧
    ALOOKUP mv x = SOME T ∧
    BDD_sem rec (r,edges,labels) mv n' b' ⇒
    BDD_sem rec (r,edges,labels) mv n b'
Proof
  rpt strip_tac >>
  simp[Once BDD_sem_cases]
QED


Theorem mk_now_internal_lbl_was_leaf_in_labels:
  ∀ r edges labels r' edges' labels' n x p h c c' rec.
    MEM n (dom_range_edges edges) ∧
    BDD_WF (r,edges,labels) ∧
    ALOOKUP edges n = NONE ∧
    ALOOKUP labels' n = SOME (non_termn (SOME x,p)) ∧
    body_of_mk rec (r,edges,labels) h c = SOME ((r',edges',labels'),c') ⇒
    ∃ p' . ALOOKUP labels n = SOME (non_termn (NONE,p'))
Proof                                               
  rpt strip_tac >>
  gvs[body_of_mk_def] >>
  gvs[AllCaseEqs()]>>
  body_of_mk_pred_tac >>
  imp_res_tac now_internal_lbl_was_leaf_in_labels >>
  gvs[]
QED



Theorem mk_terminal_leafs_in_old_new_labels:        
  ∀ r edges labels r' edges' labels' n x p h c c' rec.
    MEM n (dom_range_edges edges) ∧
    BDD_WF (r,edges,labels) ∧
    BDD_WF (r',edges',labels') ∧
    ALOOKUP edges n = NONE ∧
    ALOOKUP edges' n = NONE ∧      
    body_of_mk rec (r,edges,labels) h c = SOME ((r',edges',labels'),c') ⇒
    ∃ action p_action . ALOOKUP labels' n = SOME (termn(action,p_action)) ∧
                        ALOOKUP labels n = SOME (termn(action,p_action))
Proof
  rpt strip_tac >>
  gvs[body_of_mk_def] >>
  gvs[AllCaseEqs()]>>
  body_of_mk_pred_tac >>
  rgs[BDD_WF_def] >|[
                  
    rgs[is_lookup_ntl_def] >>
    rgs[ALL_DISTINCT_APPEND] >>
    imp_res_tac_body >>
    
    ‘MEM n leaves’ by metis_tac[leaves_in_get_leaves] >>
    ‘ALOOKUP ntl n = SOME p’ by metis_tac[leaves_in_ntl_lemma] >> rgs[] >>
    subgoal ‘∃ new_p . ALOOKUP new_edges n = SOME new_p’ >-
     ( metis_tac[alookup_map_local_thm]) >>
    
    rgs[ALOOKUP_APPEND] >>
    gvs[AllCaseEqs()]
    ,
        
    imp_res_tac lookup_labels_in_updt_term >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘h’])) >>
    ‘MEM n (dom_range_edges (edges ⧺ new_edges))’ by gvs[dom_range_edges_in_append] >>
    imp_res_tac ALOOKUP_MEM >>
    imp_res_tac mem_fst_snd >>
    rgs[] >>
    rgs[ALOOKUP_APPEND] >>
    gvs[AllCaseEqs()]
]
QED
        


Theorem terminals_eq_triviality:  
  ∀ r edges labels n action p_action p mv rec.
    ALOOKUP labels n = SOME (termn (action,p_action)) ∧
    ALOOKUP edges n = NONE ∧
    BDD_sem rec (r,edges,labels) mv n (rec.sem p mv) ∧
    BDD_sem rec (r,edges,labels) mv n (rec.sem p_action mv) ∧
    rec.sem p_action mv = rec.sem p mv ⇒
    SOME action = rec.sem p mv
Proof
  rpt strip_tac >>
  gvs[Once BDD_sem_cases] >>
  rgs[from_formula_to_action_def] >>
  gvs[AllCaseEqs()]>>
  Cases_on ‘from_formula_to_action rec (termn (action',v3)) mv’ >> gvs[]
QED




        
val parent_in_old_sem_correct_tac_l = (
            ‘MEM n' (dom_range_edges edges')’ by imp_res_tac lookup_edges_in_domain >>

          (*  ‘fv_in_labels rec labels mv’ by imp_res_tac fv_in_labels_preserved >> *)
          (*  ‘mv_dom_bdd mv (r,edges,labels)’ by imp_res_tac mv_dom_bdd_preserved >>  replace*)
            ‘node_in_BDD n (r,edges,labels)’ by rgs[node_in_BDD_def, lookup_edges_in_domain] >>
            ‘node_in_BDD n' (r,edges,labels)’ by rgs[node_in_BDD_def, lookup_edges_in_domain] >>
            
            gvs[] >>
                                           
            subgoal ‘∃b. BDD_sem rec (r,edges,labels) mv n b’ >-
             ( irule BDD_sem_exsists >> srw_tac [SatisfySimps.SATISFY_ss][]) >>
            
            subgoal ‘∃b. BDD_sem rec (r,edges,labels) mv n' b’ >- 
             ( irule BDD_sem_exsists >> srw_tac [SatisfySimps.SATISFY_ss][]) >>
            
            subgoal ‘ b = op_sem rec (get_prop labels n) mv’ >-
             ( gvs[correct_sem_def]) >>
            
            subgoal ‘ b' = op_sem rec (get_prop labels n') mv’ >-
             ( gvs[correct_sem_def]) >>
            
            rgs[get_prop_def, op_sem_def] >>
            
            qpat_x_assum ‘BDD_sem rec (r,edges,labels) mv n (rec.sem p mv)’
                         (fn thm => assume_tac (SIMP_RULE (srw_ss()) [Once BDD_sem_cases] thm)) >>
            
            rgs[] >>
            imp_res_tac BDD_sem_determ);




 

val parent_in_old_sem_correct_tac_r = (
            ‘MEM n'' (dom_range_edges edges')’ by imp_res_tac lookup_edges_in_domain >>

          (*  ‘fv_in_labels rec labels mv’ by imp_res_tac fv_in_labels_preserved >> *)
          (*  ‘mv_dom_bdd mv (r,edges,labels)’ by imp_res_tac mv_dom_bdd_preserved >>  replace*)
            ‘node_in_BDD n (r,edges,labels)’ by rgs[node_in_BDD_def, lookup_edges_in_domain] >>
            ‘node_in_BDD n'' (r,edges,labels)’ by rgs[node_in_BDD_def, lookup_edges_in_domain] >>
            
            gvs[] >>
                                           
            subgoal ‘∃b. BDD_sem rec (r,edges,labels) mv n b’ >-
             ( irule BDD_sem_exsists >> srw_tac [SatisfySimps.SATISFY_ss][]) >>
            
            subgoal ‘∃b. BDD_sem rec (r,edges,labels) mv n'' b’ >- 
             ( irule BDD_sem_exsists >> srw_tac [SatisfySimps.SATISFY_ss][]) >>
            
            subgoal ‘ b = op_sem rec (get_prop labels n) mv’ >-
             ( gvs[correct_sem_def]) >>
            
            subgoal ‘ b' = op_sem rec (get_prop labels n'') mv’ >-
             ( gvs[correct_sem_def]) >>
            
            rgs[get_prop_def, op_sem_def] >>
            
            qpat_x_assum ‘BDD_sem rec (r,edges,labels) mv n (rec.sem p mv)’
                         (fn thm => assume_tac (SIMP_RULE (srw_ss()) [Once BDD_sem_cases] thm)) >>
            
            rgs[] >>
            imp_res_tac BDD_sem_determ);



                         

(*** this is lemma 2 (modified) ***)
Theorem correct_sem_translation_inner_nodes:
  ∀ vars_consumed x r edges labels r' edges' labels' mv n n' n'' h c c' p b rec vars.
    prop1 rec ∧ prop2 rec ∧
          
    BDD_ordered ((r,edges,labels):('a,'b) BDD) (vars_consumed) ∧
    BDD_WF (r,edges,labels) ∧
    range_c c (r,edges,labels) ∧
           
    fv_in_BDD rec (r,edges,labels) (vars++[h]++vars_consumed) ∧
    mv_dom_vars mv (vars++[h]++vars_consumed) ∧
                
    consumed_dom_bdd (vars_consumed) (r,edges,labels) ∧                 
    correct_sem rec (r,edges,labels) (vars ⧺ [h] ⧺ vars_consumed) ∧ 
    body_of_mk rec (r,edges,labels) h c = SOME ((r',edges',labels'),c') ∧
               
    BDD_sem rec (r',edges',labels') mv n b ∧
    ALOOKUP edges' n = SOME (n',n'') ∧
    ALOOKUP labels' n = SOME (non_termn (SOME x,p)) ⇒
    b = op_sem rec (SOME p) mv
Proof
  ntac 2 strip_tac >>
  measureInduct_on `THE(INDEX_OF x vars_consumed)` >>
  rpt strip_tac >>
  
  imp_res_tac WFness_range_c_inter >>
  ‘BDD_WF (r',edges',labels')’ by imp_res_tac WFness_translation_inter >>
  
  ‘MEM n (dom_range_edges edges')’ by imp_res_tac lookup_edges_in_domain >>
  Cases_on ‘ALOOKUP edges n’ >> rgs[] >|[
    
    (* Case where n was a leaf in old edges and became a parent in new edges this needs the body *)
    imp_res_tac body_correctness_new_layer             
    ,
    
    (* Case where n was a parent in old edges, directly from IH and other things *)
    PairCases_on ‘x'’ >>
    rename1 ‘ALOOKUP edges n = SOME (n1',n2')’ >>
    ‘(n'=n1') ∧ (n''=n2')’ by (imp_res_tac inner_edges_are_same >> srw_tac[][]) >>
    
    ‘lookup_is_some edges n’ by gvs[lookup_is_some_def] >>
    ‘∃x p. ALOOKUP labels n = SOME (non_termn (SOME x,p))’ by (imp_res_tac WF_imp_non_leaf_lbl_abs >> metis_tac[]) >>
    ‘(x=x') ∧ (p=p')’ by (imp_res_tac inner_labels_are_same >> srw_tac[][]) >>
    
    
    ‘MEM n1' (dom_range_edges edges)’ by imp_res_tac lookup_edges_in_domain >>
    ‘MEM n2' (dom_range_edges edges)’ by imp_res_tac lookup_edges_in_domain >>
    ‘MEM n' (dom_range_edges edges')’ by imp_res_tac lookup_edges_in_domain >>

    gvs[op_sem_def] >>          
    rgs[Once BDD_sem_cases] >|[

        (***** True ******)

        (* according to semantics, this edge depends on the left and right child*)
        (*Case taking True; left child*)
        
        Cases_on ‘ALOOKUP edges n'’ >> rgs[] >|[
          (* the child n' is a leaf at the time in old edges, this represents
             internal nodes n' that are tl or ntl *)
          Cases_on ‘ALOOKUP edges' n'’ >> rgs[] >|[
            
            (* inner terminal leaf tl *)
            subgoal ‘∃ action p_action . ALOOKUP labels' n' = SOME (termn(action,p_action)) ∧
                                         ALOOKUP labels n' = SOME (termn(action,p_action))’ >-
             ( metis_tac[mk_terminal_leafs_in_old_new_labels] ) >>
            
            rgs[Once BDD_sem_cases] >>
                    
            rgs[] >>
            rgs[from_formula_to_action_def] >>
            
            parent_in_old_sem_correct_tac_l >>
            imp_res_tac terminals_eq_triviality
                                
            ,
            (* new layer wrt last layer in edges *)
            PairCases_on ‘x'’ >>
            rename1 ‘ALOOKUP edges' n' = SOME (n1',n2')’ >>
            
            ‘lookup_is_some edges' n'’ by gvs[lookup_is_some_def] >>
            ‘∃x p. ALOOKUP labels' n' = SOME (non_termn (SOME x,p))’ by
              (imp_res_tac WF_imp_non_leaf_lbl_abs >> metis_tac[]) >>

            ‘MEM n1' (dom_range_edges edges')’ by imp_res_tac lookup_edges_in_domain >>
            ‘MEM n2' (dom_range_edges edges')’ by imp_res_tac lookup_edges_in_domain >>
            
            assume_tac body_correctness_new_layer >>
            first_x_assum (strip_assume_tac o (Q.SPECL [‘r’, ‘edges’, ‘labels’, ‘r'’, ‘edges'’, ‘labels'’, ‘mv’,
                                                        ‘n'’, ‘n1'’, ‘n2'’, ‘x'’, ‘p'’, ‘c’, ‘c'’, ‘b’,
                                                        ‘vars ⧺ [h] ⧺ vars_consumed’, ‘h’, ‘rec’])) >>
            rgs[op_sem_def] >> gvs[] >>
            gvs[] >>
            
            subgoal ‘∃ p'' . ALOOKUP labels n' = SOME (non_termn (NONE,p''))’ >-
             ( metis_tac [mk_now_internal_lbl_was_leaf_in_labels]) >>
            ‘x' = h ∧ p'' = p'’ by ( metis_tac[ntls_labels_and_prop_comp] ) >>
            
            parent_in_old_sem_correct_tac_l 
          ]
                                                        
          ,
          (* inner layer, that stayed inner using IH *)
          PairCases_on ‘x'’ >>
          rename1 ‘ALOOKUP edges n' = SOME (n1',n2')’ >>
                  
          ‘lookup_is_some edges n'’ by gvs[lookup_is_some_def] >>
          ‘∃x p. ALOOKUP labels n' = SOME (non_termn (SOME x,p))’ by
            (imp_res_tac WF_imp_non_leaf_lbl_abs >> metis_tac[]) >>

          subgoal ‘THE (INDEX_OF x' vars_consumed) < THE (INDEX_OF x vars_consumed)’ >-
           (imp_res_tac ordered_for_two_labels) >>

          first_x_assum (strip_assume_tac o (Q.SPECL [‘INDEX_OF (x':string) (vars_consumed: string list)’])) >>
          rgs[PULL_FORALL] >>
          first_x_assum (strip_assume_tac o (Q.SPECL [‘x'’, ‘vars_consumed’, ‘r’, ‘edges’, ‘labels’,
                                                      ‘r'’, ‘edges'’, ‘labels'’, ‘mv’, ‘n'’,‘n1'’, ‘n2'’,
                                                      ‘h’, ‘c’, ‘c'’, ‘p'’, ‘b’, ‘rec’, ‘vars’])) >> gvs[] >>
          
          ‘ALOOKUP edges' n' = SOME (n1',n2')’ by
            (imp_res_tac inner_edges_are_same_exists >> gvs[]) >>
          ‘ALOOKUP labels' n' = SOME (non_termn (SOME x',p'))’ by
            (imp_res_tac inner_labels_are_same_exists >> gvs[]) >>
          gvs[] >>
          
          parent_in_old_sem_correct_tac_l
        ]
        ,
        (***** False ******)
         Cases_on ‘ALOOKUP edges n''’ >> rgs[] >|[
          (* the child n' is a leaf at the time in old edges, this represents
             internal nodes n' that are tl or ntl *)
          Cases_on ‘ALOOKUP edges' n''’ >> rgs[] >|[
            
            (* inner terminal leaf tl *)
            subgoal ‘∃ action p_action . ALOOKUP labels' n'' = SOME (termn(action,p_action)) ∧
                                         ALOOKUP labels n'' = SOME (termn(action,p_action))’ >-
             ( metis_tac[mk_terminal_leafs_in_old_new_labels] ) >>
            
            rgs[Once BDD_sem_cases] >>
                    
            rgs[] >>
            rgs[from_formula_to_action_def] >>
            
            parent_in_old_sem_correct_tac_r >>
            imp_res_tac terminals_eq_triviality 
   
            ,
            (* new layer wrt last layer in edges *)
            PairCases_on ‘x'’ >>
            rename1 ‘ALOOKUP edges' n'' = SOME (n1',n2')’ >>
            
            ‘lookup_is_some edges' n''’ by gvs[lookup_is_some_def] >>
            ‘∃x p. ALOOKUP labels' n'' = SOME (non_termn (SOME x,p))’ by
              (imp_res_tac WF_imp_non_leaf_lbl_abs >> metis_tac[]) >>

            ‘MEM n1' (dom_range_edges edges')’ by imp_res_tac lookup_edges_in_domain >>
            ‘MEM n2' (dom_range_edges edges')’ by imp_res_tac lookup_edges_in_domain >>
            
            assume_tac body_correctness_new_layer >>
            first_x_assum (strip_assume_tac o (Q.SPECL [‘r’, ‘edges’, ‘labels’, ‘r'’, ‘edges'’, ‘labels'’, ‘mv’,
                                                        ‘n''’, ‘n1'’, ‘n2'’, ‘x'’, ‘p'’, ‘c’, ‘c'’, ‘b’,
                                                        ‘vars ⧺ [h] ⧺ vars_consumed’, ‘h’, ‘rec’])) >>
            rgs[op_sem_def] >> gvs[] >>
            gvs[] >>
            
            subgoal ‘∃ p'' . ALOOKUP labels n'' = SOME (non_termn (NONE,p''))’ >-
             ( metis_tac [mk_now_internal_lbl_was_leaf_in_labels]) >>
            ‘x' = h ∧ p'' = p'’ by
              ( metis_tac[ntls_labels_and_prop_comp] ) >>
            
            parent_in_old_sem_correct_tac_r 
          ]
                                                        
          ,
          (* inner layer, that stayed inner using IH *)
          PairCases_on ‘x'’ >>
          rename1 ‘ALOOKUP edges n'' = SOME (n1',n2')’ >>
                  
          ‘lookup_is_some edges n''’ by gvs[lookup_is_some_def] >>
          ‘∃x p. ALOOKUP labels n'' = SOME (non_termn (SOME x,p))’ by
            (imp_res_tac WF_imp_non_leaf_lbl_abs >> metis_tac[]) >>

          subgoal ‘THE (INDEX_OF x' vars_consumed) < THE (INDEX_OF x vars_consumed)’ >-
           (imp_res_tac ordered_for_two_labels) >>

          first_x_assum (strip_assume_tac o (Q.SPECL [‘INDEX_OF (x':string) (vars_consumed: string list)’])) >>
          rgs[PULL_FORALL] >>
          first_x_assum (strip_assume_tac o (Q.SPECL [‘x'’, ‘vars_consumed’, ‘r’, ‘edges’, ‘labels’,
                                                      ‘r'’, ‘edges'’, ‘labels'’, ‘mv’, ‘n''’,‘n1'’, ‘n2'’,
                                                      ‘h’, ‘c’, ‘c'’, ‘p'’, ‘b’, ‘rec’, ‘vars’])) >> gvs[] >>
          
          ‘ALOOKUP edges' n'' = SOME (n1',n2')’ by
            (imp_res_tac inner_edges_are_same_exists >> gvs[]) >>
          ‘ALOOKUP labels' n'' = SOME (non_termn (SOME x',p'))’ by
            (imp_res_tac inner_labels_are_same_exists >> gvs[]) >>
          gvs[] >>
          
          parent_in_old_sem_correct_tac_r
        ]
        
      ]                          
  ]
QED



        
               
Theorem dom_range_edges_not:
  ∀ edges new_edges n.
    ¬MEM n (dom_range_edges (edges ⧺ new_edges)) ⇒
    ¬MEM n (dom_range_edges edges) ∧ ¬ MEM n (dom_range_edges new_edges)
Proof
  rpt strip_tac >>
  gvs[dom_range_edges_def]
QED



Theorem lookup_in_updt_labels_term:        
  ∀ labels n p h.
    ALOOKUP (non_term_leaf_updt labels h) n = SOME (termn p) ⇒
    ALOOKUP labels n = SOME (termn p)
Proof
  Induct >>
  rpt strip_tac >>
  gvs[non_term_leaf_updt_def] >>
  
  PairCases_on ‘h’ >> 
  gvs[AllCaseEqs()] >>
  Cases_on ‘h1’ >> gvs[] >>
  Cases_on ‘p'’ >> gvs[] >>
  gvs[AllCaseEqs()] >>
  res_tac >>
  Cases_on ‘q’ >> gvs[] >>
  gvs[AllCaseEqs()] >>
  res_tac  
QED




        
Triviality mem_not_mem_triv:
∀ l n1 n2. ¬MEM n1 l ∧  MEM n2 l ⇒ n1 ≠ n2       
Proof
  Induct >> gvs[]
QED


Theorem if_in_new_labels_parents_in_new_edges:        
  ∀ simp_leaves' new_labels new_edges n action prop x c.
    ALL_DISTINCT (MAP FST simp_leaves') ∧
    (ALOOKUP new_labels n = SOME (termn (action,prop)) ∨
     ALOOKUP new_labels n = SOME (non_termn (SOME x,prop)) ∨
     ALOOKUP new_labels n = SOME (non_termn (NONE,prop))             
    )∧
    mk_new_labels simp_leaves' c = new_labels ∧
    mk_new_edges simp_leaves' c = new_edges ⇒
    ∃ n_parent n'. ALOOKUP new_edges n_parent = SOME (n,n') ∨
                   ALOOKUP new_edges n_parent = SOME (n',n) 
Proof
  
  Induct >>
  rpt strip_tac >>
  imp_res_tac mk_body_map5 >-
   gvs[mk_new_labels_def] >-
  gvs[mk_new_labels_def, mk_new_edges_def] >>

  rgs[] >-
   rgs[mk_new_labels_def, mk_new_edges_def] >>
  
  ‘MEM n (MAP FST new_labels)’ by (imp_res_tac ALOOKUP_MEM >>   imp_res_tac mem_fst_snd >> gvs[]) >>
  ‘n < c + LENGTH new_labels ’ by (imp_res_tac counter_range_in_new_labels) >>
  imp_res_tac mk_body_map5 >>
  
  (PairCases_on ‘h’ >> rgs[] >> 
  rgs[mk_new_edges_def] >>
  rgs[mk_new_labels_def] >>
  Cases_on ‘new_labels’ >>
  Cases_on ‘new_edges’ >> 
  rgs[] >|[
    PairCases_on ‘h’ >> rgs[] >>
    PairCases_on ‘h'’ >> rgs[] >>
    gvs[] >>
    qexistsl_tac[‘h'0’, ‘c+1’] >> gvs[]
    ,
    PairCases_on ‘h’ >> rgs[] >>
    PairCases_on ‘h'’ >> rgs[] >>
    gvs[] >|[
        qexistsl_tac[‘h'0’, ‘c’] >> gvs[]
        ,
        gvs[AllCaseEqs()]>-
         (qexistsl_tac[‘h'0’, ‘c+1’] >> gvs[]) >-
         (qexistsl_tac[‘h'0’, ‘c’] >> gvs[]) >>
        res_tac >>
        imp_res_tac ALOOKUP_MEM >>
        imp_res_tac mem_fst_snd >>
        gvs[] >>
        metis_tac[mem_not_mem_triv]
      ]
  ])
QED

                                                        


        
Theorem edges_not_empty_correct_tl:        
  ∀vars_consumed r edges labels r' edges' labels' mv n h c c' action prop rec vars.
    prop1 rec ∧ prop2 rec ∧ prop3 rec ∧
          
    range_c c (r,edges,labels) ∧
    ALL_DISTINCT vars_consumed ∧
    ¬MEM h vars_consumed ∧
    BDD_ordered (r,edges,labels) vars_consumed ∧
    BDD_WF (r,edges,labels) ∧
    consumed_dom_bdd vars_consumed (r,edges,labels) ∧
                     
    correct_sem rec (r,edges,labels) (vars ⧺ [h] ⧺ vars_consumed) ∧
    body_of_mk rec (r,edges,labels) h c = SOME ((r',edges',labels'),c') ∧
               
    BDD_ordered (r',edges',labels') (h::vars_consumed) ∧
                
    mv_dom_vars mv (vars ⧺ [h] ⧺ vars_consumed) ∧
    fv_in_labels rec labels (vars ⧺ [h] ⧺ vars_consumed) ∧
      
    ALOOKUP edges' n = NONE ∧
    ALOOKUP labels' n = SOME (termn (action,prop)) ⇒
    SOME action = rec.sem prop mv
Proof 
  rpt strip_tac >>
  
  ‘range_c c' (r',edges',labels')’ by imp_res_tac WFness_range_c_inter >>
  ‘BDD_WF (r',edges',labels')’ by imp_res_tac WFness_translation_inter >>
  (*‘mv_dom_bdd mv (r,edges,labels)’ by imp_res_tac mv_dom_bdd_preserved >> replace with mv_dom_vars*)
  (*‘fv_in_labels rec labels mv’ by imp_res_tac fv_in_labels_preserved >> *)
 
  Cases_on ‘ALOOKUP (non_term_leaf_updt labels h) n’ >|[
    (* none in labels *)
       
    gvs[body_of_mk_def] >>
    gvs[AllCaseEqs()]>>
    body_of_mk_pred_tac >>
                        
    ‘ALOOKUP new_labels n = SOME (termn (action,prop))’ by rgs[ALOOKUP_APPEND] >>

    subgoal ‘∃ n_parent n'. ALOOKUP new_edges n_parent = SOME (n,n') ∨
                            ALOOKUP new_edges n_parent = SOME (n',n) ’ >-
     (
        ‘ALL_DISTINCT (MAP FST simp_leaves')’ by (rgs[BDD_WF_def] >> imp_res_tac_distinct) >>
        metis_tac[if_in_new_labels_parents_in_new_edges]
     ) >>
    (
    
    ‘∃ prop_parent . ALOOKUP ntl n_parent = SOME prop_parent ’ by
      (imp_res_tac_body >>  metis_tac[alookup_map_local_thm] ) >>

    subgoal ‘MEM n_parent leaves ∧ ∃ lbl. ALOOKUP leaves_labels n_parent = SOME lbl’ >- (
      imp_res_tac_body >>
      imp_res_tac alookup_nonterm_exsists >>
      imp_res_tac ALOOKUP_MEM >>
      imp_res_tac mem_fst_snd >> rgs[]
      ) >>

  
    ‘ALOOKUP labels n_parent = SOME lbl’ by imp_res_tac lookup_labels_of_leaves_same >>
    
    subgoal ‘c > n_parent’ >-
     (
     rgs[range_c_def] >>
     rgs[EVERY_MEM] >> imp_res_tac ALOOKUP_MEM >>
     imp_res_tac mem_fst_snd >>
     rgs[]
     )
     ) >| [
      assume_tac body_return_in_decision_str_conv >>
      first_x_assum (strip_assume_tac o (Q.SPECL [‘simp_leaves'’, ‘leaves_sub’, ‘ntl’, ‘simp_leaves’,
                                                  ‘new_edges’, ‘new_labels’, ‘n_parent’,
                                                  ‘n’, ‘n'’, ‘prop_parent’, ‘termn (action,prop)’, ‘p'’,
                                                  ‘h’, ‘c’, ‘rec’])) >>
      rgs[] >>
      rgs[from_formula_to_action_def, op_sem_def] >>
      rgs[determine_termn_def] >>
      rgs[AllCaseEqs()]>>
      rgs[prop1_def] >>
      rgs[prop2_def] >>
      res_tac >>
      rgs[prop3_def] >>
      res_tac >>        
      gvs[]
      ,
      assume_tac body_return_in_decision_str_conv >>
      first_x_assum (strip_assume_tac o (Q.SPECL [‘simp_leaves'’, ‘leaves_sub’, ‘ntl’, ‘simp_leaves’,
                                                  ‘new_edges’, ‘new_labels’, ‘n_parent’,
                                                  ‘n'’, ‘n’, ‘prop_parent’, ‘p'’, ‘termn (action,prop)’,
                                                  ‘h’, ‘c’, ‘rec’])) >>
      
      rgs[from_formula_to_action_def, op_sem_def] >>
      rgs[determine_termn_def] >>
      rgs[AllCaseEqs()]>>
      rgs[prop1_def] >>
      rgs[prop2_def] >>
      res_tac >>
      rgs[prop3_def] >>
      res_tac >>        
      gvs[]
    ]

    ,
    imp_res_tac body_of_mk_output >> rgs[] >>

    ‘SOME x = SOME (termn (action,prop))’ by (rgs[BDD_WF_def] >> rgs[ALL_DISTINCT_APPEND, ALOOKUP_APPEND]) >>
    rgs[] >>
          

    ‘ALOOKUP labels n = SOME (termn (action,prop))’ by imp_res_tac lookup_in_updt_labels_term >>
    rgs[] >>
          
    rgs[correct_sem_def] >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘n’, ‘mv’, ‘SOME action’])) >>
    gvs[get_prop_def, op_sem_def] >>

    subgoal ‘BDD_sem rec (r,edges,labels) mv n (SOME action)’ >-
     (
     simp[Once BDD_sem_cases] >>
     rgs[from_formula_to_action_def, ALOOKUP_APPEND] >>
     gvs[AllCaseEqs()]
     ) >>
    gvs[]
  ]       
QED


 
(* this is a concrete theorem, with the correct vars, vars_consumed distrubution, 
   later in this file I am more general and instansiate it with just vars *)
Theorem correct_sem_translation_inter:
  ∀ (BDD:('a,'b) BDD) BDD'' rec c c' vars h vars_consumed.
    prop1 rec ∧ prop2 rec ∧ prop3 rec ∧
    
    range_c c BDD ∧
    ALL_DISTINCT (h::vars_consumed) ∧
    BDD_ordered BDD (vars_consumed) ∧
    fv_in_BDD rec BDD (vars ⧺ [h] ⧺ vars_consumed) ∧
    BDD_WF BDD ∧
    consumed_dom_bdd (vars_consumed) BDD ∧
    
    correct_sem rec BDD (vars ⧺ [h] ⧺ vars_consumed)∧
    body_of_mk rec BDD h c = SOME (BDD'',c') ⇒
    correct_sem rec BDD'' (vars ⧺ [h] ⧺ vars_consumed)
Proof
        
  rpt strip_tac >>


  imp_res_tac order_translation_inter >>
  imp_res_tac WFness_range_c_inter >>
  ‘BDD_WF BDD''’ by imp_res_tac WFness_translation_inter >>

  PairCases_on ‘BDD’ >>
  rename1 ‘(r,edges,labels)’ >>
  
  PairCases_on ‘BDD''’ >>
  rename1 ‘(r',edges',labels')’ >>

  simp [correct_sem_def] >>
  rpt strip_tac >>

  Cases_on ‘ALOOKUP edges' n’ >|[
    (* completly new edges: trivial *)
    rgs[op_sem_def] >>
    rgs[get_prop_def] >>
    rpt (BasicProvers.full_case_tac >> gvs[]) >>
        
    rgs[Once BDD_sem_cases] >>
    rgs[from_formula_to_action_def] >>
    Cases_on ‘b’ >> gvs[] >>

    gvs[fv_in_BDD_def] >>
    metis_tac[edges_not_empty_correct_tl]
    ,
    (*inner nodes including the changed layer *)
    Cases_on ‘x’ >>
    rename1 ‘ALOOKUP edges' n = SOME (n',n'')’ >>

    (* from WFness we know that n's label is x,p*)
    ‘MEM n (dom_range_edges edges')’ by imp_res_tac lookup_edges_in_domain >>
    ‘lookup_is_some edges' n’ by gvs[lookup_is_some_def] >>
    ‘is_lookup_internal labels' n’ by (rgs[BDD_WF_def] >>res_tac) >>

    rgs[is_lookup_internal_def] >>
    rgs[get_prop_def] >>
   (* ‘fv_in_labels rec labels mv’ by imp_res_tac fv_in_labels_preserved >> *)
                      
    assume_tac correct_sem_translation_inner_nodes >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘vars_consumed’, ‘x’, ‘r’, ‘edges’, ‘labels’, ‘r'’,
                                                ‘edges'’, ‘labels'’, ‘mv’, ‘n’, ‘n'’, ‘n''’, ‘h’, ‘c’,
                                                ‘c'’, ‘p’, ‘b’, ‘rec’, ‘vars’])) >>
    gvs[]
  ]

QED




        
Theorem fv_in_body_of_mk_verbose:
  ∀ simp_leaves simp_leaves' leaves_sub ntl new_edges new_labels n_parent n n' prop_parent x p c rec varslist h. 
    c > n_parent ∧ prop4 rec ∧
    fv_in_vars rec prop_parent varslist∧
    ALOOKUP ntl n_parent = SOME prop_parent ∧
    leaves_pred_sub rec ntl h = leaves_sub ∧
    simp_pred_list rec leaves_sub = simp_leaves ∧
    determine_termn_list rec simp_leaves = simp_leaves' ∧
    mk_new_edges simp_leaves' c = new_edges ∧
    mk_new_edges simp_leaves' c = new_edges ∧
    mk_new_labels simp_leaves' c = new_labels ∧
    (ALOOKUP new_edges n_parent = SOME (n,n') ∨ ALOOKUP new_edges n_parent = SOME (n',n))∧
    ALOOKUP new_labels n = SOME (non_termn (NONE,p)) ⇒
    fv_in_vars rec p varslist
Proof

  rpt strip_tac >>
  imp_res_tac leaves_pred_sub_alookup_some >>
  imp_res_tac simp_pred_list_alookup_some >>
  imp_res_tac determine_termn_list_alookup_some >>
  
  assume_tac (INST_TYPE [“:'a” |-> “:string” , “:'b” |-> “:('a,'b) label” ] mk_new_labels_contains_prop)  >>
  
  first_x_assum (strip_assume_tac o (Q.SPECL [‘simp_leaves'’, ‘new_edges’, ‘new_labels’,
                                              ‘determine_termn rec (rec.simp (rec.sub prop_parent h T))’,
                                            ‘determine_termn rec (rec.simp (rec.sub prop_parent h F))’,
                                            ‘n_parent’])) >>
  rgs[] >>
  first_x_assum (strip_assume_tac o (Q.SPECL [‘c’])) >>
  rgs[determine_termn_def] >>
  rgs[AllCaseEqs()] >> gvs[prop4_def]
QED


        

Theorem fv_in_body_of_mk_verbose_multi:
  ∀ simp_leaves simp_leaves' leaves_sub ntl new_edges new_labels n_parent n n' prop_parent x p c rec h vars vars_consumed. 
    c > n_parent ∧ prop4 rec ∧
    fv_in_vars rec prop_parent (vars ⧺ [h] ⧺ vars_consumed) ∧
    ALOOKUP ntl n_parent = SOME prop_parent ∧
    leaves_pred_sub rec ntl h = leaves_sub ∧
    simp_pred_list rec leaves_sub = simp_leaves ∧
    determine_termn_list rec simp_leaves = simp_leaves' ∧
    mk_new_edges simp_leaves' c = new_edges ∧
    mk_new_edges simp_leaves' c = new_edges ∧
    mk_new_labels simp_leaves' c = new_labels ∧
    (ALOOKUP new_edges n_parent = SOME (n,n') ∨ ALOOKUP new_edges n_parent = SOME (n',n))∧
    ALOOKUP new_labels n = SOME (non_termn (NONE,p)) ⇒
    fv_in_vars rec p (vars ⧺ [h] ⧺ vars_consumed)
Proof
  metis_tac[fv_in_body_of_mk_verbose]
QED

(*
Definition prop4_def:
  prop4 rec =    
  ∀ varslist prop_parent p b h.
  rec.simp (rec.sub prop_parent h b) = p ∧
  fv_in_vars rec prop_parent varslist ⇒
  fv_in_vars rec p varslist
End
*)
(*
Theorem prop4_imp_fv_in_vars:       
  ∀ varslist prop_parent p b h rec.
  rec.simp (rec.sub prop_parent h b) = p ∧
  fv_in_vars rec prop_parent varslist ⇒
  fv_in_vars rec p varslist
Proof
  rpt strip_tac >>
  rgs[fv_in_vars_def] >>
  
        
QED
*)

               
Theorem fv_in_BDD_body_preserved:
  ∀ r edges labels r'' edges'' labels'' c rec c' h vars vars_consumed.        
    range_c c (r,edges,labels) ∧ prop4 rec ∧
    ALL_DISTINCT (vars ⧺ [h] ⧺ vars_consumed) ∧
    BDD_WF (r,edges,labels) ∧
    fv_in_BDD rec (r,edges,labels) (vars ⧺ [h] ⧺ vars_consumed) ∧
    body_of_mk rec (r,edges,labels) h c = SOME ((r'',edges'',labels''),c') ⇒
    fv_in_BDD rec (r'',edges'',labels'') (vars ⧺ [h] ⧺ vars_consumed)
Proof
  
  rpt strip_tac >>
  rgs[fv_in_BDD_def, fv_in_labels_def] >>
  rpt strip_tac >>
  
  gvs[body_of_mk_def] >>
  gvs[AllCaseEqs()]>>
  body_of_mk_pred_tac >>
  
  rgs[ALOOKUP_APPEND] >>
  rgs[AllCaseEqs()] >|[
    (* case when in new labels, we wanna show that the parent had all fv defined and
       then the children are also the same out of the body *)
    
    Cases_on ‘opx’ >|[
      
      subgoal ‘∃ n_parent n'. ALOOKUP new_edges n_parent = SOME (n,n') ∨
                              ALOOKUP new_edges n_parent = SOME (n',n) ’ >-
       (
       ‘ALL_DISTINCT (MAP FST simp_leaves')’ by (rgs[BDD_WF_def] >> imp_res_tac_distinct) >>
       metis_tac[if_in_new_labels_parents_in_new_edges]
       ) >>
      
      (
      ‘∃ prop_parent . ALOOKUP ntl n_parent = SOME prop_parent ’ by
         (imp_res_tac_body >>  metis_tac[alookup_map_local_thm] ) >>
      
      
      subgoal ‘MEM n_parent leaves ∧ ∃ lbl. ALOOKUP leaves_labels n_parent = SOME lbl’ >- (
        imp_res_tac_body >>
        imp_res_tac alookup_nonterm_exsists >>
        imp_res_tac ALOOKUP_MEM >>
        imp_res_tac mem_fst_snd >> rgs[]
        ) >>
      
      ‘ALOOKUP labels n_parent = SOME lbl’ by imp_res_tac lookup_labels_of_leaves_same >>
      ‘ALL_DISTINCT (MAP FST leaves_labels)’ by  (rgs[BDD_WF_def] >> imp_res_tac_distinct) >>
      ‘lbl = non_termn (NONE,prop_parent)’ by imp_res_tac lbl_pred_rel_extract_nontermn >>
      rgs[] >>
      
      first_x_assum (strip_assume_tac o (Q.SPECL [‘n_parent’, ‘NONE’, ‘prop_parent’])) >>
      rgs[] >>
      
      subgoal ‘c > n_parent’ >-
       (
       rgs[range_c_def] >>
       rgs[EVERY_MEM] >> imp_res_tac ALOOKUP_MEM >>
       imp_res_tac mem_fst_snd >>
       rgs[]
       ) >>
      rgs[] >>

      assume_tac fv_in_body_of_mk_verbose_multi >>
      srw_tac [SatisfySimps.SATISFY_ss][]
      ) 
      ,
      (* new edges cannot have SOME x there, proof by contr *)
      ‘ALL_DISTINCT (MAP FST simp_leaves')’ by (rgs[BDD_WF_def] >> imp_res_tac_distinct) >>
      imp_res_tac new_labels_are_not_internal
    ]
    ,

    (* case in labels *)
    imp_res_tac lookup_non_term_leaf_some >>
    Cases_on ‘lbl’ >-
     (imp_res_tac lookup_labels_in_updt_term >>
      metis_tac[]) >>
    
    Cases_on ‘p'’ >>
    Cases_on ‘q’ >|[
        imp_res_tac lookup_labels_in_updt_none >>
        Cases_on ‘opx’ >> gvs[] >>
        res_tac
        ,
        imp_res_tac lookup_labels_in_updt >>
        metis_tac[]
      ]        
  ]
QED              



(* in the previous theorems varslist = ((REVERSE vars)++vars_consumed) *)         
Theorem correct_sem_translation:
  ∀ vars vars_consumed BDD BDD' rec c.
    prop1 rec ∧ prop2 rec ∧ prop3 rec ∧ prop4 rec ∧
    BDD_ordered BDD vars_consumed ∧
    BDD_WF BDD ∧
    range_c c BDD ∧
    consumed_dom_bdd vars_consumed BDD ∧
    ALL_DISTINCT ((REVERSE vars)++vars_consumed) ∧
    fv_in_BDD rec BDD ((REVERSE vars)++vars_consumed) ∧
    correct_sem rec BDD ((REVERSE vars)++vars_consumed) ∧
    SOME BDD' = mk_BDDPred rec BDD vars_consumed vars c ⇒
    correct_sem rec BDD' ((REVERSE vars)++vars_consumed) 
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

    ‘ALL_DISTINCT (h::vars_consumed)’ by gvs[ALL_DISTINCT_APPEND] >>        
    ‘BDD_ordered (r'',edges'',labels'') (h::vars_consumed)’ by imp_res_tac order_translation_inter >>
      
    ‘consumed_dom_bdd (h::vars_consumed) (r'',edges'',labels'')’ by imp_res_tac consumed_dom_bdd_inter >>


    assume_tac correct_sem_translation_inter >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘(r,edges,labels)’, ‘(r'',edges'',labels'')’, ‘rec’, ‘c’, ‘c'’, ‘REVERSE vars’, ‘h’, ‘vars_consumed’])) >>
    gvs[]>>
                
    (*  ‘REVERSE vars ⧺ h::vars_consumed = REVERSE vars ++ [h] ++ vars_consumed’ by gvs[Once CONS_APPEND] >>
        ‘ALL_DISTINCT (REVERSE vars ⧺ h::vars_consumed)’ by metis_tac[] >>
     *)
    first_x_assum (strip_assume_tac o (Q.SPECL [‘[h] ⧺ vars_consumed’, ‘(r'',edges'',labels'')’, ‘(r',edges',labels')’, ‘rec’, ‘c'’])) >>
    gvs[] >>
          
    ‘fv_in_BDD rec (r'',edges'',labels'') (REVERSE vars ⧺ [h] ⧺ vars_consumed)’ by metis_tac[fv_in_BDD_body_preserved] >>
    
    metis_tac[]
  ]
QED
    



(* in the previous theorems varslist = ((REVERSE vars)++vars_consumed) *)         
Theorem correct_sem_valid_translation_verbose:
  ∀ vars vars_consumed BDD BDD' rec c.
    prop1 rec ∧ prop2 rec ∧ prop3 rec ∧ prop4 rec ∧
    BDD_ordered BDD vars_consumed ∧
    BDD_WF BDD ∧
    range_c c BDD ∧
    consumed_dom_bdd vars_consumed BDD ∧
    ALL_DISTINCT ((REVERSE vars)++vars_consumed) ∧
    fv_in_BDD rec BDD ((REVERSE vars)++vars_consumed) ∧
    correct_sem rec BDD ((REVERSE vars)++vars_consumed) ∧
    SOME BDD' = mk_BDDPred rec BDD vars_consumed vars c ⇒
    (
    BDD_WF BDD'  ∧
    BDD_ordered BDD' ((REVERSE vars)++vars_consumed)  ∧
    fv_in_BDD rec BDD' ((REVERSE vars)++vars_consumed)  ∧
    consumed_dom_bdd ((REVERSE vars)++vars_consumed)  BDD' ∧
    correct_sem rec BDD' ((REVERSE vars)++vars_consumed) )
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

    ‘ALL_DISTINCT (h::vars_consumed)’ by gvs[ALL_DISTINCT_APPEND] >>        
    ‘BDD_ordered (r'',edges'',labels'') (h::vars_consumed)’ by imp_res_tac order_translation_inter >>
      
    ‘consumed_dom_bdd (h::vars_consumed) (r'',edges'',labels'')’ by imp_res_tac consumed_dom_bdd_inter >>


    assume_tac correct_sem_translation_inter >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘(r,edges,labels)’, ‘(r'',edges'',labels'')’, ‘rec’, ‘c’, ‘c'’, ‘REVERSE vars’, ‘h’, ‘vars_consumed’])) >>
    gvs[]>>
                
    (*  ‘REVERSE vars ⧺ h::vars_consumed = REVERSE vars ++ [h] ++ vars_consumed’ by gvs[Once CONS_APPEND] >>
        ‘ALL_DISTINCT (REVERSE vars ⧺ h::vars_consumed)’ by metis_tac[] >>
     *)
    first_x_assum (strip_assume_tac o (Q.SPECL [‘[h] ⧺ vars_consumed’, ‘(r'',edges'',labels'')’, ‘(r',edges',labels')’, ‘rec’, ‘c'’])) >>
    gvs[] >>
          
    ‘fv_in_BDD rec (r'',edges'',labels'') (REVERSE vars ⧺ [h] ⧺ vars_consumed)’ by metis_tac[fv_in_BDD_body_preserved] >>
    
    metis_tac[]
  ]
QED

        





        
(* in the previous theorems varslist = ((REVERSE vars)++vars_consumed) *)         
Theorem correct_sem_valid_translation:
  ∀ vars vars_consumed BDD BDD' rec c.
    prop1 rec ∧ prop2 rec ∧ prop3 rec ∧ prop4 rec ∧

    range_c c BDD ∧
    ALL_DISTINCT ((REVERSE vars)++vars_consumed) ∧
          
    valid_BDD rec BDD vars vars_consumed ∧
    correct_sem rec BDD ((REVERSE vars)++vars_consumed) ∧
                
    SOME BDD' = mk_BDDPred rec BDD vars_consumed vars c ⇒
    (
    valid_BDD rec BDD' [] ((REVERSE vars)++vars_consumed) ∧
    correct_sem rec BDD' ((REVERSE vars)++vars_consumed) )
Proof

  rw[valid_BDD_def] >>
  metis_tac[correct_sem_valid_translation_verbose]
QED







        

val _ = export_theory ();




