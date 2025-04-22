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


Theorem BDD_sem_determ_not:
  ∀ n r edges labels mv b rec n' n'' x p.
    ALOOKUP edges n = SOME (n',n'') ∧
    ALOOKUP labels n = SOME (non_termn (SOME x,p)) ∧
    ALOOKUP mv x = SOME T ∧
    BDD_sem rec (r,edges,labels) mv n b ⇒
    ~ ∃ b' . b' ≠ b ∧BDD_sem rec (r,edges,labels) mv n b'
Proof
 rpt strip_tac >>
 gvs[Once BDD_sem_cases] >>
 rgs[Once BDD_sem_cases] >>
 imp_res_tac BDD_sem_determ
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


Theorem dom_range_edges_in_append:
∀ edges new_edges n.
MEM n (dom_range_edges new_edges) ⇒
MEM n (dom_range_edges (edges++new_edges))
Proof
  Induct >>
  gvs[dom_range_edges_def]
QED



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
Theorem edges_empty_correct:
  ∀r edges labels r' edges' labels' mv n n' n'' x p c c' p' h rec.
    prop1 rec ∧
    prop2 rec ∧
    range_c c ((r,edges,labels):('a,'b) BDD) ∧
    BDD_WF (r,edges,labels) ∧
    body_of_mk rec (r,edges,labels) h c = SOME ((r',edges',labels'),c') ∧
    ALOOKUP edges' n = SOME (n',n'') ∧
    ALOOKUP labels' n = SOME (non_termn (SOME x,p)) ∧
    fv_in_labels rec labels mv ∧
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
    ALOOKUP mv h = SOME T ∧
    
    ALOOKUP ntl n = SOME p ∧
    ALOOKUP new_edges n = SOME (n',n'') ∧
    leaves_pred_sub rec ntl h = leaves_sub ∧ 
    simp_pred_list rec leaves_sub = simp_leaves ∧
    determine_termn_list rec simp_leaves = simp_leaves' ∧
    mk_new_edges simp_leaves' c = new_edges ∧
    mk_new_labels simp_leaves' c = new_labels ∧
    ALOOKUP new_labels n' = SOME p'
    ⇒
    from_formula_to_action rec p' mv = op_sem rec (SOME p) mv
Proof
  
  rpt strip_tac >>
  assume_tac  body_return_in_decision_str_conv >>
  first_x_assum (strip_assume_tac o (Q.SPECL [‘simp_leaves'’, ‘leaves_sub’, ‘ntl’, ‘simp_leaves’, ‘new_edges’, ‘new_labels’, ‘n’,
                                              ‘n'’, ‘n''’, ‘p’, ‘p'’, ‘p''’, ‘h’, ‘c’, ‘rec’])) >>
  rgs[] >>
  
  rgs[from_formula_to_action_def, op_sem_def] >>
  rgs[determine_termn_def] >>
  rgs[AllCaseEqs()]>>
  rgs[prop1_def] >>
  rgs[prop2_def] >>
  res_tac 
QED






                                              




                                              

Theorem body_correctness_new_layer:       
  ∀ r edges labels r' edges' labels' mv n n' n'' x p c c' b vars_consumed h rec.
    prop1 rec ∧ prop2 rec ∧ range_c c (r,edges,labels) ∧
          
    BDD_WF (r,edges,labels) ∧
    BDD_WF (r',edges',labels') ∧
    mv_dom_bdd mv (r',edges',labels') ∧
    fv_in_labels rec labels mv ∧
    consumed_dom_bdd vars_consumed (r,edges,labels) ∧
    range_c c (r,edges,labels) ∧

                     
    correct_sem rec (r,edges,labels) ∧
    body_of_mk rec (r,edges,labels) h c = SOME ((r',edges',labels'),c') ∧
    BDD_sem rec (r',edges',labels') mv n b ∧
    ALOOKUP edges' n = SOME (n',n'') ∧
    ALOOKUP labels' n = SOME (non_termn (SOME x,p)) ∧
    ALOOKUP edges n = NONE ⇒
    b = op_sem rec (SOME p) mv
Proof

rpt strip_tac >>
‘ALOOKUP edges' n' = NONE’ by imp_res_tac mk_body_new_edges_none >>
‘ALOOKUP edges' n'' = NONE’ by imp_res_tac mk_body_new_edges_none >>
rgs[Once BDD_sem_cases] >>
rgs[Once BDD_sem_cases] >| [
    (*case n' *)

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
      ‘ALOOKUP labels n = SOME (non_termn (NONE,p))’ by  cheat >> (*imp_res_tac lookup_labels_of_leaves_same >>*)
      ‘x=h’ by  cheat >> (*lookup_non_term_leaf_updt_internal*)
      rgs[] >>

      ‘ALOOKUP ntl n = SOME p’ by imp_res_tac leaves_in_ntl_lemma >>
      ‘ALL_DISTINCT (MAP FST labels)’ by cheat >>
      ‘ALOOKUP leaves_labels n = SOME (non_termn (NONE,p))’ by imp_res_tac leaves_labels_same_in_labels_some >>
      ‘ALOOKUP new_edges n = SOME (n',n'')’ by cheat >>

      (* we also know that the new label for the new leafs are in new_labels*)
      ‘ALOOKUP new_labels n' = SOME p'’ by cheat >>


      rgs[range_c_def] >>

      assume_tac statements_structs_correctness_new_layer >>
      first_x_assum (strip_assume_tac o (Q.SPECL [‘simp_leaves'’, ‘leaves_sub’, ‘ntl’, ‘simp_leaves’, ‘new_edges’, ‘new_labels’,
                                                 ‘n’, ‘n'’, ‘n''’, ‘p’, ‘p'’, ‘p''’, ‘h’, ‘c’, ‘mv’, ‘rec’])) >> 
      

      subgoal ‘fv_in_p rec p mv’ >-
       (rgs[fv_in_labels_def] >>
        metis_tac[]) >>
        
      subgoal ‘c > n’ >- (
       rgs[EVERY_MEM] >>
       imp_res_tac ALOOKUP_MEM >>
       imp_res_tac mem_fst_snd >>
       rgs[]
      ) >>
        
      rgs[]
               
      ,
      (* if n is not in edges, it means either the edges are empty so we work with root, otherwise by contradiction*)
      Cases_on ‘edges = []’  >|[
          (* then we should prove the root*)
          imp_res_tac edges_empty_correct    
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
        ]
    ]
    ,
    (*case n'' *)
    cheat
  ]


QED


                                



Theorem bdd_sem_imp:
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


(*
Prop
(∃p' x'' b. p = rec.simp (rec.sub p' x'' b))

Theorem WF_imp_non_leaf_lbl_abs_sub_lemma:
  ∀r edges labels n rec.
    lookup_is_some edges n ∧
    BDD_WF (r,edges,labels) ⇒
    ∃x p x' b. ALOOKUP labels n = SOME (non_termn (SOME x, (rec.simp(rec.sub p x' b))))
Proof
  rpt strip_tac >>
  fs[lookup_is_some_def] >>
  PairCases_on ‘y’ >>
  imp_res_tac WF_imp_non_leaf_lbl >>
  gvs[] >>
  cheat
QED  
*)                                                              


                                
(*** this is lemma 2 (modified) ***)
Theorem correct_sem_translation_inner_nodes:
  ∀ vars_consumed x r edges labels r' edges' labels' mv n n' n'' h c c' p b rec.                     
    BDD_ordered ((r,edges,labels):('a,'b) BDD) (vars_consumed) ∧
    BDD_WF (r,edges,labels) ∧
    BDD_WF (r',edges',labels') ∧ (* induce it initially *)
             
    mv_dom_bdd mv (r',edges',labels') ∧
    consumed_dom_bdd (vars_consumed) (r,edges,labels) ∧
    fv_in_labels rec labels' mv ∧
                 
    correct_sem rec (r,edges,labels) ∧
    body_of_mk rec (r,edges,labels) h c = SOME ((r',edges',labels'),c') ∧
               
    BDD_sem rec (r',edges',labels') mv n b ∧
    ALOOKUP edges' n = SOME (n',n'') ∧
    ALOOKUP labels' n = SOME (non_termn (SOME x,p)) ⇒
    b = op_sem rec (SOME p) mv
Proof

  ntac 2 strip_tac >>
  measureInduct_on `THE(INDEX_OF x vars_consumed)` >>
  rpt strip_tac >>
  
  ‘MEM n (dom_range_edges edges')’ by imp_res_tac lookup_edges_in_domain >>
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
        Cases_on ‘ALOOKUP edges n'’ >> rgs[] >|[
          (* from body *)
          cheat
          ,
          PairCases_on ‘x'’ >>
          rename1 ‘ALOOKUP edges n' = SOME (n1',n2')’ >>
                  
          ‘lookup_is_some edges n'’ by gvs[lookup_is_some_def] >>
          ‘∃x p. ALOOKUP labels n' = SOME (non_termn (SOME x,p))’ by (imp_res_tac WF_imp_non_leaf_lbl_abs >> metis_tac[]) >>
        

          subgoal ‘THE (INDEX_OF x' vars_consumed) < THE (INDEX_OF x vars_consumed)’ >-
           (
           
           ‘MEM x' vars_consumed ∧ MEM x vars_consumed’ by (rgs[Once consumed_dom_bdd_def] >> res_tac >> fs[]) >>
           ‘∃i. INDEX_OF x vars_consumed = SOME i’ by (imp_res_tac MEM_INDEX_OF >> gvs[] )>>
           ‘∃i'. INDEX_OF x' vars_consumed = SOME i'’ by (imp_res_tac MEM_INDEX_OF >> gvs[]) >>
           
           rgs[Once BDD_ordered_def]>>
           first_x_assum (strip_assume_tac o (Q.SPECL [‘n’,‘n'’, ‘n''’]))>>
           gvs[order_hold_def]
           ) >>


            (*
        subgoal  ‘∃x p x' b.
         ALOOKUP labels n' =
         SOME (non_termn (SOME x,rec.simp (rec.sub p x' b)))’ by (imp_res_tac WF_imp_non_leaf_lbl_abs_sub_lemma >> cheat) >>
          *)


           
                
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
          gvs[] >>

          (****************)


          gvs[correct_sem_def] >>

                

                
          subgoal ‘∃b. BDD_sem rec (r,edges,labels) mv n b’ >-
           (
           assume_tac BDD_sem_exsists >>
           first_x_assum (strip_assume_tac o (Q.SPECL [‘(r,edges,labels)’, ‘mv’, ‘n’, ‘vars_consumed’, ‘rec’])) >>
           gvs[] >>
           ‘mv_dom_bdd mv (r,edges,labels) ∧ node_in_BDD n (r,edges,labels)’ by cheat >>
           gvs[] >>
           srw_tac [SatisfySimps.SATISFY_ss][]
           ) >>


          
          subgoal ‘∃b. BDD_sem rec (r,edges,labels) mv n' b’ >-
           (
           assume_tac BDD_sem_exsists >>
           first_x_assum (strip_assume_tac o (Q.SPECL [‘(r,edges,labels)’, ‘mv’, ‘n'’, ‘vars_consumed’, ‘rec’])) >>
           gvs[] >>
           ‘mv_dom_bdd mv (r,edges,labels) ∧ node_in_BDD n' (r,edges,labels)’ by cheat >>
           gvs[] >>
           srw_tac [SatisfySimps.SATISFY_ss][]

           ) >>




           subgoal ‘ b = op_sem rec (get_prop labels n) mv’ >- (
            first_x_assum (strip_assume_tac o (Q.SPECL [‘n’, ‘mv’, ‘b’])) >>
            ‘mv_dom_bdd mv (r,edges,labels) ∧ fv_in_labels rec labels mv’ by cheat >>
            gvs[]
            ) >>
          
          
          subgoal ‘ b' = op_sem rec (get_prop labels n') mv’ >- (
            first_x_assum (strip_assume_tac o (Q.SPECL [‘n'’, ‘mv’, ‘b'’])) >>
            ‘mv_dom_bdd mv (r,edges,labels) ∧ fv_in_labels rec labels mv’ by cheat >>
            gvs[]
            ) >>


          rgs[get_prop_def] >>
          rgs[op_sem_def] >>

             qpat_x_assum ‘BDD_sem rec (r,edges,labels) mv n (rec.sem p mv)’
             (fn thm => assume_tac (SIMP_RULE (srw_ss()) [Once BDD_sem_cases] thm)) >>
          
          rgs[] >>
          imp_res_tac BDD_sem_determ 
          
        ]
        ,
        (* False *)
        cheat

      ]


  ]
QED

               























               



        

Theorem correct_sem_translation_inter:
  ∀ (BDD:('a,'b) BDD) BDD'' rec c c' vars h vars_consumed.
    prop1 rec ∧

    range_c c BDD ∧
    ALL_DISTINCT (h::vars_consumed) ∧
    BDD_ordered BDD (vars_consumed) ∧      
    BDD_WF BDD ∧
    consumed_dom_bdd (vars_consumed) BDD ∧
                     
    correct_sem rec BDD ∧
    body_of_mk rec BDD h c = SOME (BDD'',c') ⇒
    correct_sem rec BDD'' 
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
  
    cheat (* TODO: consult with Roberto about this one*)
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

    assume_tac correct_sem_translation_inner_nodes >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘vars_consumed’, ‘x’, ‘r’, ‘edges’, ‘labels’, ‘r'’,
                                                ‘edges'’, ‘labels'’, ‘mv’, ‘n’, ‘n'’, ‘n''’, ‘h’, ‘c’,
                                                ‘c'’])) >>
    gvs[]
  ]

QED





       

        


        
                 

Theorem correct_sem_translation:
  ∀ vars vars_consumed BDD BDD' rec c.
    prop1 rec ∧
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
                
    ‘ALL_DISTINCT (REVERSE vars ⧺ h::vars_consumed)’ by cheat >>

    metis_tac[]
  ]
QED
    



val _ = export_theory ();
