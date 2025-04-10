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

open bdd_genTheory;     
open bdd_auxTheory;     

     
val _ = new_theory "bdd_gen_wf";


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

        
Theorem WFness_range_c_inter:
  ∀ BDD BDD'' c c' h rec.
    range_c c BDD ∧
    body_of_mk rec BDD h c = SOME (BDD'',c') ⇒
    range_c c' BDD''
Proof
  rpt strip_tac >>
  PairCases_on ‘BDD’ >>
  rename1 ‘(r,edges,labels)’ >>
          
  gvs[body_of_mk_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  body_of_mk_pred_tac >>

  rgs[range_c_def] >>
  rpt strip_tac >>
      
  imp_res_tac_body >>
  ‘∃old_updated .non_term_leaf_updt labels h = old_updated’ by gvs[] >>              
  imp_res_tac mk_body_map6 >>
  
  rgs[EVERY_MEM] >>
  rpt strip_tac >| [
    first_x_assum (strip_assume_tac o (Q.SPECL [‘n’])) >>
    rgs[] >> metis_tac[]
    ,
    
    imp_res_tac length_new_labels >>                
    imp_res_tac counter_range_in_new_labels >>
    rgs[]
  ]
QED






Theorem WFness_distinct_edges_labels:
  ∀ BDD r'' edges'' labels'' c c' h rec.
    range_c c BDD ∧
    BDD_WF BDD ∧
    body_of_mk rec BDD h c = SOME ((r'',edges'',labels''),c') ⇒
    (ALL_DISTINCT (MAP FST edges'') ∧ ALL_DISTINCT (MAP FST labels''))
Proof
  rpt strip_tac >>
  PairCases_on ‘BDD’ >>
  rename1 ‘(r,edges,labels)’ >>
          
  gvs[body_of_mk_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  body_of_mk_pred_tac >|[

    ‘ALL_DISTINCT (MAP FST edges)’ by rgs[Once BDD_WF_def] >>
    ‘∃ leaves. getLeaves edges r = leaves’ by gvs[] >>
    
    imp_res_tac all_distinct_leaves >>
    ‘ALL_DISTINCT (MAP FST leaves_labels)’ by (imp_res_tac all_distinct_leaves_labels >> gvs[]) >>
    imp_res_tac all_distinct_ntl >>       
    imp_res_tac all_distinct_sub >>
    imp_res_tac all_distinct_simp >>
    ‘ALL_DISTINCT (MAP FST simp_leaves')’ by (imp_res_tac all_distinct_determine >> gvs[]) >>        
    ‘ALL_DISTINCT (MAP FST new_edges)’ by (imp_res_tac all_distinct_mk_edges >> gvs[]) >>
    
    simp[ALL_DISTINCT_APPEND]>> 
    strip_tac >> strip_tac >>
    imp_res_tac leaves_are_not_parents>>
    
    imp_res_tac_body >>
    rgs[] >>
    
    imp_res_tac extract_nonterm_mem_neg >>   
    gvs[ALOOKUP_NONE]
    ,
    
    
    ‘ALL_DISTINCT (MAP FST labels)’ by rgs[Once BDD_WF_def] >>
    ‘ALL_DISTINCT (MAP FST (non_term_leaf_updt labels h))’ by (imp_res_tac all_distinct_non_term_leaf_updt >> gvs[]) >>

    (* same as before *)
    subgoal ‘ALL_DISTINCT (MAP FST new_labels)’ >- (
      ‘ALL_DISTINCT (MAP FST edges)’ by rgs[Once BDD_WF_def] >>
      ‘∃ leaves. getLeaves edges r = leaves’ by gvs[] >>
      
      imp_res_tac all_distinct_leaves >>
      ‘ALL_DISTINCT (MAP FST leaves_labels)’ by (imp_res_tac all_distinct_leaves_labels >> gvs[]) >>
      imp_res_tac all_distinct_ntl >>       
      imp_res_tac all_distinct_sub >>
      imp_res_tac all_distinct_simp >>
      ‘ALL_DISTINCT (MAP FST simp_leaves')’ by (imp_res_tac all_distinct_determine >> gvs[]) >>        
      ‘ALL_DISTINCT (MAP FST new_edges)’ by (imp_res_tac all_distinct_mk_edges >> gvs[]) >>
      (*end*)
      
      ‘ALL_DISTINCT (MAP FST new_labels)’ by (imp_res_tac all_distinct_mk_labels >> gvs[])
      )>>        
    simp[ALL_DISTINCT_APPEND]>>
    
    strip_tac >> strip_tac >>
    ‘∃ updated_labels . non_term_leaf_updt labels h = updated_labels’ by gvs[] >>          
    imp_res_tac leaves_are_not_parents >>
                
    (*if in labels changed, then in labels, then from wfness in *)
    imp_res_tac_body >>
    
    ‘MEM e (MAP FST labels)’ by gvs[] >>
    rgs[range_c_def] >>
    imp_res_tac EVERY_MEM >>
    ‘c > e’ by gvs[EVERY_MEM] >>
    imp_res_tac counter_range_in_new_labels >>
    strip_tac >>
    res_tac >>
    DECIDE_TAC
  ]               
QED




(* if adding n in BDD is ok, we should also add it here*)
Theorem WFness_lookup_edges:
  ∀ r edges labels r'' edges'' labels'' h c c' n vars_consumed rec.
    range_c c (r,edges,labels) ∧
    BDD_WF (r,edges,labels) ∧
    body_of_mk rec (r,edges,labels) h c = SOME ((r'',edges'',labels''),c') ∧
    MEM n (dom_range_edges edges'') ∧
    edges ≠ []
    ⇒
    (lookup_is_some edges'' n ⇔ is_lookup_internal labels'' n)
Proof
  rpt strip_tac >>
  imp_res_tac WFness_distinct_edges_labels >>
  rgs[lookup_is_some_def, is_lookup_internal_def] >>                      
  imp_res_tac WFness_range_c_inter >>
  
  EQ_TAC >>
  rpt strip_tac >|[
    (* if it has edges then indeed the label (x,p)*)
    
    gvs[body_of_mk_def] >>
    gvs[AllCaseEqs()]>>
    body_of_mk_pred_tac >>
    rgs[ALOOKUP_APPEND] >>
    rgs[AllCaseEqs()]  >>
    PairCases_on ‘y’ >> rgs[]  >| [
      (*if in the newly created layer edges *)
        
        
      Cases_on ‘MEM n (dom_range_edges edges)’ >> rgs[] >|[
        
        Cases_on ‘ALOOKUP (non_term_leaf_updt labels h) n’ >>
        rpt (BasicProvers.FULL_CASE_TAC >> rgs[]) >> rgs[] >|[
          imp_res_tac lookup_ntl_updt_none >>   
          rgs[BDD_WF_def] >>
          rgs[is_lookup_ntl_def]              
          ,
          rgs[BDD_WF_def] >-
           (
           rgs[is_lookup_ntl_def]>>
           imp_res_tac lookup_labels_in_updt_none >>
           first_x_assum (strip_assume_tac o (Q.SPECL [‘h’])) >>
           rgs[]                 
           ) >>
          (* case terminal, we do not pick it up really, so it shouldn't satisfy the result,
             we should          show this subgoal by proving that in new_edges when looking up for n, then teh result should be none.
           *)
          (* we should show that n it is in leaves_labels , but not in ntl *)
          (
          rgs[is_lookup_internal_def, lookup_is_some_def] >>
          ‘ALOOKUP edges n = NONE’ by res_tac >>
          
          imp_res_tac lookup_labels_in_updt_term >>
          first_x_assum (strip_assume_tac o (Q.SPECL [‘h’])) >>
          rgs[] >>
          
          (* since n in new edges, then indeed it was in ntl*)
          subgoal ‘ ∃ p . ALOOKUP ntl n = SOME p’ >-
           (
           imp_res_tac_body >>
           rgs[] >>
           
           assume_tac (INST_TYPE [“:'a” |-> “:num” , “:'b” |-> “:(num#num)” , “:'c” |-> “:('a)” ] alookup_map_local_thm)  >>
           first_x_assum (strip_assume_tac o (Q.SPECL [‘new_edges’,‘ntl’,‘n’,‘(y0,y1)’])) >>
           gvs[]
           ) >>
          
          ‘∃ lbl . ALOOKUP leaves_labels n = SOME lbl’ by (imp_res_tac alookup_nonterm_exsists >> gvs[]) >>
          imp_res_tac mk_body_map2 >>
          ‘ALL_DISTINCT (MAP FST leaves_labels)’ by (rgs[BDD_WF_def] >> imp_res_tac_distinct) >>
          ‘lbl = non_termn (NONE,p')’ by imp_res_tac lbl_pred_rel_extract_nontermn >>
          rgs[] >>
          
          imp_res_tac mk_body_map1 >>
          rgs[] >>
          ‘ALOOKUP labels n = SOME (non_termn (NONE,p'))’ by imp_res_tac lookup_labels_of_leaves_same >>
          gvs[]
          )
        ]
          ,
          (* n not a mem of edges *)
          imp_res_tac get_leaves_in_nodes >>
          ‘ALOOKUP leaves_labels n = NONE’ by imp_res_tac not_in_leaves_not_in_res >>
          subgoal ‘ALOOKUP new_edges n = NONE’ >-
           (
           imp_res_tac_body >>
           rgs[ALOOKUP_NONE] >>
           imp_res_tac extract_nonterm_mem_neg >>
           gvs[]
           ) >>
          gvs[] 
        ] 
   
                                                           
      ,
      (*if in the old edges *) 
      Cases_on ‘MEM n (dom_range_edges edges)’ >> rgs[] >|[
          
          Cases_on ‘ALOOKUP (non_term_leaf_updt labels h) n’ >>
          rpt (BasicProvers.FULL_CASE_TAC >> rgs[]) >> rgs[] >|[
            (* This is imposisble *)
            rgs[BDD_WF_def] >>
            rgs[lookup_is_some_def, is_lookup_internal_def] >>
            ‘∃ x p . ALOOKUP labels n = SOME (non_termn (SOME x,p))’ by (res_tac >> gvs[]) >>
            imp_res_tac lookup_ntl_updt_none >>  
            gvs[] 
            ,
            imp_res_tac wf_lookup_if_edges_label >>
            imp_res_tac WF_imp_non_leaf_lbl >>
            rgs[] >>
            first_x_assum (strip_assume_tac o (Q.SPECL [‘h’])) >>
            rgs[]
               
          ]
          ,
          imp_res_tac lookup_edges_in_domain      
        ]
    ]                    
    ,
        
    (***** second part of implication *****)
    
    gvs[body_of_mk_def] >>
    gvs[AllCaseEqs()]>>
    body_of_mk_pred_tac >>
    rgs[ALOOKUP_APPEND] >>
    rgs[AllCaseEqs()] >| [
        (* n here is in the newly created labels and edges, basically from c *)     
        imp_res_tac new_labels_are_not_internal >>
        ‘ALL_DISTINCT (MAP FST simp_leaves')’ by (rgs[BDD_WF_def] >> imp_res_tac_distinct) >>         
        gvs[]
        ,

        Cases_on ‘ALOOKUP edges n’ >> rgs[] >>
        imp_res_tac lookup_non_term_leaf_updt_internal >|[
                    
            Cases_on ‘MEM n (dom_range_edges edges)’ >|[
              ‘ALL_DISTINCT (MAP FST edges)’ by (gvs[ALL_DISTINCT_APPEND]) >>
              ‘MEM n leaves’ by imp_res_tac leaves_in_get_leaves >>
              ‘ALOOKUP ntl n = SOME p’ by imp_res_tac leaves_in_ntl_lemma >>
      
              imp_res_tac_body >>
              rgs[MEM_MAP] >>
                           
              PairCases_on ‘y’ >>
              rgs[] >>
              imp_res_tac alookup_map_local_thm >>
              gvs[]
              ,
              rgs[] >>
              imp_res_tac get_leaves_in_nodes >>
              ‘ALOOKUP leaves_labels n = NONE’ by imp_res_tac not_in_leaves_not_in_res >>
              subgoal ‘ALOOKUP new_edges n = NONE’ >-
               (
               imp_res_tac_body >>
               rgs[ALOOKUP_NONE] >>
               imp_res_tac extract_nonterm_mem_neg >>
               gvs[]
               ) >>
              
              imp_res_tac dom_range_edges_in_sec >>
              
              Cases_on ‘ALOOKUP new_edges n’ >> rgs[] >>

                               
              (* tweaky way to solve this goal : first we know that n is indeed a cild,
              since it is a child, then indeed its node identifier larner than c,
              and this means in labels og this (n = c) which breaks the distinct, *)

              assume_tac (INST_TYPE [“:'a” |-> “:num”] leaf_parents_lookup)  >>
              ‘ALL_DISTINCT (MAP FST new_edges)’ by (gvs[ALL_DISTINCT_APPEND]) >>
              first_x_assum (strip_assume_tac o (Q.SPECL [‘new_edges’,‘n’])) >>
              rgs[] >>
                    
              (
              ‘ALL_DISTINCT (MAP FST (mk_new_labels simp_leaves' c))’ by (rgs[BDD_WF_def] >> imp_res_tac_distinct) >>
              ‘∃ lbl. ALOOKUP new_labels n = SOME lbl ’ by (imp_res_tac lookup_new_edges_labels_thm1 >> gvs[] ) >>
              
              ‘MEM (n,lbl) new_labels’ by (imp_res_tac ALOOKUP_MEM) >>
              ‘MEM (n,non_termn (SOME h,p)) (non_term_leaf_updt labels h)’ by (imp_res_tac ALOOKUP_MEM) >>
              imp_res_tac mem_fst_snd >>
              rgs[] >>
              
              rgs[ALL_DISTINCT_APPEND]
                )
                                                  
              ] 
            
                    
            ,
            Cases_on ‘MEM n (dom_range_edges edges)’ >|[
                rgs[BDD_WF_def] >>
                gvs[is_lookup_ntl_def]
                ,

                rgs[] >>
                imp_res_tac get_leaves_in_nodes >>
                ‘ALOOKUP leaves_labels n = NONE’ by imp_res_tac not_in_leaves_not_in_res >>
                subgoal ‘ALOOKUP new_edges n = NONE’ >-
                 (
                 imp_res_tac_body >>
                 rgs[ALOOKUP_NONE] >>
                 imp_res_tac extract_nonterm_mem_neg >>
                 gvs[]
                 ) >>
                
                imp_res_tac dom_range_edges_in_sec >>
                
                Cases_on ‘ALOOKUP new_edges n’ >> rgs[] >>
                
                
                (* tweaky way to solve this goal : first we know that n is indeed a cild,
                   since it is a child, then indeed its node identifier larner than c,
                   and this means in labels og this (n = c) which breaks the distinct, *)

                assume_tac (INST_TYPE [“:'a” |-> “:num”] leaf_parents_lookup)  >>
                ‘ALL_DISTINCT (MAP FST new_edges)’ by (gvs[ALL_DISTINCT_APPEND]) >>
                first_x_assum (strip_assume_tac o (Q.SPECL [‘new_edges’,‘n’])) >>
                rgs[] >>
                
                (
                ‘ALL_DISTINCT (MAP FST (mk_new_labels simp_leaves' c))’ by (rgs[BDD_WF_def] >> imp_res_tac_distinct) >>
                ‘∃ lbl. ALOOKUP new_labels n = SOME lbl ’ by (imp_res_tac lookup_new_edges_labels_thm1 >> gvs[]) >>
             (*   
                ‘MEM (n,non_termn (SOME x,p)) new_labels’ by (imp_res_tac ALOOKUP_MEM) >>
                ‘MEM (n,non_termn (SOME x,p)) (non_term_leaf_updt labels h)’ by (imp_res_tac ALOOKUP_MEM) >>
               *)
                imp_res_tac ALOOKUP_MEM >>
                imp_res_tac mem_fst_snd >>
                rgs[] >>
                
                rgs[ALL_DISTINCT_APPEND]
                   
                )
              ]                                           
          ]
      ]
  ]
QED





Theorem WFness_lookup_ntl:
  ∀ r edges labels r'' edges'' labels'' h c c' n vars_consumed rec.
    range_c c (r,edges,labels) ∧
    BDD_WF (r,edges,labels) ∧
    body_of_mk rec (r,edges,labels) h c = SOME ((r'',edges'',labels''),c') ∧
    MEM n (dom_range_edges edges'') ∧
    edges ≠ []
    ⇒
    (ALOOKUP edges'' n = NONE ⇔
        is_lookup_ntl labels'' n ∨
        ∃p b. ALOOKUP labels'' n = SOME (termn (b,p)))
Proof
  rpt strip_tac >>
  imp_res_tac WFness_distinct_edges_labels >>
  imp_res_tac WFness_range_c_inter >>
  
  rpt strip_tac >>
  rgs[is_lookup_ntl_def] >>                      
  
  EQ_TAC >|[
         
    rpt strip_tac >>
    gvs[body_of_mk_def] >>
    gvs[AllCaseEqs()]>>
    body_of_mk_pred_tac >>
    rgs[ALOOKUP_APPEND] >>
    rgs[AllCaseEqs()]  >>
    Cases_on ‘ALOOKUP (non_term_leaf_updt labels h) n’  >> rgs[] >|[
             
      Cases_on ‘MEM n (dom_range_edges edges)’ >|[
        rgs[BDD_WF_def] >>
        last_x_assum (strip_assume_tac o (Q.SPECL [‘n’])) >>
        rgs[is_lookup_ntl_def] >> 
        imp_res_tac lookup_ntl_updt_none >>
        gvs[]
        ,
        Cases_on ‘ALOOKUP new_labels n’ >> rgs[] >| [
            rgs[] >>
            imp_res_tac get_leaves_in_nodes >>
            ‘ALOOKUP leaves_labels n = NONE’ by imp_res_tac not_in_leaves_not_in_res >>
            subgoal ‘ALOOKUP new_edges n = NONE’ >-
             (
             imp_res_tac_body >>
             rgs[ALOOKUP_NONE] >>
             imp_res_tac extract_nonterm_mem_neg >>
             gvs[]
             ) >>
            
            imp_res_tac dom_range_edges_in_sec >>
            
            Cases_on ‘ALOOKUP new_edges n’ >> rgs[] >>
            
            
            (* tweaky way to solve this goal : first we know that n is indeed a cild,
               since it is a child, then indeed its node identifier larner than c,
               and this means in labels og this (n = c) which breaks the distinct, *)
            
            assume_tac (INST_TYPE [“:'a” |-> “:num”] leaf_parents_lookup)  >>
            ‘ALL_DISTINCT (MAP FST new_edges)’ by (gvs[ALL_DISTINCT_APPEND]) >>
            first_x_assum (strip_assume_tac o (Q.SPECL [‘new_edges’,‘n’])) >>
            rgs[] >>
            
            (
            ‘ALL_DISTINCT (MAP FST (mk_new_labels simp_leaves' c))’ by (rgs[BDD_WF_def] >> imp_res_tac_distinct) >>
            ‘∃ lbl. ALOOKUP new_labels n = SOME lbl ’ by (imp_res_tac lookup_new_edges_labels_thm1 >> gvs[]) >>
            imp_res_tac ALOOKUP_MEM >>
            imp_res_tac mem_fst_snd >>
            rgs[] >>
            rgs[ALL_DISTINCT_APPEND]
            )
            ,
                
            Cases_on ‘x’ >> rgs[] >>
            
            imp_res_tac_body >>
            imp_res_tac new_labels_are_not_internal >>
            imp_res_tac get_leaves_in_nodes >>
            PairCases_on ‘p’ >> rgs[] >>
            Cases_on ‘p0’ >> rgs[] >>
            ‘MEM n (dom_range_edges new_edges)’ by imp_res_tac dom_range_edges_in_sec >>
                 

            assume_tac (INST_TYPE [“:'a” |-> “:num”] leaf_parents_lookup)  >>
            ‘ALL_DISTINCT (MAP FST new_edges)’ by (rgs[BDD_WF_def] >> imp_res_tac_distinct) >>
            first_x_assum (strip_assume_tac o (Q.SPECL [‘new_edges’,‘n’])) >>
            rgs[]                         
          ]
      ]
      
      ,
        
      (* this is obviously false, we should show that it is never the case*)
      
               
      Cases_on ‘x’ >> rgs[] >>
      PairCases_on ‘p’ >> rgs[] >>
      Cases_on ‘p0’ >> rgs[] >>
      
      imp_res_tac lookup_non_term_leaf_updt_internal >|[
          Cases_on ‘MEM n (dom_range_edges edges)’ >|[

            ‘ALL_DISTINCT (MAP FST edges)’ by (gvs[ALL_DISTINCT_APPEND]) >>
            ‘MEM n leaves’ by (imp_res_tac leaves_in_get_leaves >> metis_tac[]) >>
            ‘ALOOKUP ntl n = SOME p1’ by imp_res_tac leaves_in_ntl_lemma >>
            
            imp_res_tac_body >>
            rgs[MEM_MAP] >>
                           
            PairCases_on ‘y’ >>
            rgs[] >>
            imp_res_tac alookup_map_local_thm >>
            gvs[]
            ,


            rgs[] >>
            imp_res_tac get_leaves_in_nodes >>
            ‘ALOOKUP leaves_labels n = NONE’ by imp_res_tac not_in_leaves_not_in_res >>
            subgoal ‘ALOOKUP new_edges n = NONE’ >-
             (
             imp_res_tac_body >>
             rgs[ALOOKUP_NONE] >>
             imp_res_tac extract_nonterm_mem_neg >>
             gvs[]
             ) >>
              
            imp_res_tac dom_range_edges_in_sec >>
            
            Cases_on ‘ALOOKUP new_edges n’ >> rgs[] >>
            
            assume_tac (INST_TYPE [“:'a” |-> “:num”] leaf_parents_lookup)  >>
            ‘ALL_DISTINCT (MAP FST new_edges)’ by (gvs[ALL_DISTINCT_APPEND]) >>
            first_x_assum (strip_assume_tac o (Q.SPECL [‘new_edges’,‘n’])) >>
            rgs[] >>
            
            (
            ‘ALL_DISTINCT (MAP FST (mk_new_labels simp_leaves' c))’ by (rgs[BDD_WF_def] >> imp_res_tac_distinct) >>
            ‘∃ lbl. ALOOKUP new_labels n = SOME lbl ’ by (imp_res_tac lookup_new_edges_labels_thm1 >> gvs[] ) >>
            
            ‘MEM (n,lbl) new_labels’ by (imp_res_tac ALOOKUP_MEM) >>
            ‘MEM (n,non_termn (SOME h,p1)) (non_term_leaf_updt labels h)’ by (imp_res_tac ALOOKUP_MEM) >>
            imp_res_tac mem_fst_snd >>
            rgs[] >>
            
            rgs[ALL_DISTINCT_APPEND]
            )
          ]
          ,

          Cases_on ‘MEM n (dom_range_edges edges)’ >|[
              rgs[BDD_WF_def] >>
              gvs[is_lookup_ntl_def]
              ,
              rgs[] >>
              imp_res_tac get_leaves_in_nodes >>
              ‘ALOOKUP leaves_labels n = NONE’ by imp_res_tac not_in_leaves_not_in_res >>
              subgoal ‘ALOOKUP new_edges n = NONE’ >-
               (
               imp_res_tac_body >>
               rgs[ALOOKUP_NONE] >>
               imp_res_tac extract_nonterm_mem_neg >>
               gvs[]
               ) >>
              
              imp_res_tac dom_range_edges_in_sec >>
              
              Cases_on ‘ALOOKUP new_edges n’ >> rgs[] >>
              assume_tac (INST_TYPE [“:'a” |-> “:num”] leaf_parents_lookup)  >>
              ‘ALL_DISTINCT (MAP FST new_edges)’ by (gvs[ALL_DISTINCT_APPEND]) >>
              first_x_assum (strip_assume_tac o (Q.SPECL [‘new_edges’,‘n’])) >>
              rgs[] >>
              
              (
              ‘ALL_DISTINCT (MAP FST (mk_new_labels simp_leaves' c))’ by (rgs[BDD_WF_def] >> imp_res_tac_distinct) >>
              ‘∃ lbl. ALOOKUP new_labels n = SOME lbl ’ by (imp_res_tac lookup_new_edges_labels_thm1 >> gvs[]) >>
              imp_res_tac ALOOKUP_MEM >>
              imp_res_tac mem_fst_snd >>
              rgs[] >>
              
              rgs[ALL_DISTINCT_APPEND]
                 
              )
            ]
        ]
    ]
                                                                   
                                                                   
    ,
    
    
    (* other side of equality *)
    gvs[body_of_mk_def] >>
    gvs[AllCaseEqs()]>>
    body_of_mk_pred_tac >>
    rgs[ALOOKUP_APPEND] >>
    rgs[AllCaseEqs()]  >>
    Cases_on ‘ALOOKUP (non_term_leaf_updt labels h) n’ >> rgs[] >|[
        
        imp_res_tac lookup_ntl_updt_none >>
     
        Cases_on ‘MEM n (dom_range_edges edges)’ >> rgs[] >|[
          rgs[BDD_WF_def] >>
          rgs[lookup_is_some_def, is_lookup_internal_def] >>
          first_x_assum (strip_assume_tac o (Q.SPECL [‘n’])) >>
          rgs[] >>
          Cases_on ‘ALOOKUP edges n’ >> rgs[] >>
          rgs[is_lookup_ntl_def]
          ,

          imp_res_tac dom_range_edges_none >>
          Cases_on ‘ALOOKUP new_labels n’ >> rgs[] >>

          
          rgs[] >>
          imp_res_tac get_leaves_in_nodes >>
          ‘ALOOKUP leaves_labels n = NONE’ by imp_res_tac not_in_leaves_not_in_res >>
          subgoal ‘ALOOKUP new_edges n = NONE’ >-
           (
           imp_res_tac_body >>
           rgs[ALOOKUP_NONE] >>
           imp_res_tac extract_nonterm_mem_neg >>
           gvs[]
           ) >>
          
          gvs[]  
        ]
                                                            
        ,
        
        Cases_on ‘x’ >> rgs[] >>
        Cases_on ‘p’ >> rgs[] >| [
            (*termn*)
            ‘ALL_DISTINCT (MAP FST (non_term_leaf_updt labels h))’ by (gvs[ALL_DISTINCT_APPEND]) >>
            imp_res_tac non_term_leaf_updt_imp_term >>
            Cases_on ‘MEM n (dom_range_edges edges)’ >> rgs[] >|[
              rgs[BDD_WF_def] >>
              
              rgs[lookup_is_some_def, is_lookup_internal_def] >>
              first_x_assum (strip_assume_tac o (Q.SPECL [‘n’])) >>
              rgs[] >>
              
              (*then it should be in leafs*)
              ‘ALOOKUP edges n= NONE’ by (Cases_on ‘ALOOKUP edges n’ >> rgs[]) >>
              ‘MEM n leaves’ by imp_res_tac leaves_in_get_leaves >>
              
              Cases_on ‘ALOOKUP new_edges n’ >> rgs[] >>
              
              ‘ALL_DISTINCT (MAP FST leaves_labels)’ by (rgs[BDD_WF_def] >> imp_res_tac_distinct) >>
              imp_res_tac mk_body_map1 >>
                          
              ‘ALOOKUP leaves_labels n = SOME (termn (q,r'))’ by imp_res_tac leaves_labels_same_in_labels_some >>
                       
              ‘ALOOKUP ntl n = NONE’ by imp_res_tac term_not_in_ntl >>
              imp_res_tac_body >>
              imp_res_tac ALOOKUP_MEM >>
              imp_res_tac ALOOKUP_NONE >>
              imp_res_tac mem_fst_snd >>
              rgs[] 
              ,
              imp_res_tac get_leaves_in_nodes >>
              ‘ALOOKUP leaves_labels n = NONE’ by imp_res_tac not_in_leaves_not_in_res >>
              subgoal ‘ALOOKUP new_edges n = NONE’ >-
               (
               imp_res_tac_body >>
               rgs[ALOOKUP_NONE] >>
               imp_res_tac extract_nonterm_mem_neg >>
               gvs[]
               ) >>
              imp_res_tac dom_range_edges_in_sec >>
              
              Cases_on ‘ALOOKUP new_edges n’ >> rgs[] >>
              
              assume_tac (INST_TYPE [“:'a” |-> “:num”] leaf_parents_lookup)  >>
              ‘ALL_DISTINCT (MAP FST new_edges)’ by gvs[ALL_DISTINCT_APPEND] >>
              first_x_assum (strip_assume_tac o (Q.SPECL [‘new_edges’,‘n’])) >>
              rgs[] >>
              
              (
              ‘ALL_DISTINCT (MAP FST (mk_new_labels simp_leaves' c))’ by (rgs[BDD_WF_def] >> imp_res_tac_distinct) >>
              ‘∃ lbl. ALOOKUP new_labels n = SOME lbl ’ by (imp_res_tac lookup_new_edges_labels_thm1 >> gvs[]) >>
              imp_res_tac ALOOKUP_MEM >>
              imp_res_tac mem_fst_snd >>
              rgs[] >>
              rgs[ALL_DISTINCT_APPEND]
              )
              
            ]
                                                                
            ,
            (*non termn*)
            strip_tac >>
            ‘ALL_DISTINCT (MAP FST (non_term_leaf_updt labels h))’ by gvs[ALL_DISTINCT_APPEND] >>
            imp_res_tac non_term_leaf_updt_imp_not_ntl >>
            Cases_on ‘q’ >> gvs[]
          ]                  
      ]
  ]      
QED

 














     
        

Theorem wf_edges_root_mkbody_imp_wf:
  ∀ r edges labels r'' edges'' labels'' rec c c' h.
    BDD_WF ((r,[],labels):('a,'b)BDD) ∧
    ALL_DISTINCT (MAP FST edges'') ∧
    ALL_DISTINCT (MAP FST labels'') ∧
    body_of_mk rec (r,[],labels) h c = SOME ((r'',edges'',labels''),c') ⇒
    BDD_WF (r'',edges'',labels'')
Proof
  rpt strip_tac >>      
  simp[BDD_WF_def] >> CONJ_TAC >>  
  rpt strip_tac >>
  
  rpt strip_tac >>        
  rgs[body_of_mk_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>

  rgs[BDD_WF_def, dom_range_edges_def] >>
  rgs[getLeaves_def, getLabels_def] >>
  Cases_on ‘p’ >>
  rgs[non_term_leaf_updt_def] >>

  Cases_on ‘p'’ >>
  gvs[AllCaseEqs()] >>
  gvs[is_lookup_ntl_def,lookup_is_some_def,is_lookup_internal_def] >>
  gvs[AllCaseEqs()] >>
  gvs[getLabels_def, extract_nontermn_def, leaves_pred_sub_def] >>
  gvs[simp_pred_list_def, mk_new_labels_def, mk_new_edges_def] >>
  gvs[determine_termn_list_def] >>
  gvs[AllCaseEqs()] >>
  gvs[mk_new_labels_def, mk_new_edges_def] >>             

  rgs[determine_termn_def] >>
  rgs[AllCaseEqs()] >>
  
  Cases_on ‘rec.final (rec.simp (rec.sub r' h T))’ >> gvs[] >>
  Cases_on ‘rec.final (rec.simp (rec.sub r' h F))’ >> gvs[]
QED

        
        
        
Theorem WFness_translation_inter:
  ∀ (BDD:('a,'b)BDD) BDD'' rec c c' h.
    range_c c BDD ∧
    BDD_WF BDD  ∧
    body_of_mk rec BDD h c = SOME (BDD'',c') ⇒
    BDD_WF BDD''
Proof
  rpt strip_tac >>
  
  PairCases_on ‘BDD’ >>
  rename1 ‘(r,edges,labels)’ >>
  
  PairCases_on ‘BDD''’ >>
  rename1 ‘(r'',edges'',labels'')’ >>
  
  imp_res_tac WFness_distinct_edges_labels >>
  Cases_on ‘edges = []’ >|[
    metis_tac[wf_edges_root_mkbody_imp_wf]
    ,
    simp[BDD_WF_def] >> CONJ_TAC >> rpt strip_tac >|[
         metis_tac[WFness_lookup_edges]
        ,
        metis_tac[WFness_lookup_ntl]
        ,
        gvs[] >>
        rpt strip_tac >>        
        gvs[body_of_mk_def] >>
        rpt (BasicProvers.FULL_CASE_TAC >> gvs[])
      ] 
  ]
QED


   
       
Theorem WFness_translation:
  ∀ vars rec vars_consumed (BDD:('a,'b)BDD) BDD' c.
    range_c c BDD ∧
    BDD_WF BDD ⇒
    (SOME BDD' = mk_BDDPred rec BDD vars_consumed vars c) ⇒
    BDD_WF BDD' 
Proof
  Induct >| [
    rpt strip_tac >>
    PairCases_on ‘BDD’ >> gvs[] >>
    gvs[mk_BDDPred_def]
    ,
    rpt strip_tac >>
    
    PairCases_on ‘BDD’ >>
    rename1 ‘(r,edges,labels)’ >>
    
    PairCases_on ‘BDD'’ >>
    rename1 ‘(r',edges',labels')’ >>
    
    gvs[mk_BDDPred_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>           
    PairCases_on ‘q’ >>
                 
    ‘BDD_WF (q0,q1,q2)’ by imp_res_tac WFness_translation_inter >>
    ‘range_c r'' (q0,q1,q2)’ by imp_res_tac WFness_range_c_inter >>
    res_tac
]    
QED



val _ = export_theory ();

















