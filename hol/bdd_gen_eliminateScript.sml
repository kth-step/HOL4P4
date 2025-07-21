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

open bdd_gen_mergeTheory;

val _ = new_theory "bdd_gen_eliminate";

   
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
    eliminable (r,edges,labels) n n' ⇒
    ∃ x p . ALOOKUP labels n'= SOME (non_termn(SOME x,p)) 
Proof
  rpt strip_tac >>
  rgs[eliminable_def] >>
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
     




                

Theorem eliminable_correct_internal:
  ∀ x vars_consumed vars r edges labels n n' n'' nl nr pred mv b rec.
    consumed_dom_bdd vars_consumed (r,edges,labels) ∧
    fv_in_BDD rec (r,edges,labels) (vars ⧺ vars_consumed) ∧
    mv_dom_vars mv (vars ⧺ vars_consumed) ∧
    BDD_ordered (r,edges,labels) vars_consumed ∧
    BDD_WF (r,edges,labels) ∧
    eliminable (r,edges,labels) n n' ∧
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
          gvs[eliminable_def] >>
          
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
          gvs[eliminable_def] >>
          
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
        


 

Theorem eliminable_correct_eq:
  ∀labels vars vars_consumed n'' r edges n' n mv b rec.
    consumed_dom_bdd vars_consumed (r,edges,labels) ∧
    fv_in_BDD rec (r,edges,labels) (vars++vars_consumed) ∧
    mv_dom_vars mv (vars ⧺ vars_consumed) ∧
    BDD_ordered (r,edges,labels) vars_consumed ∧
    BDD_WF (r,edges,labels) ∧
    eliminable (r,edges,labels) n n' ∧ n'' ≠ n' ⇒
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

     
   metis_tac[eliminable_correct_internal]
  ]
QED





        
                           
                
 (* merge = eliminate defs*)       
Theorem eliminate_correct_bdd_exracted:        
  ∀ r edges labels vars vars_consumed n n' rec .
    correct_sem rec (r,edges,labels) (vars++vars_consumed) ∧
    BDD_WF (r,edges,labels) ∧
    consumed_dom_bdd vars_consumed (r,edges,labels) ∧
    BDD_ordered (r,edges,labels) vars_consumed ∧
    fv_in_BDD rec (r,edges,labels) (vars++vars_consumed)  ∧
    eliminable (r,edges,labels) n n'
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
    assume_tac eliminable_correct_eq >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘labels’, ‘vars’, ‘vars_consumed’, ‘n''’, ‘r’, ‘edges’, ‘n'’, ‘n’, ‘mv’, ‘b’, ‘rec’])) >>
    gvs[] >>
    
    gvs[correct_sem_def] >>
    res_tac >>
    
    metis_tac[op_sem_adel_key]
  ]
QED



Theorem eliminate_correct:        
  ∀ BDD vars vars_consumed n n' rec .
    correct_sem rec BDD (vars++vars_consumed) ∧
    BDD_WF BDD ∧
    consumed_dom_bdd vars_consumed BDD ∧
    BDD_ordered BDD vars_consumed ∧
    fv_in_BDD rec BDD (vars++vars_consumed)  ∧
    eliminable BDD n n'
    ==>
    correct_sem rec (merge BDD n n')  (vars++vars_consumed)
Proof
  rpt strip_tac >>
  rw[] >>
  
  PairCases_on ‘BDD’ >>
  rename1 ‘(root, edges, labels)’ >>
 metis_tac[eliminate_correct_bdd_exracted]
QED

(*

EVAL “mergable (0,[(0,1,2)],
        [(0,non_termn (SOME "a",Or (Var "a") (Not (Var "a"))));
         (1,termn (T,True)); (2,termn (T,True))]) 1 2”


EVAL “merge (0,[(0,1,2)],
        [(0,non_termn (SOME "a",Or (Var "a") (Not (Var "a"))));
         (1,termn (T,True)); (2,termn (T,True))]) 1 2” 



EVAL “eliminable (0,[(0,1,1)],
      [(0,non_termn (SOME "a",Or (Var "a") (Not (Var "a"))));
       (1,termn (T,True))]) 1 0” 
        
EVAL “merge (0,[(0,1,1)],
      [(0,non_termn (SOME "a",Or (Var "a") (Not (Var "a"))));
       (1,termn (T,True))]) 1 0” 

*)

(*
EVAL “is_unique_var [(1,non_termn (SOME "x",p));(2,non_termn (SOME "x",p))] (1:num)” 
*)


        
        
Theorem list_eliminated_flat_membership2:
  ∀ t n n' n'' b c.
    n'' ≠ n' ∧
    n ≠ n' ∧
    ALL_DISTINCT (MAP FST t) ∧
    MEM n'' (flat_edges t) ∧
    MEM (n',n,n) t ∧
    MEM (n,b,c) t ⇒
    MEM n'' (flat_edges (FILTER (λp. FST p ≠ n') t))
Proof

rpt strip_tac >>
rw[] >>
Cases_on ‘n''=n’ >> fs[] >|[
    irule flat_edges_mem_triv4 >>
    srw_tac [SatisfySimps.SATISFY_ss][]
    ,
    irule list_not_merged_flat_membership2 >>
    srw_tac [SatisfySimps.SATISFY_ss][]
  ]
QED





        

        
                                           
Theorem eliminate_dom_range_edges3_imp_adel_key_mem:
  ∀edges root labels vars n n' n'' a b.
    n'' ≠ n' ∧ n ≠ n' ∧
    BDD_ordered (root,edges,labels) vars ∧
    ALL_DISTINCT (MAP FST edges) ∧
    MEM (n',n,n) edges ∧
    MEM (n,a,b) edges ∧
    MEM n (dom_range_edges3 edges) ∧  (* can be inferred later *)
    MEM n'' (dom_range_edges3 (merge_edges edges n n')) ⇒
    MEM n'' (dom_range_edges3 (ADELKEY n' (merge_edges edges n n')))
Proof
  rpt strip_tac >> 
  ‘(n ≠ a ∧ n ≠ b ∧ n'' ≠ a ∧ n'' ≠ b)’ by cheat >>
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
      
      fs[merge_edges_def]
      ,
        
      fs[Once merge_edges_list_normalize] >>
      qpat_x_assum ‘merge_edges [(n,a,b)] n n' = [(h0,h1,h2)]’
                   (fn thm => assume_tac (SIMP_RULE (srw_ss()) [merge_edges_def] thm)) >>
      
      Cases_on ‘a = n' ∧ b = n'’ >> fs[] >>
      Cases_on ‘a = n'’ >> fs[] >>
      Cases_on ‘b = n'’ >> fs[] >>
               
      rgs[flat_edges_def]  >>
      irule list_not_merged_flat_membership2 >> fs[] >>

      FIRST [
          subgoal ‘MEM (a,h0,h0) t ’ >- ( metis_tac[merge_edges_membership] ) >>
          srw_tac [SatisfySimps.SATISFY_ss][]
          ,
          
          subgoal ‘MEM (b,h0,h0) t ’ >- ( metis_tac[merge_edges_membership] ) >>
          srw_tac [SatisfySimps.SATISFY_ss][]
          ,
          subgoal ‘MEM (n',h0,h0) t ’ >- ( metis_tac[merge_edges_membership] ) >>
          srw_tac [SatisfySimps.SATISFY_ss][]
        ]
      ,

      PairCases_on ‘h’ >>
      fs[Once merge_edges_list_normalize] >>

      qpat_x_assum ‘merge_edges [(h0',h1',h2')] n n' = [(h0,h1,h2)]’
                   (fn thm => assume_tac (SIMP_RULE (srw_ss()) [merge_edges_def] thm)) >>
      
      Cases_on ‘h1' = n' ∧ h2' = n'’ >> 
      Cases_on ‘h1' = n'’ >> 
      Cases_on ‘h2' = n'’ >> fs[]  >|[
              
          fs[flat_edges_def] >-
           metis_tac[mem_triple_map_fst] >>
          
          subgoal ‘MEM (n',h1,h1) t ’ >- ( metis_tac[merge_edges_membership] ) >>
          rgs[] >> 
          irule list_not_merged_flat_membership2 >>
          metis_tac[]
          ,

          fs[flat_edges_def] >>
          imp_res_tac mem_triple_map_fst >>
          irule list_not_merged_flat_membership2 >>
          
          FIRST  [
              subgoal ‘MEM (h1',h1,h1) t ’ >- ( metis_tac[merge_edges_membership] ) >>
              metis_tac[]
              ,
              subgoal ‘MEM (n',h1,h1) t ’ >- ( metis_tac[merge_edges_membership] ) >>
              metis_tac[]
            ] 
            
          ,
                
          fs[flat_edges_def] >>
          imp_res_tac mem_triple_map_fst >>
          irule list_not_merged_flat_membership2 >> fs[] >>

          FIRST [
              subgoal ‘MEM (n',h1,h1) t ’ >- ( metis_tac[merge_edges_membership] ) >>  
              metis_tac[]
              ,
              subgoal ‘MEM (n',h2,h2) t ’ >- ( metis_tac[merge_edges_membership] ) >>  
              metis_tac[]
            ]
          ,
          fs[flat_edges_def] >>
          imp_res_tac mem_triple_map_fst >> fs[] >|[
              
              subgoal ‘MEM (n',h1,h1) t ’ >- ( metis_tac[merge_edges_membership] ) >>  
              irule list_not_merged_flat_membership2 >> 
              metis_tac[]
              ,
              subgoal ‘MEM (n',h1,h1) t ’ >- ( metis_tac[merge_edges_membership] ) >>  
              irule list_not_merged_flat_membership2 >> 
              metis_tac[]
              ,
              subgoal ‘MEM (n',h2,h2) t ’ >- ( metis_tac[merge_edges_membership] ) >>  
              irule list_not_merged_flat_membership2 >> 
              metis_tac[]
              ,
              subgoal ‘MEM (n',n,n) t ’ >- ( metis_tac[merge_edges_membership] ) >>
              ‘∃ b'' c'' . MEM (n,b'',c'') t’ by metis_tac[head_mem_not_changed_in_merge] >>
              irule list_eliminated_flat_membership2 >> 
              srw_tac [SatisfySimps.SATISFY_ss][]
            ]
                                                   
        ]
    ]
    ,
    
    (* because of distinct we know that h1 and h2 are equal to n and n from merge def*)
    assume_tac merge_normalize_for_mergable_nodes_concrete >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘edges’, ‘t’, ‘h0’, ‘h1’, ‘h2’, ‘n’, ‘n’, ‘n’])) >>
    gvs[] >>
    
    ‘¬ MEM (h0,n,n) t’ by gvs[] >> (* from ∀y. h0 = FST y ⇒ ¬MEM y t*)
    ‘¬MEM h0 (MAP FST t)’ by gvs[MEM_MAP] >>

    Cases_on ‘edges = []’ >> gvs[] >>
    Cases_on ‘edges’ >> gvs[] >|[
        
        rgs[Once merge_edges_list_normalize] >>
        rgs[flat_edges_def] >>
        imp_res_tac mem_triple_map_fst >>
        irule list_not_merged_flat_membership1 >> fs[] >>
        ‘∃ b'' c'' . MEM (h1, b'',c'') t’ by metis_tac[head_mem_not_changed_in_merge] >>
        ‘MEM h1 (MAP FST t)’ by ( imp_res_tac mem_triple_map_fst ) >>
        metis_tac[mem_input_then_in_flattened]

        ,
        
        rgs[Once merge_edges_list_normalize] >>
        rgs[flat_edges_def] >>
        irule list_not_merged_flat_membership1 >|[
            subgoal ‘MEM (h0,h1,h1) t ’ >- ( metis_tac[merge_edges_membership] ) >>
            gvs[]
            ,
            gvs[]
          ]
        ,
        rgs[Once merge_edges_list_normalize] >>
        rgs[flat_edges_def] >|[
            (* by contr because h0 is in n0*)
            subgoal ‘MEM (h0,h1,h1) t ’ >- ( metis_tac[merge_edges_membership] ) >>
            imp_res_tac mem_triple_map_fst
            ,
            irule list_not_merged_flat_membership1 >>
            gvs[]

          ]

      ] 
  ]

QED      


            

         
Theorem eliminate_dom_range_edges_imp_adel_key_mem:
  ∀edges root labels vars n n' n'' a b.
    n'' ≠ n' ∧ n ≠ n' ∧ BDD_ordered (root,edges,labels) vars ∧
    ALL_DISTINCT (MAP FST edges) ∧
    MEM (n',n,n) edges ∧ MEM (n,a,b) edges ∧
    MEM n (dom_range_edges edges) ∧
    MEM n'' (dom_range_edges (merge_edges edges n n')) ⇒
    MEM n'' (dom_range_edges (ADELKEY n' (merge_edges edges n n')))
Proof
  fs[GSYM dom_range_edges1_3_eq] >>
  metis_tac[eliminate_dom_range_edges3_imp_adel_key_mem]
QED


Theorem flat_edges_mem_exists_trivial:
  ∀ l n''.
    MEM n'' (flat_edges l) ⇒
    (∃k v1 v2. MEM (k,v1,v2) l ∧ (n'' = k ∨ n'' = v1 ∨ n'' = v2))
Proof
  Induct >> rw[flat_edges_def] >>
  rpt strip_tac >>
  PairCases_on ‘h’ >> gvs[] >>
  gvs[flat_edges_def] >> 
  metis_tac[]  
QED

  

Theorem flat_edges_normalization:
  ∀ l n a b c .        
    MEM n (flat_edges ((a,b,c)::l)) =  (MEM n (flat_edges ([a,b,c])) ∨ MEM n (flat_edges l))
Proof
  rw[flat_edges_def] >>
  metis_tac[]
QED

        

Theorem has_parent_imp_exsists:
  ∀edges n n'.
    ALL_DISTINCT (MAP FST edges) ∧
    has_parent edges n n' ⇒
    ∃parent left right. MEM (parent, left, right) edges ∧ 
                        (left = n' ∨ right = n') ∧ 
                        parent ≠ n' ∧  parent ≠ n
Proof
  rw[has_parent_def, EXISTS_DEF] >>
  gvs[EXISTS_MEM] >>
  qexistsl_tac [‘FST e’, ‘FST(SND e)’ ,‘SND (SND e)’] >>                     
  PairCases_on ‘e’ >> 
  gvs[] 
QED

         



Theorem list_eliminated_flat_membership3:
  ∀ l a n n'' parent right left.
    n'' ≠ a ∧  parent ≠ a ∧
    ALL_DISTINCT (MAP FST l) ∧
    MEM n'' (flat_edges l) ∧
    MEM (a,n,n) l ∧
    (MEM (parent,n,right) l ∨ MEM (parent,left,n) l) ⇒
    MEM n'' (flat_edges (FILTER (λp. FST p ≠ a) l))
Proof

  rpt strip_tac >>
  rw[] >>
  Cases_on ‘n''=n’ >> gvs[] >|[
    
    irule flat_edges_mem_triv5 >>
    srw_tac [SatisfySimps.SATISFY_ss][]
    ,
    irule list_not_merged_flat_membership2 >>
    srw_tac [SatisfySimps.SATISFY_ss][]
    ,
    irule flat_edges_mem_triv6 >>
    srw_tac [SatisfySimps.SATISFY_ss][]
    ,
    irule list_not_merged_flat_membership2 >>
    srw_tac [SatisfySimps.SATISFY_ss][]
  ]
QED




Theorem MEM_LOOKUP_trio:
  ∀ l a b c n n'.        
    ALL_DISTINCT (MAP FST l) ∧
    MEM (a,b,c) l ⇒
    ALOOKUP l a = SOME (b,c)     
Proof                     
  Induct >> gvs[] >>
  rpt strip_tac >>
  Cases_on ‘h’ >> fs[] >>
  Cases_on ‘q=a’ >> fs[] >>
  imp_res_tac mem_triple_map_fst
QED



Theorem eliminate_snd_edges_membership:
  ∀ l l' n n' a b h.
    b = n' ∧
    ALL_DISTINCT (MAP FST l) ∧
    MEM (n,a,b) l ∧
    merge_edges l h n' = l' ⇒
    ∃ a' . MEM (n,a',h) l'
Proof
  Induct_on ‘l’ >>
  rpt strip_tac >-
   gvs[merge_edges_def, MEM_MAP]  >>
  PairCases_on ‘h’ >>
  fs[] >|[
    
    gvs[merge_edges_def, MEM_MAP]  >>
    Cases_on ‘b=a’ >> gvs[] >|[
      qexists_tac ‘h'’ >> gvs[]
      ,
      qexists_tac ‘a’ >> gvs[]
    ]
    ,
    rgs[Once merge_edges_list_cons] >>
    res_tac >>
    gvs[] >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘h'’])) >>
    qexists_tac ‘a'’ >> gvs[]
  ]
QED




Theorem eliminate_fst_edges_membership:
  ∀ l l' n n' a b h.
    a = n' ∧
    ALL_DISTINCT (MAP FST l) ∧
    MEM (n,a,b) l ∧
    merge_edges l h n' = l' ⇒
    ∃ b' . MEM (n,h,b') l'
Proof
  Induct_on ‘l’ >>
  rpt strip_tac >-
   gvs[merge_edges_def, MEM_MAP]  >>
  PairCases_on ‘h’ >>
  fs[] >|[
    
    gvs[merge_edges_def, MEM_MAP]  >>
    Cases_on ‘b=a’ >> gvs[] >|[
      qexists_tac ‘h'’ >> gvs[]
      ,
      qexists_tac ‘b’ >> gvs[]
    ]
    ,
    rgs[Once merge_edges_list_cons] >>
    res_tac >>
    gvs[] >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘h'’])) >>
    qexists_tac ‘b'’ >> gvs[]
  ]
QED










        
    
Theorem eliminate_dom_range_edges3_imp_adel_key_mem_none:
  ∀ edges n n' n''.
    n'' ≠ n' ∧ n ≠ n' ∧
    has_parent edges n n' ∧
    ALL_DISTINCT (MAP FST edges) ∧
    ALOOKUP edges n = NONE ∧
    ALOOKUP edges n' = SOME (n,n) ∧
    MEM n'' (dom_range_edges3 (merge_edges edges n n'))
    ⇒
    MEM n'' (dom_range_edges3 (ADELKEY n' (merge_edges edges n n')))
Proof
  rw[] >>
  gvs[dom_range_edges3_def] >>
  gvs[MEM_MAP, ADELKEY_def, MEM_FILTER] >>
  ‘ALL_DISTINCT (MAP FST (merge_edges edges n n')) ’ by metis_tac [all_distinct_fst_merge_edges] >>

  gvs[ALOOKUP_NONE] >>
  imp_res_tac ALOOKUP_MEM >>
  imp_res_tac mem_triple_map_fst >>
  imp_res_tac mem_input_then_in_flattened >>
  
  Cases_on ‘(merge_edges edges n n') = []’ >-
   gvs[flat_edges_def] >>
  Cases_on ‘(merge_edges edges n n')’ >-
   gvs[flat_edges_def] >>
  PairCases_on ‘h’ >>
  
  gvs[MEM_MAP, ADELKEY_def, MEM_FILTER] >>
  rpt(BasicProvers.FULL_CASE_TAC >> gvs[ALOOKUP_MEM, ALOOKUP_NONE]) >|[
    
    PairCases_on ‘y’ >>
    rename1 ‘MEM (a,b,c) edges’ >>
    subgoal ‘n=b ∧ n=c’ >- (imp_res_tac MEM_LOOKUP_trio >> gvs[]) >>
    
    gvs[flat_edges_def] >>
    Cases_on ‘n'' = h0 ∨ n'' = h1 ∨ n'' = h2’ >> gvs[] >>
    
    Cases_on ‘edges’ >> gvs[] >|[
      fs[merge_edges_def]
      ,
      PairCases_on ‘h’ >>
      rgs[Once merge_edges_list_normalize] >>
      rgs[Once merge_edges_def] >>
      
      Cases_on ‘h1' = a ∧ h2' = a’ >> fs[] >> 
      Cases_on ‘h1' = a’ >> fs[] >>
      Cases_on ‘h2' = a’ >> fs[]  >|[
          
          fs[flat_edges_def] >>
          imp_res_tac mem_triple_map_fst >>
          irule list_not_merged_flat_membership2 >> fs[] >|[
            ‘MEM (a,h0,h0) t ’ by ( metis_tac[merge_edges_membership] ) >>
            metis_tac[]
            ,
            Cases_on ‘h1 = a’ >> fs[] >>
            ‘MEM (a,h1,h1) t ’ by ( metis_tac[merge_edges_membership] ) >>
            metis_tac[]
          ]                                            
          ,
          
          fs[flat_edges_def] >>
          imp_res_tac mem_triple_map_fst >>
          irule list_not_merged_flat_membership2  >|[
              subgoal ‘MEM (a,h0,h0) t ’ >- ( metis_tac[merge_edges_membership] ) >>
              metis_tac[]
              ,
              subgoal ‘MEM (a,h2,h2) t ’ >- ( metis_tac[merge_edges_membership] ) >>
              metis_tac[]
              ,
              subgoal ‘MEM (a,h1,h1) t ’ >- ( metis_tac[merge_edges_membership] ) >>
              metis_tac[]
            ]
          ,
          
          fs[flat_edges_def] >>
          imp_res_tac mem_triple_map_fst >>
          irule list_not_merged_flat_membership2  >|[
              subgoal ‘MEM (a,h0,h0) t ’ >- ( metis_tac[merge_edges_membership] ) >>
              metis_tac[]
              ,
              subgoal ‘MEM (a,h1,h1) t ’ >- ( metis_tac[merge_edges_membership] ) >>
              metis_tac[] 
              ,
              subgoal ‘MEM (a,h2,h2) t ’ >- ( metis_tac[merge_edges_membership] ) >>
              metis_tac[]
            ]
          ,

          fs[flat_edges_def] >>
          imp_res_tac mem_triple_map_fst >|[
              irule list_not_merged_flat_membership2 >>
              subgoal ‘MEM (a,h0,h0) t ’ >- ( metis_tac[merge_edges_membership] ) >>
              metis_tac[]
              ,
              irule list_not_merged_flat_membership2 >>
              subgoal ‘MEM (a,h1,h1) t ’ >- ( metis_tac[merge_edges_membership] ) >>
              metis_tac[]
              ,
              irule list_not_merged_flat_membership2 >>
              subgoal ‘MEM (a,h2,h2) t ’ >- ( metis_tac[merge_edges_membership] ) >>
              metis_tac[]
              ,
              
              Cases_on ‘h2 = a’ >> fs[] >> 
              subgoal ‘MEM (a,b,b) t ’ >- ( metis_tac[merge_edges_membership] ) >>
            
              ‘~ MEM b (MAP FST t')’ by fs[MEM_MAP] >>
              subgoal ‘has_parent t' b a’ >- ( fs[has_parent_def] )  >>
              
              subgoal ‘∃parent left right.
                         MEM (parent,left,right) t' ∧ (left = a ∨ right = a) ∧
                         parent ≠ a ∧ parent ≠ b’ >- metis_tac[has_parent_imp_exsists] >>
              
              (* two cases solution is the same *)
              fs[] >|[
                  
                  subgoal ‘∃ right'. MEM (parent,b,right') t ’ >- (metis_tac[eliminate_fst_edges_membership]) >>
                  metis_tac[list_eliminated_flat_membership3]
                  ,
                  
                  subgoal ‘∃ left'. MEM (parent,left',b) t ’ >- (metis_tac[eliminate_snd_edges_membership]) >>
                  metis_tac[list_eliminated_flat_membership3]
                ]
            ]
        ]
    ]
    ,
    (* second part *)
    PairCases_on ‘y’ >>
    rename1 ‘FST (m,q,q')’ >> gvs[] >>
    
    (* the node to be eliminated is h1*)
    ‘n=q ∧ n=q'’ by (imp_res_tac MEM_LOOKUP_trio >> gvs[]) >>
    rgs[] >>
    
    assume_tac merge_normalize_for_mergable_nodes_concrete >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘edges’, ‘t’, ‘m’, ‘h1’, ‘h2’, ‘q’, ‘q'’, ‘n’])) >>
    gvs[] >>

    ‘¬ MEM (m,n,n) t’ by gvs[] >> (* from ∀y. h0 = FST y ⇒ ¬MEM y t*)
    ‘¬MEM m (MAP FST t)’ by fs[MEM_MAP] >>
    
    Cases_on ‘edges = []’ >> gvs[] >>
    Cases_on ‘edges’ >> gvs[] >|[
        
        rgs[Once merge_edges_list_normalize] >>
        rgs[flat_edges_def] >|[
          
          subgoal ‘has_parent t' h1 m’ >- ( fs[has_parent_def] )  >>
 
          subgoal ‘∃parent left right.
                     MEM (parent,left,right) t' ∧ (left = m ∨ right = m) ∧
                     parent ≠ m ∧ parent ≠ h1’ >- metis_tac[has_parent_imp_exsists] >|[
            
            subgoal ‘∃ right'. MEM (parent,h1,right') t ’ >- (metis_tac[eliminate_fst_edges_membership]) >>
            fs[] >>
            imp_res_tac flat_edges_mem_triv2         
            ,
            subgoal ‘∃ left'. MEM (parent,left',h1) t ’ >- (metis_tac[eliminate_snd_edges_membership]) >>
            fs[] >>
            imp_res_tac flat_edges_mem_triv2
          ]
          ,
          irule list_not_merged_flat_membership1 >> fs[]
        ]      
        ,
                
        rgs[Once merge_edges_list_normalize] >>
        rgs[flat_edges_def] >|[
            subgoal ‘MEM (m,h1,h1) t ’ >- ( metis_tac[merge_edges_membership] ) >>
            imp_res_tac mem_triple_map_fst
            ,
            irule list_not_merged_flat_membership1 >> fs[]
          ]
      ]
  ]                           
QED


Theorem eliminate_dom_range_edges_imp_adel_key_mem_none:
  ∀ edges n n' n''.
    n'' ≠ n' ∧ n ≠ n' ∧
    has_parent edges n n' ∧
    ALL_DISTINCT (MAP FST edges) ∧
    ALOOKUP edges n = NONE ∧
    ALOOKUP edges n' = SOME (n,n) ∧
    MEM n (dom_range_edges edges) ∧
    MEM n' (dom_range_edges edges) ∧
    MEM n'' (dom_range_edges (merge_edges edges n n'))
    ⇒
    MEM n'' (dom_range_edges (ADELKEY n' (merge_edges edges n n')))
Proof
  fs[GSYM dom_range_edges1_3_eq] >>
  metis_tac[eliminate_dom_range_edges3_imp_adel_key_mem_none]
QED  

        
   
Theorem eliminate_edges_preserve_nodes:
  ∀ edges n n' n'' root labels vars.
    n'' ≠ n' ∧ n ≠ n' ∧
    has_parent edges n n' ∧
    BDD_ordered (root,edges,labels) vars ∧
    ALL_DISTINCT (MAP FST edges) ∧
    ALOOKUP edges n' = SOME (n,n) ∧
    MEM n'' (dom_range_edges (merge_edges edges n n')) ⇒
    MEM n'' (dom_range_edges (ADELKEY n' (merge_edges edges n n')))
Proof

  rpt strip_tac >>

  ‘MEM n (dom_range_edges edges)’ by metis_tac[lookup_edges_in_domain] >>
  ‘MEM n' (dom_range_edges edges)’ by metis_tac[lookup_edges_in_domain] >>

  Cases_on ‘ALOOKUP edges n’ >|[
    irule eliminate_dom_range_edges_imp_adel_key_mem_none >>
    fs[]
    ,
    
    ‘ALL_DISTINCT (MAP FST (merge_edges edges n n'))’ by gvs[GSYM all_distinct_fst_merge_edges] >>           
    PairCases_on ‘x’ >> 
    ‘MEM (n',n,n) edges’ by gvs[ALOOKUP_MEM] >>
    ‘MEM (n,x0,x1) edges’ by gvs[ALOOKUP_MEM] >>
    metis_tac[eliminate_dom_range_edges_imp_adel_key_mem] 
  ]
QED



Theorem eliminate_wf_labels_edges_same:          
  ∀ r edges labels n n' vars_consumed.
    ALL_DISTINCT (MAP FST edges) ∧
    BDD_ordered (r,edges,labels) vars_consumed ∧
    eliminable (r,edges,labels) n n' ∧
    ( ∀n. MEM n (dom_range_edges edges) ⇔ MEM n (MAP FST labels)) ⇒
    (∀n''. MEM n'' (dom_range_edges (ADELKEY n' (merge_edges edges n n'))) ⇔
             MEM n'' (MAP FST (ADELKEY n' labels)))
Proof
  rw[eliminable_def] >>
  Cases_on ‘n'' = n'’ >> gvs[] >|[
           
    gvs[merge_no_effect_on_unrelated_node_mem] >>
    gvs[ADELKEY_def, MEM_MAP, MEM_FILTER]
    ,

    ‘MEM n (dom_range_edges edges)’ by metis_tac[lookup_edges_in_domain] >>
    ‘MEM n' (dom_range_edges edges)’ by metis_tac[lookup_edges_in_domain] >>
    ‘MEM n'' (dom_range_edges edges) ⇔ MEM n'' (MAP FST labels)’ by gvs[] >>

    
    Cases_on ‘MEM n'' (dom_range_edges edges)’  >|[
        ‘MEM n'' (dom_range_edges edges)’ by gvs[] >>
        ‘MEM n'' (dom_range_edges (merge_edges edges n n'))’  by metis_tac[mem_edges_imp_mem_merge_imp1] >>
        
        subgoal ‘MEM n'' (dom_range_edges (ADELKEY n' (merge_edges edges n n')))’ >-
         (
         irule eliminate_edges_preserve_nodes >>
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
  ] 
QED










Theorem wf_non_empty_after_eliminable:
  ∀r edges labels n n'.
    ALL_DISTINCT (MAP FST edges) ∧
    edges ≠ [] ∧
    eliminable (r,edges,labels) n n' ⇒
    ADELKEY n' (merge_edges edges n n') ≠ []
Proof
        
  rw[eliminable_def] >>
  ‘∃parent left right.
     MEM (parent,left,right) edges ∧ (left = n' ∨ right = n') ∧
     parent ≠ n' ∧ parent ≠ n’ by metis_tac[has_parent_imp_exsists] >>
  gvs[] >>
  
  CCONTR_TAC >>
  gvs[] >>
  imp_res_tac merge_edges_adelkey_empty_imp_cases >>
  
  gvs[EVERY_MEM] >|[
    first_x_assum (strip_assume_tac o (Q.SPECL [‘(parent,left,right)’])) >>
    gvs[]
  ,
    first_x_assum (strip_assume_tac o (Q.SPECL [‘(parent,left,n')’])) >>
    gvs[]
  ]
QED



        
(*********************************)
(*   ELIMINATE  WFness           *)
(*********************************)
 
Theorem eliminate_wf_preservation:        
  ∀ BDD n n' vars_consumed.
    BDD_ordered BDD vars_consumed ∧
    BDD_WF BDD ∧
    consumed_dom_bdd vars_consumed BDD ∧
    eliminable BDD n n'
    ==>
    BDD_WF (merge BDD n n') 
Proof
  rpt strip_tac >>
  PairCases_on ‘BDD’ >>
  rename1 ‘(r,edges,labels)’ >>

  (* when there are no edges is simply wrong to do any optimizations *)
  Cases_on ‘edges = []’ >-
   (gvs[eliminable_def, eq_vars_in_labels_def] >>
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
          MEM n'' (MAP FST (ADELKEY n' labels))’ by imp_res_tac eliminate_wf_labels_edges_same >> gvs[] >>

  imp_res_tac mergable_wf_internals_some >> gvs[] >>

  imp_res_tac mergable_wf_leafs_some >> gvs[] >> rw[] >>
 
  imp_res_tac wf_non_empty_after_eliminable
  
QED




          
Theorem order_hold_for_eliminate1: 
  ∀ r edges labels n n' n'' nl vars_consumed.
    BDD_WF (r,edges,labels) ∧
    consumed_dom_bdd vars_consumed (r,edges,labels) ∧
    eliminable (r,edges,labels) n n' ⇒
    (
    ( order_hold labels vars_consumed n'' nl ⇒ order_hold (ADELKEY n' labels) vars_consumed n'' nl)
    ) 
Proof
  rw[order_hold_def] >>
  rpt strip_tac >> 
  gvs[eliminable_def,ALOOKUP_ADELKEY,BDD_WF_def] >>
  gvs[eq_vars_in_labels_def] >>
  rpt (BasicProvers.full_case_tac >> gvs[])
QED



Theorem order_hold_for_eliminate2: 
  ∀ r edges labels n n' n'' nl vars_consumed.
    BDD_WF (r,edges,labels) ∧
    consumed_dom_bdd vars_consumed (r,edges,labels) ∧
    eliminable (r,edges,labels) n n' ⇒
    (
    ( order_hold labels vars_consumed n'' n' ∧
      order_hold labels vars_consumed n' n
      ⇒ order_hold (ADELKEY n' labels) vars_consumed n'' n)
    ) 
Proof
  rw[order_hold_def] >>
  rpt strip_tac >> 
  
  gvs[ALOOKUP_ADELKEY, eliminable_def] >>

  ‘MEM n' (dom_range_edges edges)’ by gvs[lookup_edges_in_domain] >>
  subgoal ‘is_lookup_internal labels n'’ >-
   (gvs[BDD_WF_def] >>
    gvs[lookup_is_some_def] >>
    res_tac
   ) >>

  gvs[is_lookup_internal_def, consumed_dom_bdd_def] >>
  res_tac >>
  imp_res_tac MEM_INDEX_OF >> fs[] >>
  first_assum (strip_assume_tac o (Q.SPECL [‘i''’])) >>
  res_tac >>                
  gvs[]
QED

        

(*********************************)
(*       ELIMINATE  Order        *)
(*********************************)      
Theorem eliminate_order_preservation:
  ∀ BDD n n' vars_consumed.
    BDD_ordered BDD vars_consumed ∧
    BDD_WF BDD ∧
    consumed_dom_bdd vars_consumed BDD ∧
    eliminable BDD n n'
    ⇒
    BDD_ordered (merge BDD n n') vars_consumed 
Proof
  rpt strip_tac >>
  (* we know that it is WF *)
  (*‘BDD_WF (merge BDD n n')’ by imp_res_tac merge_wf_preservation >>*)
                                                
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
          metis_tac[order_hold_for_eliminate1]
          ,
          (* afftected by the merge, i.e. a parent of eliminated n', at left node *)
          ‘nl'=n' ∧ nl=n’ by metis_tac[merge_parent_change] >>
          ‘ALOOKUP edges n' = SOME (n,n)’ by gvs[eliminable_def] >>
          first_assum (strip_assume_tac o (Q.SPECL [‘n''’, ‘n'’, ‘nr'’])) >>
          first_assum (strip_assume_tac o (Q.SPECL [‘n'’, ‘n’, ‘n’])) >>
          res_tac >>
          metis_tac [order_hold_for_eliminate2]
        ]
        ,
        (* the right part*)
        Cases_on ‘nr=nr'’ >> gvs[]  >|[
            (* unaffected by the merge*)
            first_x_assum (strip_assume_tac o (Q.SPECL [‘n''’, ‘nl'’, ‘nr’])) >>
            gvs[] >>
            metis_tac[order_hold_for_eliminate1]
            ,
            (* afftected by the merge, i.e. a parent of eliminated n', at left node *)
            ‘nr'=n' ∧ nr=n’ by metis_tac[merge_parent_change] >>
            ‘ALOOKUP edges n' = SOME (n,n)’ by gvs[eliminable_def] >>
            first_assum (strip_assume_tac o (Q.SPECL [‘n''’, ‘nl’, ‘n'’])) >>
            first_assum (strip_assume_tac o (Q.SPECL [‘n'’, ‘n’, ‘n’])) >>
            res_tac >>
            metis_tac [order_hold_for_eliminate2]
          ]
      ]
                    
  ]
QED



        

              
Theorem eliminate_BDD_preserves_correctness:
  ∀BDD n nl vars rec.
    
    BDD_WF BDD ∧
    BDD_ordered BDD vars ∧
    fv_in_BDD rec BDD vars ∧
    consumed_dom_bdd vars BDD ∧
    correct_sem rec BDD vars  ⇒
                
    (
    BDD_WF (eliminate_BDD BDD n nl) ∧
    BDD_ordered (eliminate_BDD BDD n nl) vars ∧
    fv_in_BDD rec (eliminate_BDD BDD n nl) vars ∧
    consumed_dom_bdd vars (eliminate_BDD BDD n nl) ∧
    correct_sem rec (eliminate_BDD BDD n nl) vars
    )
Proof
  Induct_on ‘nl’ >-
   (* Base case: empty list *)
   fs [eliminate_BDD_def] >>
  
  (* Inductive case *)
  rpt gen_tac >> strip_tac >>
  fs [eliminate_BDD_def] >>
  
  Cases_on ‘eliminable BDD h n’ >> gvs[] >|[
    gvs[] >>
    assume_tac eliminate_correct >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘BDD’, ‘[]’, ‘vars’, ‘h’, ‘n’, ‘rec’])) >>
    gvs[] >>
    (*res_tac >>*)
    ‘BDD_WF (merge BDD h n)’ by imp_res_tac eliminate_wf_preservation >>
    ‘BDD_ordered (merge BDD h n) vars’ by imp_res_tac eliminate_order_preservation >>
    ‘fv_in_BDD rec (merge BDD h n) vars’ by (imp_res_tac merge_fv_final_preservation >>
                                             first_x_assum (strip_assume_tac o (Q.SPECL [‘n’, ‘h’]))) >>
    imp_res_tac merge_consumed_dom_final_preservation >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘n’, ‘h’]) ) >>
    gvs[]>>

        
    res_tac >>
    gvs[]
    , 
    metis_tac[]
  ]
QED



(* TODO: now add those in Valid_BDD rec (BDD:('a,'b)BDD) vars *)


val _ = export_theory ();

