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

     
val _ = new_theory "bdd_gen_order";



(* to do, how to make a tactic visible to all files *)

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



                                                                
Theorem body_of_mk_output:
  ∀  r r'' edges edges'' labels labels''  c c' h rec .
    body_of_mk rec (r,edges,labels) h c = SOME ((r'',edges'',labels''),c') ⇒
    r = r'' ∧
    ∃ edges_new labels_new. edges'' = edges ++ edges_new ∧ labels'' = (non_term_leaf_updt labels h) ++ labels_new
Proof                 
  rpt strip_tac >>
  gvs[body_of_mk_def] >>
  gvs[AllCaseEqs()]>>
  body_of_mk_pred_tac
QED 



Theorem mem_leaves_in_dom_edges:
  ∀ leaves edges n r.
    edges ≠ [] ∧
    MEM n leaves ∧
    getLeaves edges r = SOME leaves ⇒
    MEM n (dom_range_edges (edges))   
Proof
  rpt strip_tac >> gvs[] >>
  Cases_on ‘edges’ >>
  rgs[getLeaves_def] >>
  gvs[AllCaseEqs()]>>
  gvs[get_leaves_list_in_nodes]
QED


Theorem index_of_head:
∀ l i h .
  INDEX_OF h (h::l) = SOME i ⇒
  i = 0
Proof
  Induct >>
  rgs[] >>
  rpt strip_tac >>
  gvs[INDEX_OF_def] >>
  
  rgs[INDEX_FIND_def] >>
  PairCases_on ‘z’ >> rgs[]
QED


        
Theorem index_of_not_shifted:
  ∀ l i h x.
    x ≠ h ∧
    INDEX_OF x (h::l) = SOME i ⇒
    i > 0
Proof
  rpt strip_tac >>
  gvs[INDEX_OF_def] >>
  
  PairCases_on ‘z’ >> rgs[] >>
  fs[INDEX_FIND_EQ_SOME_0] >>
  
  Cases_on ‘z0’ >> gvs[] 
QED


Theorem index_of_shifted_backwards:        
∀ l i h x.
  x ≠ h ∧
INDEX_OF x (h::l) = SOME i ⇒
∃ i'. INDEX_OF x l = SOME i' ∧ i' = i-1
Proof
  rpt strip_tac >>
  imp_res_tac index_of_not_shifted >>
  gvs[INDEX_OF_def] >>
  PairCases_on ‘z’ >> rgs[] >>
  
  Cases_on ‘z0’ >> gvs[] >>
  fs[INDEX_FIND_EQ_SOME_0] >>
  gvs[] >>
  
  qexistsl_tac [‘(n , EL n l)’] >>
  gvs[]>>
  fs[INDEX_FIND_EQ_SOME_0] >>
  rpt strip_tac >>

  first_x_assum (strip_assume_tac o (Q.SPECL [‘SUC j'’])) >>
  gvs[]
QED






                                        


        

Theorem in_range_of_new_edges_in_dom_new_labels:
  ∀ simp_leaves' new_edges new_labels n n' n'' c.
    mk_new_labels simp_leaves' c = new_labels ∧
    mk_new_edges simp_leaves' c = new_edges ∧
    ALOOKUP new_edges n = SOME (n',n'') ⇒
    (MEM n' (MAP FST new_labels) ∧ MEM n'' (MAP FST new_labels))
Proof
  
  Induct >>
  rpt strip_tac >>
  rgs[mk_new_labels_def, mk_new_edges_def] >>
  
  PairCases_on ‘h’ >> rgs[] >>
  rgs[mk_new_labels_def, mk_new_edges_def] >>
  gvs[AllCaseEqs()]>>
  res_tac >>
  gvs[]
QED

     
        
        

Theorem falsified_assump_triv1:
  ∀ simp_leaves' new_labels new_edges c n n' n''.          
    c > n' ∧    
    mk_new_labels simp_leaves' c = new_labels ∧
    mk_new_edges simp_leaves' c = new_edges ∧
    ALOOKUP new_edges n = SOME (n',n'')
    ⇒
    F
Proof
  rpt strip_tac >>
  ‘MEM n' (MAP FST new_labels)’ by imp_res_tac in_range_of_new_edges_in_dom_new_labels >>
  ‘MEM n'' (MAP FST new_labels)’ by imp_res_tac in_range_of_new_edges_in_dom_new_labels >>
  imp_res_tac counter_range_in_new_labels >> gvs[]
QED


Theorem lookup_labels_in_updt_append:
  ∀ labels new_labels  h n x p x' p'.
    ALOOKUP labels n = SOME (non_termn (SOME x,p)) ∧
    ALOOKUP (non_term_leaf_updt labels h ⧺ new_labels) n = SOME (non_termn (SOME x',p')) ⇒
    (x=x' ∧ p=p')
Proof
  rpt gen_tac >>
  strip_tac >>
  gvs[ALOOKUP_APPEND] >>
  gvs[AllCaseEqs()]>>
  imp_res_tac lookup_labels_in_updt >> rgs[] 
QED
        
        

Theorem order_translation_inter_children:
  ∀ r edges labels r'' edges'' labels'' h c c' n n' n'' vars_consumed rec.
    range_c c (r,edges,labels) ∧
    consumed_dom_bdd vars_consumed (r,edges,labels) ∧
    ALL_DISTINCT (h::vars_consumed) ∧
    BDD_WF (r'',edges'',labels'') ∧ 
    BDD_WF (r,edges,labels) ∧             
    BDD_ordered (r,edges,labels) vars_consumed ∧
    edges ≠ [] ∧
    body_of_mk rec (r,edges,labels) h c = SOME ((r'',edges'',labels''),c') ∧
    ALOOKUP edges'' n = SOME (n',n'') ⇒
    (order_hold labels'' (h::vars_consumed) n n' (*∧
     order_hold labels'' (h::vars_consumed) n n'' *) )
Proof
                        
  rpt gen_tac >>
  strip_tac >>

  imp_res_tac WFness_range_c_inter >>
  (*imp_res_tac WFness_translation_inter >> *)
    
  gvs[body_of_mk_def] >>
  gvs[AllCaseEqs()]>>
  body_of_mk_pred_tac >>


  (* First: we know that the parent, n, is
     indeed defined and its children are in the edges, and
     indeed the parent has a label of (x,p)*)
  
  ‘MEM n (dom_range_edges (edges ⧺ new_edges))’ by imp_res_tac lookup_edges_in_domain >>
  
  ‘lookup_is_some (edges ⧺ new_edges) n’ by rgs[lookup_is_some_def] >>
  
  
  subgoal ‘∃x p. ALOOKUP (non_term_leaf_updt labels h ⧺ new_labels) n = SOME (non_termn (SOME x,p))’ >-
   (
   rgs[BDD_WF_def] >>
   rgs[lookup_is_some_def] >>
   rgs[is_lookup_internal_def] 
   ) >>
  
  
  (* Second: the child could be a leaf, and could be something else.
     if the child is a leaf, we know that it should not exsist in the
     vars order simply because they have no x with the property in the labels. *)

  ‘MEM n' (dom_range_edges (edges ⧺ new_edges))’ by imp_res_tac lookup_edges_in_domain >>
  
  Cases_on ‘ALOOKUP (edges ⧺ new_edges) n'’ >|[
    (* if the child is a leaf, we need to show it by contradition *)
    (*according to WFness, this kind of leaf has a label of ntl *)
    
    rgs[BDD_WF_def, is_lookup_ntl_def] >>
    simp[order_hold_def] >> rpt strip_tac 
                                
    ,
    (* if not a leaf, then indeed it has a children, those children
       can be either in old edges or new edges, eitherway can be
       proved by the order property in teh assumptions *)
    
    PairCases_on ‘x'’ >>
    ‘lookup_is_some (edges ⧺ new_edges) n'’ by rgs[lookup_is_some_def] >>
    
    subgoal ‘∃x p. ALOOKUP (non_term_leaf_updt labels h ⧺ new_labels) n' = SOME (non_termn (SOME x,p))’ >-
     (
     rgs[BDD_WF_def] >>
     rgs[lookup_is_some_def] >>
     rgs[is_lookup_internal_def] 
     ) >>
    
    simp[order_hold_def] >> rpt strip_tac >>
    rgs[lookup_is_some_def] >>
    
    qpat_x_assum ‘ALOOKUP (edges ⧺ new_edges) n' = SOME (x'0,x'1)’ (fn thm => assume_tac (SIMP_RULE (srw_ss()) [Once ALOOKUP_APPEND] thm)) >>
    rgs[AllCaseEqs()] >|[

                      
        (* if n' in new edges and n is in old*)
        (* if n is in new edges, we know that its variable in the label was h *)


        (* we start by showing that n' is in labels, and has a label termin p'',
           then since it is that, we show that it got updated by non_term_leaf_updt to h,
           then since it is in labels, then it can't be in new labels as they are distinct,
         *)

        subgoal ‘MEM n' (dom_range_edges (edges))’ >-
         (
                          
         subgoal ‘ ∃ p . ALOOKUP ntl n' = SOME p’ >-
          (
          imp_res_tac_body >>
          rgs[] >>
          
          assume_tac (INST_TYPE [“:'a” |-> “:num” , “:'b” |-> “:(num#num)” , “:'c” |-> “:('a)” ] alookup_map_local_thm)  >>
          first_x_assum (strip_assume_tac o (Q.SPECL [‘new_edges’,‘ntl’,‘n'’,‘(x'0,x'1)’])) >>
          gvs[]
          ) >>
          imp_res_tac_body >>

         ‘∃ lbl . ALOOKUP leaves_labels n' = SOME lbl’ by (imp_res_tac alookup_nonterm_exsists >> gvs[]) >>
         ‘MEM (n',lbl) leaves_labels’ by imp_res_tac ALOOKUP_MEM >>
         ‘MEM n' (MAP FST leaves_labels)’ by (imp_res_tac mem_fst_snd >> gvs[]) >>
         ‘MEM n' leaves’ by gvs[] >>
         irule mem_leaves_in_dom_edges >> srw_tac [SatisfySimps.SATISFY_ss][]
         )>>


        
        (* now we use WFness to show that n' was indeed an ntl in labels *)
        
        subgoal ‘∃ p_old . ALOOKUP labels n' = SOME (non_termn (NONE,p_old))’ >-
         (
         qpat_x_assum ‘BDD_WF (r,edges,labels)’ (fn thm => assume_tac (SIMP_RULE (srw_ss()) [Once BDD_WF_def] thm)) >>
         rgs[] >>
               
         rgs[is_lookup_ntl_def] >>
         res_tac >> rgs[] >>
         rgs[BDD_WF_def] >>
         imp_res_tac lookup_labels_in_updt_term >>
         first_x_assum (strip_assume_tac o (Q.SPECL [‘h’])) >>
         rgs[ALOOKUP_APPEND] >>
         srw_tac [SatisfySimps.SATISFY_ss][]
         ) >>
        
        
        subgoal ‘ALOOKUP (non_term_leaf_updt labels h) n' = SOME (non_termn (SOME h,p_old))’ >-
         (
         imp_res_tac lookup_labels_in_updt_none >>
         first_x_assum (strip_assume_tac o (Q.SPECL [‘h’])) 
         ) >>

        
        (* if n is in new edges, we know that its variable in the label was h *)
        subgoal ‘ALOOKUP (non_term_leaf_updt labels h ⧺ new_labels) n' =
                          SOME (non_termn (SOME h,p_old))’ >-
         (
         rgs[ALOOKUP_APPEND]
         ) >>
        rgs[] >>
         
        (* this makes i' = 0 *)
        ‘i' = 0’ by (imp_res_tac index_of_head) >>
        rgs[] >>

        (* we need to show that the parent n is in edges, then show that it was already internal leaf, then
           thus its label is the updated one stays as it is
           and not in new edges for us to show
           that x ≠ h
         *)



        subgoal ‘ALOOKUP edges n = SOME (n',n'')’ >-
         (
         qpat_x_assum ‘ALOOKUP (edges ⧺ new_edges) n = SOME (n',n'')’ (fn thm => assume_tac (SIMP_RULE (srw_ss()) [ALOOKUP_APPEND] thm)) >>
         rgs[AllCaseEqs()] >>
         rgs[] >>

         ‘MEM n' (MAP FST labels)’ by (imp_res_tac ALOOKUP_MEM >> imp_res_tac mem_fst_snd >> gvs[]) >>       
    

         rgs[range_c_def] >>                                           
         rgs[EVERY_MEM] >>
         res_tac >>

         imp_res_tac falsified_assump_triv1 
         ) >>
        
        ‘MEM n (dom_range_edges edges)’ by imp_res_tac lookup_edges_in_domain >>
        
        subgoal ‘is_lookup_internal labels n’ >- 
         (qpat_x_assum ‘BDD_WF (r,edges,labels)’ (fn thm => assume_tac (SIMP_RULE (srw_ss()) [Once BDD_WF_def] thm)) >>
        rgs[lookup_is_some_def] >>
        res_tac 
         ) >>

        rgs[is_lookup_internal_def] >>


        ‘x'' = x’ by imp_res_tac lookup_labels_in_updt_append >>
        
        rgs[consumed_dom_bdd_def] >>
        res_tac >>

                        
          ‘x ≠ h’ by metis_tac[] >>
          rgs[] >>
          
          ‘i>0’ by imp_res_tac index_of_not_head >>
          rgs[]
                        
        ,


                
        (* if n' in edges , we need to show that n was also in edges *)
        
        (* first we work with n' *)
        ‘MEM n' (dom_range_edges edges)’ by imp_res_tac lookup_edges_in_domain >>
        
        
        ‘∃ x'' p''.ALOOKUP labels n' = SOME (non_termn (SOME x'',p''))’ by
          (rgs[BDD_WF_def] >>
           rgs[lookup_is_some_def, is_lookup_internal_def] >> res_tac >> gvs[]) >>
        
        
        (* second  we work with n *)

                subgoal ‘ALOOKUP edges n = SOME (n',n'')’ >-
         (
         qpat_x_assum ‘ALOOKUP (edges ⧺ new_edges) n = SOME (n',n'')’ (fn thm => assume_tac (SIMP_RULE (srw_ss()) [ALOOKUP_APPEND] thm)) >>
         rgs[AllCaseEqs()] >>
         rgs[] >>

         ‘MEM n' (MAP FST labels)’ by (imp_res_tac ALOOKUP_MEM >> imp_res_tac mem_fst_snd >> gvs[]) >>       
    

         rgs[range_c_def] >>                                           
         rgs[EVERY_MEM] >>
         res_tac >>

         imp_res_tac falsified_assump_triv1 
         ) >>

         
        
        ‘MEM n (dom_range_edges edges)’ by imp_res_tac lookup_edges_in_domain >>  (* this needs a proof*)
        ‘∃ x'' p''.ALOOKUP labels n = SOME (non_termn (SOME x'',p''))’ by
          (rgs[BDD_WF_def] >>
           rgs[lookup_is_some_def, is_lookup_internal_def] >> res_tac >> rgs[]) >>

        

           
        ‘x'³' = x’ by imp_res_tac lookup_labels_in_updt_append  >>
        ‘x'' = x'’ by imp_res_tac lookup_labels_in_updt_append  >>
        
        ‘p'³' = p’ by imp_res_tac lookup_labels_in_updt_append  >>
        ‘p'' = p'’ by imp_res_tac lookup_labels_in_updt_append  >>
        
        
        rgs[] >> rgs[BDD_ordered_def] >>
        first_x_assum (strip_assume_tac o (Q.SPECL [‘n’, ‘n'’, ‘n''’])) >>
        rgs[] >>
        
        qpat_x_assum ‘order_hold labels vars_consumed n n'’ (fn thm => assume_tac (SIMP_RULE (srw_ss()) [Once order_hold_def] thm)) >>
        
        
        first_x_assum (strip_assume_tac o (Q.SPECL [‘i-1’,‘i'-1’, ‘x’,‘x'’,‘p’,‘p'’])) >>
        rgs[] >>
        
          rgs[consumed_dom_bdd_def] >>
        res_tac >>

                        
          ‘x ≠ h’ by metis_tac[] >>
        rgs[] >>


        imp_res_tac index_of_shifted_backwards
        ‘INDEX_OF x vars_consumed = SOME (i − 1)’ by (imp_res_tac index_of_shifted_backwards >> gvs[]) >>
        ‘INDEX_OF x' vars_consumed = SOME (i' − 1)’ by (imp_res_tac index_of_shifted_backwards >> gvs[]>> metis_tac[]) >>
        rgs[]
           
           
      ]
                        
                        
  ]
QED






Theorem orderd_edges_empty_mkbody_imp_orderd:
  ∀ r edges labels r'' edges'' labels'' rec c c' h vars_consumed.
    range_c c (r,[],labels) ∧
    BDD_WF (r,[],labels) ∧
    BDD_ordered (r,[],labels) vars_consumed ∧
    body_of_mk rec (r,[],labels) h c = SOME ((r'',edges'',labels''),c') ⇒
    BDD_ordered (r'',edges'',labels'') (h::vars_consumed)
Proof
  rpt strip_tac >>      
  simp[BDD_ordered_def] >> 
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
  Cases_on ‘rec.final (rec.simp (rec.sub r' h F))’ >> gvs[order_hold_def] >>
  
  rgs[BDD_ordered_def] >>
  rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  gvs[range_c_def]
QED                                                        



                                                                


Theorem order_translation_inter:
  ∀ vars rec vars_consumed (BDD:('a,'b)BDD) BDD'' c c' h.
    range_c c BDD ∧
    BDD_WF BDD ∧
    BDD_WF BDD'' ∧
    BDD_ordered BDD vars_consumed ∧
    body_of_mk rec BDD h c = SOME (BDD'',c') ⇒
    BDD_ordered BDD'' (h::vars_consumed) 
Proof
  rpt strip_tac >>
  
  PairCases_on ‘BDD’ >>
  rename1 ‘(r,edges,labels)’ >>
  
  PairCases_on ‘BDD''’ >>
  rename1 ‘(r'',edges'',labels'')’ >>
  
  Cases_on ‘edges = []’ >|[
    irule orderd_edges_empty_mkbody_imp_orderd >>
    srw_tac [SatisfySimps.SATISFY_ss][]
    ,
    simp[BDD_ordered_def] >>  rpt strip_tac >|[
      cheat
      ,
      cheat
    ]
  ]
QED



        
Theorem order_translation:
  ∀ vars rec vars_consumed (BDD:('a,'b)BDD) BDD' c.
    range_c c BDD ∧
    BDD_ordered BDD vars_consumed ∧
    BDD_WF BDD ∧
    (SOME BDD' = mk_BDDPred rec BDD vars_consumed vars c) ⇒
    BDD_ordered BDD' ((REVERSE vars)++vars_consumed)
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

    (* proved eariler *)
    ‘BDD_WF (q0,q1,q2)’ by imp_res_tac WFness_translation_inter >>
    ‘range_c r'' (q0,q1,q2)’ by imp_res_tac WFness_range_c_inter >>
    
    
    
    ‘BDD_ordered (q0,q1,q2) (h::vars_consumed)’ by imp_res_tac order_translation_inter >> 
    res_tac >>
    ‘REVERSE vars ++ h::vars_consumed = REVERSE vars ++ [h] ++ vars_consumed’ by gvs[Once CONS_APPEND] >>
    metis_tac []
  ]    
QED




                     

    

val _ = export_theory ();
