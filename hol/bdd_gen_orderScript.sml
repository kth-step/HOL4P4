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



    

      

Theorem order_translation_inter_children:
  ∀ r edges labels r'' edges'' labels'' h c c' n n' n'' vars_consumed rec.
    ALL_DISTINCT (h::vars_consumed) ∧
    BDD_WF (r'',edges'',labels'') ∧
    BDD_WF (r,edges,labels) ∧             
    BDD_ordered (r,edges,labels) vars_consumed ∧
    body_of_mk rec (r,edges,labels) h c = SOME ((r'',edges'',labels''),c') ∧
    ALOOKUP edges'' n = SOME (n',n'') ⇒
    (order_hold labels'' (h::vars_consumed) n n' (*∧
     order_hold labels'' (h::vars_consumed) n n'' *) )
Proof
                        
  rpt gen_tac >>
  strip_tac >>
  
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
        ‘ALOOKUP (non_term_leaf_updt labels h ⧺ new_labels) n' =
         SOME (non_termn (SOME h,p'))’ by cheat >>
        rgs[] >>
         
        (* this makes i' = 0 *)
        ‘INDEX_OF h (h::vars_consumed) = SOME 0’ by cheat >>
        rgs[] >>

        ‘x ≠ h’ by cheat >>
        rgs[] >>

        ‘i>0’ by cheat >>
        rgs[] 
        ,
        (* if n' in edges , we need to show that n was also in edges *)
        
        (* first we work with n' *)
        ‘MEM n' (dom_range_edges edges)’ by cheat >>
        
        
        ‘∃ x'' p''.ALOOKUP labels n' = SOME (non_termn (SOME x'',p''))’ by
          (rgs[BDD_WF_def] >>
           rgs[lookup_is_some_def, is_lookup_internal_def] >> res_tac >> gvs[]) >>
        
        
        (* second  we work with n *)
        
        ‘MEM n (dom_range_edges edges)’ by cheat >>  (* this needs a proof*)
        ‘ALOOKUP edges n = SOME (n',n'')’ by cheat >>
        ‘∃ x'' p''.ALOOKUP labels n = SOME (non_termn (SOME x'',p''))’ by
          (rgs[BDD_WF_def] >>
           rgs[lookup_is_some_def, is_lookup_internal_def] >> res_tac >> rgs[]) >>
        ‘x'³' = x’ by cheat >>
        ‘x'' = x'’ by cheat >>
        
        ‘p'³' = p’ by cheat >>
        ‘p'' = p'’ by cheat >>
        
        
        rgs[] >> rgs[BDD_ordered_def] >>
        first_x_assum (strip_assume_tac o (Q.SPECL [‘n’, ‘n'’, ‘n''’])) >>
        rgs[] >>
        
        qpat_x_assum ‘order_hold labels vars_consumed n n'’ (fn thm => assume_tac (SIMP_RULE (srw_ss()) [Once order_hold_def] thm)) >>
        
        
        first_x_assum (strip_assume_tac o (Q.SPECL [‘i-1’,‘i'-1’, ‘x’,‘x'’,‘p’,‘p'’])) >>
        rgs[] >>
        
        ‘x≠h’ by cheat >>
        ‘INDEX_OF x vars_consumed = SOME (i − 1)’ by cheat >>
        ‘INDEX_OF x' vars_consumed = SOME (i' − 1)’ by cheat >>
        rgs[]
           
           
      ]
                        
                        
  ]
QED













   

        


Theorem order_translation_inter:
  ∀ vars rec vars_consumed (BDD:('a,'b)BDD) BDD'' c c' h.
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

  simp[BDD_ordered_def] >>  rpt strip_tac >|[
    cheat
    ,
    cheat
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
