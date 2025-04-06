open HolKernel boolLib liteLib simpLib Parse bossLib;
open arithmeticTheory stringTheory containerTheory pred_setTheory
     listTheory finite_mapTheory;

open p4Lib;
open blastLib bitstringLib;
open p4Theory;
open p4_auxTheory;
open p4_coreTheory;

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

open bdd_genTheory;     
     
val _ = new_theory "p4_policy";


 (* Predicate datatype *)
val _ = Hol_datatype `
  pred = Var of string
       | True
       | False
       | And of pred => pred
       | Or of pred => pred
       | Not of pred
       | Implies of pred => pred`;
     
                                  
(**************************************************)
(* specialized definitions for a predicate record *)
(*   here 'a would be pred and 'b would be bool   *)
(**************************************************)
(*
Definition Sem_rule_def:
  (Sem_rule (Var x) mv = (ALOOKUP mv x) ) /\
  (Sem_rule True _ = SOME T) /\
  (Sem_rule False _ = SOME F) /\
  (Sem_rule (And p q) mv = 
   case (Sem_rule p mv, Sem_rule q mv)  of
   | (SOME b, SOME b') => SOME (b ∧ b')
   | (_,_) => NONE
  ) /\
  (Sem_rule (Or p q) mv = 
   case (Sem_rule p mv, Sem_rule q mv)  of
   | (SOME b,SOME b') => SOME (b ∨ b')
   | (_,_) => NONE
  ) /\
  (Sem_rule (Not p) mv = 
   case (Sem_rule p mv)  of
   | SOME b => SOME (~b)
   | _ => NONE
  ) /\
  (Sem_rule (Implies p q) mv = 
   case (Sem_rule p mv, Sem_rule q mv)  of
   | (SOME b,SOME b') => SOME (b ⇒ b')
   | (_,_) => NONE
  ) 
End


(* predicates substitute *)
Definition mk_substitute_pred_def:
  (mk_substitute_pred (True) x b = True) ∧
  (mk_substitute_pred (False) x b = False) ∧
  (mk_substitute_pred (Var x') x b = 
  if (x=x') then (if b then True else False) else (Var x') 
  ) ∧
  (mk_substitute_pred (And c c' ) x b =
      (And (mk_substitute_pred c x b) (mk_substitute_pred c' x b ))) ∧
  (mk_substitute_pred (Or c c') x b =
      (Or (mk_substitute_pred c x b) (mk_substitute_pred c' x b ))) ∧
  (mk_substitute_pred (Not c) x b=
      (Not (mk_substitute_pred c x b)))
End


(* predicates simplifications *)        
Definition simp_pred_def:
  (simp_pred (Var x) = Var x) /\
  (simp_pred True = True) /\
  (simp_pred False = False) /\
  (simp_pred (And p q) =
   let p' = simp_pred p in
     let q' = simp_pred q in
       case (p', q') of
       | (True, True) => True
       | (False,  _) => False
       | (_, False) => False
       | (True, q') => q'
       | (p', True) => p'
       | _ => And p' q') /\
  (simp_pred (Or p q) =
   let p' = simp_pred p in
     let q' = simp_pred q in
       case (p', q') of
       | (False, False) => False
       | (False, q') => q'
       | (p', False) => p'
       | (True, _) => True
       | (_, True) => True
       | _ => Or p' q') /\
  (simp_pred (Not p) =
   let p' = simp_pred p in
     case p' of
     | True => False
     | False => True
     | _ => Not p') /\
  (simp_pred (Implies p q) =
   let p' = simp_pred p in
     let q' = simp_pred q in
       case (p', q') of
       | (True, False) => False
       | (False, _) => True
       | (True, q') => q'
       | _ => Implies p' q')
End



   


(* move to other file the specialized *)
Definition pred_final_def:
 pred_final p = 
 case p of
 | True => SOME T
 | False => SOME F
 | _ => NONE
End
                                                                
                                                         
Definition pred_structure_def:
  pred_structure =
  <|
    sem := Sem_rule;
    sub := mk_substitute_pred;
    simp := simp_pred;
    final := pred_final;
  |>
End            



Definition size_of_tree_def:
  size_of_tree (edges:edges) (n:num) =
  ( case ALOOKUP edges n of
    | SOME (l,r) => 1 + size_of_tree (DELETE_ELEMENT (n,l,r) edges) l + size_of_tree (DELETE_ELEMENT (n,l,r) edges) r
    | NONE =>  (1:num)
  )
Termination
  WF_REL_TAC `measure (\(edges,n). LENGTH edges)` >>
  rpt STRIP_TAC >>
  gvs[LENGTH_DELETE_ELEMENT_LE, ALOOKUP_MEM]
End

                                                       
       

Definition FV_def:
  FV (Var x) = [x] ∧
  FV True = [] ∧
  FV False = [] ∧
  FV (And p q) = nub (FV p ++ FV q) ∧
  FV (Or p q) = nub (FV p ++ FV q) ∧
  FV (Not p) = FV p ∧
  FV (Implies p q) = nub (FV p ++ FV q)
End




Theorem simp_pred_imp_mem:          
  ∀ p x .
    simp_pred p = Var x ⇒
    MEM x (FV p)
Proof
  Induct >>
  rw[simp_pred_def, FV_def] >> gvs[AllCaseEqs()]
QED


Theorem mem_imp_sem_rule:        
  ∀p mv. (∀x. MEM x (FV p) ⇒ (∃b. ALOOKUP mv x = SOME b)) ⇒
         Sem_rule p mv ≠ NONE ∧ ∃ b' . Sem_rule p mv = SOME b'
Proof
  Induct >>
  rw[simp_pred_def, FV_def] >> gvs[AllCaseEqs()] >>
  gvs[Sem_rule_def, simp_pred_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) 
QED




Theorem simplification_correct:
  ∀p mv. (∀x. MEM x (FV p) ⇒ (∃b. ALOOKUP mv x = SOME b)) ⇒
         Sem_rule p mv = Sem_rule (simp_pred p) mv
Proof
  Induct_on `p` >-
   (rw[simp_pred_def, Sem_rule_def]) >-
   (rw[simp_pred_def, Sem_rule_def]) >-
   (rw[simp_pred_def, Sem_rule_def]) >>

  rpt strip_tac >>
  imp_res_tac mem_imp_sem_rule >>

  LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘mv’])) >>
  gvs[FV_def] >>
  gvs[Sem_rule_def] >>   

  rw[Sem_rule_def, simp_pred_def] >>   
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  gvs[Sem_rule_def, simp_pred_def] >>
  
  first_x_assum (strip_assume_tac o (Q.SPECL [‘s’])) >>
  imp_res_tac simp_pred_imp_mem >>
  gvs[]
QED

        
             


   



                            




                     
             

Theorem SNOC_rw:
  ∀ l x .
    SNOC x l = l ++[x]
Proof
  gvs[SNOC]
QED



val move_forall_fst_tac : tactic =
  FIRST_X_ASSUM (fn th =>
  let val (vars, body) = strip_forall (concl th) in
    if null vars then
      NO_TAC
    else
      let val new_vars = tl vars @ [hd vars]
          val th_body = SPEC_ALL th
          val new_th = GENL new_vars th_body
      in
      POP_ASSUM (K ALL_TAC) >> ASSUME_TAC new_th
       end
   end
);




 



Definition correct_sem_def:
  correct_sem (BDD:BDD)  =
  ∀ n mv b r edges labels .
    BDD = (r,edges,labels) ∧
   (* ALOOKUP labels n = SOME lbl ∧ *)
      BDD_pred_sem BDD mv n b  ⇒
       b = apply_Sem_rule (get_prop labels n) mv         
End  



        
Theorem BDD_pred_sem_determ:
  ∀ n BDD mv b b'.        
    BDD_pred_sem BDD mv n b ∧
    BDD_pred_sem BDD mv n b' ⇒
    (b=b')
Proof
 Induct_on ‘BDD_pred_sem’ >>        
 rpt strip_tac >>
 rgs[Once BDD_pred_sem_cases]
QED


 
          

Theorem BDD_pred_sem_exsists_inter:
  ∀ vars_consumed x' labels root edges mv n n1 n2 pred b.            
    BDD_ordered (root,edges,labels) vars_consumed ∧
    mv_dom_bdd mv (root,edges,labels)  ∧
    consumed_dom_bdd vars_consumed (root,edges,labels) ∧
    BDD_WF (root,edges,labels) ∧
    ALOOKUP edges n = SOME (n1,n2) ∧
    ALOOKUP labels n = SOME (non_termn (SOME x',pred)) ∧
    ALOOKUP mv x' = SOME b 
    ⇒
    ∃b'. ALOOKUP mv x' = SOME T ∧ BDD_pred_sem (root,edges,labels) mv n1 b' ∨
         ALOOKUP mv x' = SOME F ∧ BDD_pred_sem (root,edges,labels) mv n2 b'
Proof
  ntac 2 strip_tac >>
  measureInduct_on `THE(INDEX_OF x' vars_consumed)` >>
  rpt strip_tac >>
  Cases_on ‘b’ >> gvs[] >|[
    
    simp[Once BDD_pred_sem_cases] >>
    rgs[] >>
    Cases_on ‘ALOOKUP edges n1’ >> gvs[] >|[
      ‘MEM n1 (dom_range_edges edges)’ by  imp_res_tac lookup_edges_in_domain >>
      gvs[BDD_WF_def, is_lookup_ntl_def]
      ,
      
      PairCases_on ‘x’ >> gvs[] >>
     
      subgoal ‘∃pred x'.ALOOKUP labels n1 = SOME (non_termn (SOME x',pred))’ >-
       (
       rgs[Once BDD_WF_def, Once is_lookup_internal_def, Once lookup_is_some_def] >>
       ‘MEM n1 (dom_range_edges edges)’ by  imp_res_tac lookup_edges_in_domain >>
       first_x_assum (strip_assume_tac o (Q.SPECL [‘n1’])) >>
       gvs[]
       ) >>
      gvs[] >>
      
      subgoal ‘∃b . ALOOKUP mv x'' = SOME b’ >-
       (
       gvs[mv_dom_bdd_def, lookup_is_some_def]
       ) >>
      
      ‘MEM x' vars_consumed ∧ MEM x'' vars_consumed’ by rgs[Once consumed_dom_bdd_def] >>
      imp_res_tac MEM_INDEX_OF >>
      
      subgoal ‘THE (INDEX_OF x'' vars_consumed) < THE (INDEX_OF x' vars_consumed)’ >-
       (
       
       rgs[Once BDD_ordered_def]>>
       first_x_assum (strip_assume_tac o (Q.SPECL [‘n’,‘n1’, ‘n2’]))>>
       gvs[order_hold_def]
       ) >>
      
      first_x_assum (strip_assume_tac o (Q.SPECL [‘INDEX_OF (x'':string) (vars_consumed: string list)’])) >>
      gvs[] >>
      first_x_assum (strip_assume_tac o (Q.SPECL [‘x''’, ‘vars_consumed’])) >>
      gvs[] >>
      METIS_TAC[]
    ]
    ,
    
    simp[Once BDD_pred_sem_cases] >>
    rgs[] >>
    Cases_on ‘ALOOKUP edges n2’ >> gvs[] >|[
        ‘MEM n2 (dom_range_edges edges)’ by  imp_res_tac lookup_edges_in_domain >>
        gvs[BDD_WF_def, is_lookup_ntl_def]
        ,
        
        PairCases_on ‘x’ >> gvs[] >>

        subgoal ‘∃pred x'.ALOOKUP labels n2 = SOME (non_termn (SOME x',pred))’ >-
         (
         rgs[Once BDD_WF_def, Once is_lookup_internal_def, Once lookup_is_some_def] >>
         ‘MEM n2 (dom_range_edges edges)’ by  imp_res_tac lookup_edges_in_domain >>
         first_x_assum (strip_assume_tac o (Q.SPECL [‘n2’])) >>
         gvs[]
         ) >>
        gvs[] >>
        

        subgoal ‘∃b . ALOOKUP mv x'' = SOME b’ >-
         (
         gvs[mv_dom_bdd_def, lookup_is_some_def]
         ) >>
        
        
        ‘MEM x' vars_consumed ∧ MEM x'' vars_consumed’ by rgs[Once consumed_dom_bdd_def] >>
        imp_res_tac MEM_INDEX_OF >>
       
        
        subgoal ‘THE (INDEX_OF x'' vars_consumed) < THE (INDEX_OF x' vars_consumed)’ >-
         (
         rgs[Once BDD_ordered_def]>>
         first_x_assum (strip_assume_tac o (Q.SPECL [‘n’,‘n1’, ‘n2’])) >>
         gvs[order_hold_def]
         ) >>
        
        first_x_assum (strip_assume_tac o (Q.SPECL [‘INDEX_OF (x'':string) (vars_consumed: string list)’])) >>
        gvs[] >>
        first_x_assum (strip_assume_tac o (Q.SPECL [‘x''’, ‘vars_consumed’])) >>
        gvs[] >>
        METIS_TAC[]
      ]
                                           
    ]          
QED




Definition node_in_BDD_def:
  node_in_BDD n ((r,edges,labels):BDD) =
     MEM n (dom_range_edges edges)
End
           
                        
  
Theorem BDD_pred_sem_exsists:
  ∀ BDD mv n vars_consumed.
    BDD_ordered BDD vars_consumed ∧
    mv_dom_bdd mv BDD  ∧
    consumed_dom_bdd vars_consumed BDD ∧
    node_in_BDD n BDD ∧   (*todo: check this out*)
    BDD_WF BDD ⇒
    ∃ b . BDD_pred_sem BDD mv n b
Proof
 rgs[Once BDD_pred_sem_cases] >>
 rpt strip_tac >>

 PairCases_on ‘BDD’ >>
 rename1 ‘(root,edges,labels)’ >>

 rgs[] >>

 Cases_on ‘ALOOKUP edges n’ >> gvs[] >| [

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
     gvs[mv_dom_bdd_def, lookup_is_some_def]
     ) >>

    METIS_TAC[BDD_pred_sem_exsists_inter]
  ]
QED






     

(*              
                                 
Theorem new_layer_correct:
  ∀ BDD BDD'' vars_consumed h c c' mv.
    correct_sem BDD ∧
    BDD_WF BDD ∧
    BDD_ordered BDD vars_consumed ∧
    mv_dom_bdd mv BDD  ∧
    consumed_dom_bdd vars_consumed BDD ∧
    body_of_mk BDD h c = SOME (BDD'',c')
    ==>
    correct_sem BDD''
Proof

  namedCases ["r edges labels"] >>
  namedCases ["r'' edges'' labels''"] >>

  gvs[correct_sem_def] >>            
  Induct_on ‘BDD_pred_sem’ >>
  rpt strip_tac >> gvs[] >|[

    gvs[get_prop_def] >>
    Cases_on ‘p’ >>gvs[] >>
    Cases_on ‘p'’ >> gvs[from_pred_to_bool_def, apply_Sem_rule_def, Sem_rule_def]

    ,

    ‘r''=r’ by (gvs[body_of_mk_def] >> gvs[AllCaseEqs()]) >> gvs[] >>       

    res_tac >>

    

            
    ‘apply_Sem_rule (get_prop labels' n') mv = apply_Sem_rule (get_prop labels' n) mv’ 

            
    simp[Once get_prop_def] >>
    simp[apply_Sem_rule_def] >>
    gvs[]

    gvs[Once BDD_pred_sem_cases] >|[

        ‘’

   cheat


      ]

  ]


  (*      
  rpt strip_tac >>
  PairCases_on ‘BDD’ >>
  rename1 ‘(r,edges,labels)’ >>

  PairCases_on ‘BDD''’ >>
  rename1 ‘(r'',edges'',labels'')’ >>

  ‘r''=r’ by (gvs[body_of_mk_def] >> gvs[AllCaseEqs()]) >> gvs[] >>       
          
  simp[correct_sem_def] >>
  rpt strip_tac >>

  gvs[Once BDD_pred_sem_cases] >| [
    gvs[get_prop_def] >>
    Cases_on ‘p’ >>gvs[] >>
    Cases_on ‘p'’ >> gvs[from_pred_to_bool_def, apply_Sem_rule_def, Sem_rule_def]
    ,
    gvs[get_prop_def] >>
    gvs[apply_Sem_rule_def]
    
    (* this is too easy, check with the boss *)
  ]
*)
QED
        
*)

        

(*
        
∀ simp_leaves simp_leaves' n.
  determine_termn_list simp_leaves = simp_leaves' ∧
  ALOOKUP simp_leaves n = SOME (x,lbl,lbl') 
  ⇒
(  ∃p p'.
     (lbl  = non_termn (NONE, p ) ∨ lbl = (termn True) ∨ lbl = (termn False) ) ∧
     (lbl' = non_termn (NONE, p') ∨ lbl' = (termn True) ∨ lbl' = (termn False) ) )



                            
        
        
∀simp_leaves' simp_leaves new_labels c n lbl.
       ALL_DISTINCT (MAP FST simp_leaves') ∧
       determine_termn_list simp_leaves = simp_leaves' ∧
       mk_new_labels simp_leaves' c = new_labels ∧
       ALOOKUP new_labels n = SOME lbl ⇒
       (∃p. lbl = (non_termn (NONE,p)) ∨ lbl = (termn True) ∨ lbl = (termn False))


 rpt strip_tac >>
 assume_tac (INST_TYPE [“:'c” |-> “:label”  ] mk_new_labels_range_exsists)  >>
 first_x_assum (strip_assume_tac o (Q.SPECL [‘simp_leaves'’, ‘new_labels’, ‘(non_termn (SOME x,p))’, ‘n’, ‘c’])) >>
rgs[] >>

Cases_on ‘lbl’ >> rgs[] >|[
    gvs[]
,    
    
  ]          

*)
        

(*********************************************************************************************************************)
(* this proof requires WFness and ordered for intermidiate steps to be proven*)        

Theorem correct_sem_translation:
  ∀ vars vars_consumed BDD BDD' c.
    BDD_ordered BDD vars_consumed ∧
    correct_sem BDD ⇒
    (SOME BDD' = mk_BDDPred BDD vars_consumed vars c) ⇒
    correct_sem BDD' 
Proof
  Induct >| [
    rpt strip_tac >>
    gvs[mk_BDDPred_def]
    ,
    rpt strip_tac >>
    
    gvs[mk_BDDPred_def] >>
    gvs[AllCaseEqs()] >>
    ‘correct_sem BDD''’ by cheat >>
    ‘BDD_ordered  BDD'' (h::vars_consumed)’ by cheat >>
    res_tac >> METIS_TAC[]
  ]
QED



(*******************************************************)
(*                                                     *)
(*                      M E R G E                      *)
(*                                                     *)
(*******************************************************)


Definition mergable_def:        
mergable ((r,edges,labels):BDD)  n n' = 
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
  merge ((r,edges,labels):BDD) n n' =
  let edges' = merge_edges (edges:edges) n n' in
    let edges'' = ADELKEY n' edges' in
      let labels' = ADELKEY n' labels in
          (r,edges'',labels')
End


        
(*
EVAL “merge (1,[(1,2,3);(2,4,5);(3,4,5)],[]) 2 3”
*)


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
  ∀labels n'' r edges n' n mv b.
    BDD_WF (r,edges,labels) ∧
    n' ≠ n'' ∧
    ALOOKUP edges n'' = NONE ⇒
    BDD_pred_sem (r,edges,labels) mv n'' b =
    BDD_pred_sem (r,ADELKEY n' (merge_edges edges n n'),ADELKEY n' labels) mv n'' b
Proof
  rpt strip_tac >>
  simp[Once BDD_pred_sem_cases]>> gvs[] >>
  rpt strip_tac >>
  
  subgoal ‘ALOOKUP (merge_edges edges n n') n'' = NONE’ >-
   (
   imp_res_tac merge_lookup_none >>
   last_x_assum (strip_assume_tac o (Q.SPECL [‘n’]))
   ) >>
    
  subgoal ‘∃ p . ALOOKUP labels n'' = SOME p’ >-
    (
    gvs[BDD_WF_def] >>
    gvs[is_lookup_ntl_def]
    ) >>
    
  gvs[] >>
  
  simp[Once BDD_pred_sem_cases] >>
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
  ‘∃ x p. ALOOKUP labels n = SOME (non_termn (SOME x,p))’ by
    (gvs[BDD_WF_def] >>
     gvs[lookup_is_some_def, is_lookup_internal_def] >>
     res_tac >> gvs[]) >|[
    
    gvs[BDD_ordered_def] >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘n’, ‘n’, ‘nl’])) >>
    gvs[order_hold_def] >>
    
    gvs[consumed_dom_bdd_def] >>
    imp_res_tac MEM_INDEX_OF >>
    
    first_x_assum (strip_assume_tac o (Q.SPECL [‘i’, ‘i’])) >>
    gvs[] >>
    
    first_x_assum (strip_assume_tac o (Q.SPECL [‘i’, ‘i’])) >>
    gvs[]
    ,
    
    gvs[BDD_ordered_def] >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘n’, ‘nr’, ‘n’])) >>
    gvs[order_hold_def] >>
    
    gvs[consumed_dom_bdd_def] >>
    imp_res_tac MEM_INDEX_OF >>
    
    first_x_assum (strip_assume_tac o (Q.SPECL [‘i’, ‘i’])) >>
    gvs[] >>
    
    first_x_assum (strip_assume_tac o (Q.SPECL [‘i’, ‘i’])) >>
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
  ∀ x vars_consumed  r edges labels n n' n'' nl nr pred mv b.
    consumed_dom_bdd vars_consumed (r,edges,labels) ∧ 
    BDD_ordered (r,edges,labels) vars_consumed ∧
    BDD_WF (r,edges,labels) ∧
    mergable (r,edges,labels) n n' ∧
    n'' ≠ n' ∧
    ALOOKUP edges n'' = SOME (nr,nl) ∧
    ALOOKUP labels n'' = SOME (non_termn (SOME x,pred))
    ⇒
    (BDD_pred_sem (r,edges,labels) mv n'' b ⇔
       BDD_pred_sem (r,ADELKEY n' (merge_edges edges n n'),ADELKEY n' labels) mv n'' b)
Proof
  ntac 2 strip_tac >>
  measureInduct_on `THE(INDEX_OF x vars_consumed)` >>
  rpt strip_tac >>
  
  
  simp[Once BDD_pred_sem_cases]>> gvs[] >>
  
  simp[Once EQ_SYM_EQ, Once BDD_pred_sem_cases] >>
  gvs[ALOOKUP_ADELKEY] >>
  
  gvs[from_pred_to_bool_def] >>
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
             gvs[BDD_WF_def] >>
             gvs[lookup_is_some_def, is_lookup_internal_def] >>
             res_tac >>
             srw_tac [SatisfySimps.SATISFY_ss][]
             ) >>
            
            gvs[] >>
            
            
            subgoal ‘THE (INDEX_OF x' vars_consumed) < THE (INDEX_OF x vars_consumed)’ >-(
              rgs[Once BDD_ordered_def] >>
              first_x_assum (strip_assume_tac o (Q.SPECL [‘n''’,‘nr’,‘nl’])) >>
              gvs[order_hold_def] >>
                                  
              gvs[consumed_dom_bdd_def] >>
              imp_res_tac MEM_INDEX_OF >>   
                                  
              last_x_assum (strip_assume_tac o (Q.SPECL [‘i'’, ‘i’ , ‘x’,‘x'’, ‘pred’, ‘pred'’])) >>
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
          
          simp[Once BDD_pred_sem_cases] >>  gvs[ALOOKUP_ADELKEY] >>
          Cases_on ‘ALOOKUP (merge_edges edges n n') n’ >> gvs[] >|[
              ‘ALOOKUP edges n' = NONE’ by (metis_tac [merge_lookup_none]) >>
              simp[Once EQ_SYM_EQ, Once BDD_pred_sem_cases] 
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
                              simp[Once EQ_SYM_EQ, Once BDD_pred_sem_cases] >>
                              
                              
                              subgoal ‘THE (INDEX_OF x' vars_consumed) < THE (INDEX_OF x vars_consumed)’ >-
                               (
                               rgs[Once BDD_ordered_def] >>
                               first_x_assum (strip_assume_tac o (Q.SPECL [‘n''’,‘n'’,‘nl’])) >>
                               gvs[order_hold_def] >>
                               
                               gvs[consumed_dom_bdd_def] >>
                               imp_res_tac MEM_INDEX_OF >>   
                               
                               last_x_assum (strip_assume_tac o (Q.SPECL [‘i’, ‘i'’ , ‘x’,‘x'’, ‘pred’, ‘pred'’])) >>
                               gvs[] >>  
                               last_x_assum (strip_assume_tac o (Q.SPECL [‘i’, ‘i'’ , ‘x’,‘x'’, ‘pred’, ‘pred'’])) >>
                               gvs[] 
                               ) >>
                               
                              gvs[] >>
                              first_x_assum (strip_assume_tac o (Q.SPECL [‘INDEX_OF (x':string) (vars_consumed: string list)’])) >>
                              gvs[] >>
                              first_x_assum (strip_assume_tac o (Q.SPECL [‘x'’, ‘vars_consumed’])) >>
                              gvs[] >>
                              first_x_assum (strip_assume_tac o (Q.SPECL [‘r’, ‘edges’, ‘labels’, ‘n’, ‘n'’, ‘n’, ‘x'1''’, ‘x'0’,  ‘r'’, ‘mv’, ‘b’])) >>
                              rgs[] >>
                              
                              gvs[Once BDD_pred_sem_cases] >>
                              simp[Once BDD_pred_sem_cases] >> gvs[ALOOKUP_ADELKEY]
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
  ∀ labels vars_consumed n'' r edges n' n mv b.
    consumed_dom_bdd vars_consumed (r,edges,labels) ∧
    BDD_ordered (r,edges,labels) vars_consumed ∧
    BDD_WF (r,edges,labels) ∧
    mergable (r,edges,labels) n n' ∧
    n'' ≠ n'
    ⇒
    BDD_pred_sem (r,edges,labels) mv n'' b =
    BDD_pred_sem (r,ADELKEY n' (merge_edges edges n n'), ADELKEY n' labels) mv n'' b 
Proof

  rpt strip_tac >>
      
  Cases_on ‘ALOOKUP edges n''’ >> gvs[] >|[
    assume_tac  mergable_correct_leaf >> 
    last_x_assum (strip_assume_tac o (Q.SPECL [‘labels’,‘n''’,‘r’, ‘edges’, ‘n'’, ‘n’, ‘mv’, ‘b’])) >>
    gvs[]
    ,
    subgoal ‘∃pred x'. ALOOKUP labels n'' = SOME (non_termn (SOME x',pred))’ >-
     (
     gvs[BDD_WF_def] >>
     gvs[lookup_is_some_def, is_lookup_internal_def] >>
     res_tac >>
     srw_tac [SatisfySimps.SATISFY_ss][]
     ) >>
     
    PairCases_on ‘x’ >>
    metis_tac[mergable_correct_internal]
  ]

QED








                                                              
        
Theorem merge_correct:        
  ∀ r edges labels vars_consumed n n'.
    correct_sem (r,edges,labels) ∧
    BDD_WF (r,edges,labels) ∧
    consumed_dom_bdd vars_consumed (r,edges,labels) ∧
    BDD_ordered (r,edges,labels) vars_consumed ∧           
    mergable (r,edges,labels) n n'
    ==>
    correct_sem (merge (r,edges,labels) n n')
Proof
  rpt strip_tac >>   
  simp[Once correct_sem_def] >>
  rpt strip_tac >>
  gvs[merge_def] >>

  Cases_on ‘n' = n''’ >> gvs[] >|[
    ‘get_prop (ADELKEY n' labels) n' = NONE’ by cheat >> 
    gvs[apply_Sem_rule_def] >>
    ‘BDD_pred_sem
     (r,ADELKEY n' (merge_edges edges n n'),ADELKEY n' labels) mv n' (NONE)’ by cheat >>
    imp_res_tac BDD_pred_sem_determ
    ,
    
    assume_tac Lemma3 >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘labels’, ‘vars_consumed’, ‘n''’, ‘r’, ‘edges’, ‘n'’, ‘n’, ‘mv’, ‘b’])) >>
    gvs[] >>           
    gvs[correct_sem_def] >>
    res_tac >>
    
    gvs[get_prop_def]>> 
    gvs[Once BDD_pred_sem_cases]>>
    
    gvs[ALOOKUP_ADELKEY]
  ]
QED
 
   
(*******************************************************)
(*                                                     *)
(*                  E L I M I N A T E                  *)
(*                                                     *)
(*******************************************************)

Definition eleminatble_def:        
eleminatble ((r,edges,labels):BDD)  n n' = 
(n≠n' ∧ ALOOKUP edges n' = SOME (n,n) )
End
*)

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

    
