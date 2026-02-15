open HolKernel boolLib simpLib Parse bossLib;

open listTheory;
open alistTheory;
open rich_listTheory;

open p4_auxTheory;

open bdd_auxTheory;     
open bdd_genTheory;  
open bdd_gen_wfTheory;   
open bdd_gen_orderTheory;
open bdd_gen_correctTheory;



     
val _ = new_theory "bdd_isomorph";



(*******************************************************)
(*  BDD Isomorphism Theorems                           *)
(*                                                     *)
(*   These theorems define and prove properties of     *)
(*   graph isomorphisms between BDDs. Two BDDs are     *)
(*   isomorphic if there exists a bijection between    *)
(*   their nodes that preserves:                       *)
(*     1. Node type (terminal/internal)                *)
(*     2. Variable labels (for internal nodes)         *)
(*    3. Children relationships (edges)                *)
(*                                                     *)
(*   The main result (isomorphism_preserves_semantics) *)
(*   shows that isomorphic BDDs have identical         *)
(*                   semantics                         *)
(*******************************************************)



(*******************************************************)
(*  Helper Functions for Node Properties               *)
(*******************************************************)

Definition get_res_def:
  get_res labels n =
  (case ALOOKUP labels n of
   | SOME (termn (b,p)) => SOME b
   | _ => NONE
  )
End


Definition get_var_def:
  get_var labels n =
  (case ALOOKUP labels n of
   | SOME (non_termn (SOME x,p)) => SOME x
   | _ => NONE
  )
End


Definition leaf_is_terminal_def:
  leaf_is_terminal labels n =
  (case ALOOKUP labels n of
   | SOME (termn (b,p)) => T
   | _ => F
  )
End

      
Definition internal_is_non_terminal_def:
  internal_is_non_terminal labels n =
  (case ALOOKUP labels n of
   | SOME (non_termn (SOME x,p)) => T
   | _ => F
  )
End


(*******************************************************)
(*  Core Isomorphism Definition                        *)
(*******************************************************)        

(* Definirion: children_edges_eq defines when two nodes have matching structure
            - For leaf nodes: both have no children and same terminal value
            - For internal nodes: same variable, and children map via I *)
Definition children_edges_eq_def:
  children_edges_eq I (BDD1:('a,'b) BDD) (BDD2:('c,'b) BDD) n1 n2=
  let (r1,edges1,labels1) = BDD1 in
    let (r2,edges2,labels2) = BDD2 in
      case ALOOKUP edges1 n1 of
      | NONE => (ALOOKUP edges2 n2 = NONE ∧ leaf_is_terminal labels1 n1 ∧get_res labels1 n1 = get_res labels2 n2)
      | SOME (n1_left,n1_right) =>
          (
          case ALOOKUP edges2 n2 of
          | NONE => F
          | SOME (n2_left,n2_right) => (internal_is_non_terminal labels1 n1 ∧
                                        get_var labels1 n1 = get_var labels2 n2 ∧
                                        ALOOKUP I n1_left  = SOME n2_left ∧
                                        ALOOKUP I n1_right = SOME n2_right 
                                       )
          )
End

        
(*
 EVAL “ children_edges_eq [(0,3);(1,4);(2,5)]  
        (0,[(0,1,2)], [(0, non_termn(SOME "x", And (Var "x") (Var "y")));
                       (1,termn (("fwd",([2]:num list)) , True));
                       (2,termn (("drop",[]) , False))])

       (0,[(3,4,5)], [(3, non_termn(SOME "x", And (Var "x") (Var "y")));
                      (4,termn (("fwd",[2]) , True));
                      (5,termn (("drop",[]) , False))])

   0 3”;
*)



(* isIsomorph defines a graph isomorphism between BDDs
  I is a partial map from nodes of BDD1 to nodes of BDD2
   such that for every mapped node, the children edges match *)
Definition isIsomorph_def:
  isIsomorph I (BDD1:('a,'b) BDD) (BDD2:('c,'b) BDD) = 
  ∀ n1 n2.
      (node_in_BDD n1 BDD1 ∧ ALOOKUP I n1 = SOME n2 ⇒
       (node_in_BDD n2 BDD2 ∧ children_edges_eq I BDD1 BDD2 n1 n2))
End


(*******************************************************)
(*  Executable Version of Isomorphism                  *)
(*******************************************************)

(* Check isomorphism for a single node mapping *)
Definition apply_iso_check_def:
  apply_iso_check I BDD1 BDD2 n1 n1_map =     
  case n1_map of
  | NONE => T (* as dont care case*)
  | SOME n2 => (node_in_BDD n2 BDD2 ∧ children_edges_eq I BDD1 BDD2 n1 n2)
End


(* Check isomorphism for all nodes in a list *)   
Definition apply_iso_check_for_nodes_def:
  (apply_iso_check_for_nodes I (BDD1:('a,'b) BDD) (BDD2:('c,'b) BDD) [] = T) ∧
  (apply_iso_check_for_nodes I (BDD1:('a,'b) BDD) (BDD2:('c,'b) BDD) I_extended =
   EVERY (\(n1,n1_map).  apply_iso_check I BDD1 BDD2 n1 n1_map ) I_extended
  )
End


Definition their_i_map_def:
  their_i_map I all_nodes1=
  MAP (\n1. (n1 ,ALOOKUP I n1)) all_nodes1
End
        
        
(* Executable version of isIsomorph that checks all nodes in domain *)
Definition isIsomorph_exec_def:
  isIsomorph_exec I (BDD1:('a,'b) BDD) (BDD2:('c,'b) BDD) =
  let (r1,edges1,labels1) = BDD1 in
    let all_nodes1 = dom_range_edges edges1 in
      let I_extended = their_i_map I all_nodes1 in
        apply_iso_check_for_nodes I BDD1 BDD2 I_extended
End



(*
EVAL “ isIsomorph_exec [(0,3);(1,4);(2,5)]  
        (0,[(0,1,2)], [(0, non_termn(SOME "x", And (Var "x") (Var "y")));
                       (1,termn (("fwd",([2]:num list)) , True));
                       (2,termn (("drop",[]) , False))])

       (0,[(3,4,5)], [(3, non_termn(SOME "x", And (Var "x") (Var "y")));
                      (4,termn (("fwd",[2]) , True));
                      (5,termn (("drop",[]) , False))]) ”

*)
        

(*Executable definition is equivalent to abstract definition *)
Theorem isIsomorph_exe_abs_eq:
  ∀ BDD1 BDD2 I.
    isIsomorph_exec I (BDD1:('a,'b) BDD) (BDD2:('c,'b) BDD) = isIsomorph I BDD1 BDD2
Proof
  rpt strip_tac >>
  PairCases_on ‘BDD1’ >>
  PairCases_on ‘BDD2’ >>
  rename1 ‘isIsomorph_exec I' (r1,edges1,labels1) (r2,edges2,labels2)’ >>
  
  gvs[isIsomorph_exec_def, isIsomorph_def] >>
  EQ_TAC >>
    
  rpt strip_tac >>
  
  (
  Cases_on ‘their_i_map I' (dom_range_edges edges1)’ >-
   gvs[apply_iso_check_for_nodes_def, their_i_map_def, dom_range_edges_def, node_in_BDD_def] >>
   
  PairCases_on ‘h’ >>
  rename1 ‘their_i_map I' (dom_range_edges edges1) = (n1',n1_map')::t’ >>
  gvs[apply_iso_check_for_nodes_def, apply_iso_check_def] >>
                                     
  rpt (BasicProvers.full_case_tac >> gvs[]) >>
  gvs[node_in_BDD_def] >>
  gvs[their_i_map_def] >>
  
  Cases_on ‘dom_range_edges edges1’ >> gvs[] >>
  Cases_on ‘h=n1’ >> gvs[] >>
  
  gvs[EVERY_MAP] >>
  gvs[EVERY_MEM] >>
  res_tac >>
  rpt (BasicProvers.full_case_tac >> gvs[]) >>
  
  rpt strip_tac >>
  rpt (BasicProvers.full_case_tac >> gvs[]) >>
  res_tac)
QED



(*In well-formed BDD, nodes with edges have internal labels *)
Theorem node_internal_defined_wf:
  ∀ r edges labels n nl nr.
    BDD_WF (r,edges,labels) ∧
    node_in_BDD n (r,edges,labels) ∧ 
    ALOOKUP edges n = SOME (nl,nr) ⇒
    is_lookup_internal labels n 
Proof
  rpt strip_tac >>
  gvs[node_in_BDD_def, BDD_WF_def, lookup_is_some_def] >>
  res_tac
QED

        

(* Theorem node_leaf_defined_wf:
  ∀ r edges labels n.
    BDD_WF (r,edges,labels) ∧
    node_in_BDD n (r,edges,labels) ∧ 
    ALOOKUP edges n = NONE ⇒
    ALOOKUP labels n ≠ NONE ∧ (∃p b. ALOOKUP labels n = SOME (termn (b,p)) ∨
                                     is_lookup_ntl labels n)  
Proof
  rpt strip_tac >>
  gvs[node_in_BDD_def, BDD_WF_def] >>
  gvs[is_lookup_ntl_def]
QED *)



(* Isomorphism preserves semantics for leaf nodes *)
Theorem isomorphism_preserves_semantics_leaf:
  ∀ I r1 edges1 labels1 BDD2 rec1 rec2 n1 n2 mv b.
    isIsomorph I (r1,edges1,labels1) BDD2 ∧
    node_in_BDD n1 (r1,edges1,labels1) ∧
    ALOOKUP edges1 n1 = NONE ∧
    ALOOKUP I n1 = SOME n2 ⇒
    ((∃p. b = from_formula_to_action rec1 p mv ∧ ALOOKUP labels1 n1 = SOME p)
     ⇔
     BDD_sem rec2 BDD2 mv n2 b)
Proof
  rpt strip_tac >>
  gvs[isIsomorph_def] >>
  first_x_assum (strip_assume_tac o (Q.SPECL [‘n1’,‘n2’])) >>             
  gvs[children_edges_eq_def] >>
  PairCases_on ‘BDD2’ >> rename1 ‘(r2,edges2,labels2)’ >> gvs[] >>
  
  gvs[leaf_is_terminal_def] >>
  gvs[AllCaseEqs()] >>
  
  simp[Once BDD_sem_cases] >>
  fs[get_res_def] >>
  gvs[AllCaseEqs()] >>
  
  gvs[from_formula_to_action_def] 
QED



(*Internal nodes in isomorphism have matching outgoing edges *)
Theorem internal_iso_nodes_has_out_edges:
  ∀ I r1 edges1 labels1 r2 edges2 labels2 n1 n2 n1_left n1_right x p.        
    isIsomorph I (r1,edges1,labels1) (r2,edges2,labels2) ∧
    node_in_BDD n1 (r1,edges1,labels1) ∧
    ALOOKUP I n1 = SOME n2 ∧
    ALOOKUP edges1 n1 = SOME (n1_left,n1_right) ∧
    ALOOKUP labels1 n1 = SOME (non_termn (SOME x,p)) ⇒
       ∃ n2_left n2_right . ALOOKUP edges2 n2 = SOME (n2_left,n2_right) ∧
       ∃ p'. ALOOKUP labels2 n2 = SOME (non_termn (SOME x,p'))
Proof
  rpt strip_tac >>
  gvs[isIsomorph_def] >>
  first_x_assum (strip_assume_tac o (Q.SPECL [‘n1’,‘n2’])) >>             
  gvs[children_edges_eq_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> rgs[]) >>
  gvs[get_var_def] >>
  Cases_on ‘ALOOKUP labels2 n2’ >> gvs[] >>
  Cases_on ‘x'’ >> gvs[] >>
  Cases_on ‘p'’ >> gvs[] >>
  Cases_on ‘q'’ >> gvs[] 
QED


                                             
Triviality rw_iff:
∀ a b . (a ⇔ b) = (b ⇔ a) 
Proof
metis_tac[]
QED



(* Theorem: Isomorphism preserves semantics for internal nodes *)        
Theorem isomorphism_preserves_semantics_internal:
  ∀ vars_consumed x I r1 edges1 labels1 BDD2 n1 n2 rec1 rec2 mv b n1_left n1_right p.
    isIsomorph I (r1,edges1,labels1) BDD2 ∧
    node_in_BDD n1 (r1,edges1,labels1) ∧
    ALOOKUP I n1 = SOME n2 ∧
    
    BDD_ordered (r1,edges1,labels1) vars_consumed ∧
    consumed_dom_bdd vars_consumed (r1,edges1,labels1) ∧
    mv_dom_vars mv vars_consumed ∧

                
    ALOOKUP edges1 n1 = SOME (n1_left,n1_right) ∧           
    ALOOKUP labels1 n1 = SOME (non_termn (SOME x,p)) ⇒
    
    ((ALOOKUP mv x = SOME T ∧ BDD_sem rec1 (r1,edges1,labels1) mv n1_left b ∨
      ALOOKUP mv x = SOME F ∧ BDD_sem rec1 (r1,edges1,labels1) mv n1_right b)
     =
     BDD_sem rec2 BDD2 mv n2 b)
Proof
  ntac 2 strip_tac >>
  measureInduct_on ‘THE(INDEX_OF x vars_consumed)’ >>
  rpt strip_tac >>
  
  PairCases_on ‘BDD2’ >> rename1 ‘isIsomorph I' (r1,edges1,labels1) (r2,edges2,labels2)’ >> gvs[] >>
  
  subgoal ‘∃n2_left n2_right.
             ALOOKUP edges2 n2 = SOME (n2_left,n2_right) ∧
             ∃p'. ALOOKUP labels2 n2 = SOME (non_termn (SOME x,p'))’ >-
   (metis_tac[internal_iso_nodes_has_out_edges]) >>
  
  simp[rw_iff, Once BDD_sem_cases] >>
  
  subgoal ‘∃b. ALOOKUP mv x = SOME b’ >-
   (
   gvs[consumed_dom_bdd_def, mv_dom_vars_def, lookup_is_some_def] >>
   metis_tac[]
   ) >>
  
  
  
  subgoal ‘node_in_BDD n1_left (r1,edges1,labels1)  ∧
           node_in_BDD n2_left (r2,edges2,labels2)  ∧
           node_in_BDD n1_right (r1,edges1,labels1)  ∧
           node_in_BDD n2_right (r2,edges2,labels2)  ’ >-
   (gvs[node_in_BDD_def] >>
    imp_res_tac lookup_edges_in_domain >>
    gvs[]) >>
  
  
  subgoal ‘ALOOKUP I' n1_left = SOME n2_left ∧
           ALOOKUP I' n1_right = SOME n2_right ’ >-
   (
   rgs[isIsomorph_def] >>
   first_x_assum (strip_assume_tac o (Q.SPECL [‘n1’, ‘n2’])) >>
   rgs[] >>
   rgs[children_edges_eq_def]
   ) >>
  
  Cases_on ‘b'’ >> gvs[] >|[
    (* case b' is true, then left branch *)
    
    qpat_assum ‘isIsomorph I' (r1,edges1,labels1) (r2,edges2,labels2)’
               (fn thm => assume_tac (SIMP_RULE (srw_ss()) [Once isIsomorph_def] thm)) >>
    
    first_x_assum (strip_assume_tac o (Q.SPECL [‘n1_left’, ‘n2_left’])) >>
    gvs[] >>
    
    Cases_on ‘ALOOKUP edges1 n1_left’ >|[
      
      (*now if n1_left is a leaf, then n2_left is also a leaf*)
      rgs[children_edges_eq_def] >>
      rgs[leaf_is_terminal_def] >>
      rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
      rgs[get_res_def] >>
      rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>


      simp[Once BDD_sem_cases] >>
      simp[rw_iff, Once BDD_sem_cases] >>
      gvs[from_formula_to_action_def]  
      ,
      (* if n1_left is not a leaf, then n2_left is not, so we use IH to show that the children
       of n1_left are semantically equivelant to n2_left
       *)

      PairCases_on ‘x'’ >>
      rename1 ‘ALOOKUP edges1 n1_left = SOME (n1_left_l,n1_left_r)’ >>

      rgs[children_edges_eq_def] >>
      rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
      rename1 ‘ALOOKUP edges2 n2_left = SOME (n2_left_l,n2_left_r)’ >>

      gvs[internal_is_non_terminal_def] >>
      rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
      gvs[get_var_def] >>
      rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>


      subgoal ‘THE (INDEX_OF x' vars_consumed) < THE (INDEX_OF x vars_consumed)’ >-
       (imp_res_tac ordered_for_two_labels) >>
      
      first_x_assum (strip_assume_tac o (Q.SPECL [‘INDEX_OF (x':string) (vars_consumed: string list)’])) >>
      rgs[PULL_FORALL] >>
      first_x_assum (strip_assume_tac o (Q.SPECL [‘x'’, ‘vars_consumed’, ‘I'’, ‘r1’, ‘edges1’, ‘labels1’])) >> gvs[] >>
      first_x_assum (strip_assume_tac o (Q.SPECL [‘(r2,edges2,labels2)’, ‘n1_left’, ‘n2_left’, ‘rec1’, ‘rec2’])) >> gvs[] >>
      first_x_assum (strip_assume_tac o (Q.SPECL [‘mv’, ‘b’])) >> gvs[] >>

      gvs[] >>
      simp[Once BDD_sem_cases] >>
      simp[rw_iff, Once BDD_sem_cases]
        
    ]
                                        
    ,
    (* case b' is false, then right branch *)
    qpat_assum ‘isIsomorph I' (r1,edges1,labels1) (r2,edges2,labels2)’
               (fn thm => assume_tac (SIMP_RULE (srw_ss()) [Once isIsomorph_def] thm)) >>
    
    first_x_assum (strip_assume_tac o (Q.SPECL [‘n1_right’, ‘n2_right’])) >>
    gvs[] >>
    
    
    Cases_on ‘ALOOKUP edges1 n1_right’ >|[
        
        (*now if n1_left is a leaf, then n2_left is also a leaf*)
        rgs[children_edges_eq_def] >>
        rgs[leaf_is_terminal_def] >>
        rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
        rgs[get_res_def] >>
        rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
        
        
        simp[Once BDD_sem_cases] >>
        simp[rw_iff, Once BDD_sem_cases] >>
        gvs[from_formula_to_action_def]  
        ,
        (* if n1_left is not a leaf, then n2_left is not, so we use IH to show that the children
       of n   1_left are semantically equivelant to n2_left
         *)
        
        PairCases_on ‘x'’ >>
        rename1 ‘ALOOKUP edges1 n1_right = SOME (n1_right_l,n1_right_r)’ >>
        
        rgs[children_edges_eq_def] >>
        rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
        rename1 ‘ALOOKUP edges2 n2_right = SOME (n2_right_l,n2_right_r)’ >>
        
        gvs[internal_is_non_terminal_def] >>
        rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
        gvs[get_var_def] >>
        rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
        
        
        subgoal ‘THE (INDEX_OF x' vars_consumed) < THE (INDEX_OF x vars_consumed)’ >-
         (imp_res_tac ordered_for_two_labels) >>
        
        first_x_assum (strip_assume_tac o (Q.SPECL [‘INDEX_OF (x':string) (vars_consumed: string list)’])) >>
        rgs[PULL_FORALL] >>
        first_x_assum (strip_assume_tac o (Q.SPECL [‘x'’, ‘vars_consumed’, ‘I'’, ‘r1’, ‘edges1’, ‘labels1’])) >> gvs[] >>
        first_x_assum (strip_assume_tac o (Q.SPECL [‘(r2,edges2,labels2)’, ‘n1_right’, ‘n2_right’, ‘rec1’, ‘rec2’])) >> gvs[] >>
        first_x_assum (strip_assume_tac o (Q.SPECL [‘mv’, ‘b’])) >> gvs[] >>
        
        gvs[] >>
        simp[Once BDD_sem_cases] >>
        simp[rw_iff, Once BDD_sem_cases]
            
      ]
  ] 
QED




(*******************************************************)
(*  MAIN THEOREM: Isomorphic BDDs Have Same Semantics  *)
(*                                                     *)
(*  If two BDDs are isomorphic via mapping I, then    *)
(*  for any node n1 in BDD1 mapped to n2 in BDD2,     *)
(*  the semantics of both BDDs at those nodes are     *)
(*  identical under any assignment that covers all    *)
(*  variables in BDD1.                                 *)
(*******************************************************)

Theorem isomorphism_preserves_semantics:
  ∀ I BDD1 BDD2 n1 n2 rec1 rec2 vars_consumed mv b.
    isIsomorph I (BDD1:('a,'b) BDD) (BDD2:('c,'b) BDD) ∧
    ALOOKUP I n1 = SOME n2 ∧
    node_in_BDD n1 BDD1 ∧

    consumed_dom_bdd vars_consumed BDD1 ∧
    mv_dom_vars mv vars_consumed ∧

                
    BDD_ordered BDD1 vars_consumed ∧
    BDD_WF BDD1 ⇒
    (BDD_sem rec1 BDD1 mv n1 b = BDD_sem rec2 BDD2 mv n2 b)
Proof

  rpt strip_tac >>
  simp[Once BDD_sem_cases] >>
  PairCases_on ‘BDD1’ >> rename1 ‘(r1,edges1,labels1)’ >> gvs[] >>

  Cases_on ‘ALOOKUP edges1 n1’ >> gvs[] >-
   metis_tac[isomorphism_preserves_semantics_leaf] >>
  

  PairCases_on ‘x’ >> rename1 ‘(n1_left,n1_right)’ >> gvs[] >>
  imp_res_tac node_internal_defined_wf >>
  gvs[is_lookup_internal_def] >>
  imp_res_tac isomorphism_preserves_semantics_internal >>
  gvs[]

QED




val _ = export_theory ();
