open HolKernel boolLib liteLib simpLib Parse bossLib;
open arithmeticTheory stringTheory containerTheory pred_setTheory
     listTheory finite_mapTheory;

open bitstringTheory;
open wordsTheory;
open optionTheory;
open sumTheory;
open ottTheory;
open pairTheory;
open rich_listTheory;
open alistTheory;
open numeralTheory;
open set_relationTheory;
open pred_setLib;

open p4_auxTheory;


val _ = new_theory "bdd_gen";




    
(******************************************************)
(*   generalized types for a structure and BDD graph  *)    
(******************************************************)
    
Hol_datatype `decision_structure = <| sem : 'a -> ((string,bool) alist) -> 'b option ;
                                      sub : 'a -> string -> bool -> 'a ;
                                      simp : 'a -> 'a ;
                                      final : 'a -> 'b option;
                                      fv : 'a -> string list
                                    |>`;
                                                              
(* BDD types *)
val _ = type_abbrev("edges", ``:(num , (num # num)) alist``);


val _ = Hol_datatype `
                     label = termn of ('b # 'a )
                            | non_termn of (string option #  'a)`;

        
                                                                       
Type labelings = ``:(num , ('a,'b) label) alist``;
val _ = type_abbrev("BDD", ``:num # edges # ('a,'b) labelings``);





    
(******************************************************)
(* generalized definition (relation) of BDD semantics *)    
(******************************************************)

Definition from_formula_to_action_def:
  from_formula_to_action (rec: ('a,'b) decision_structure) p mv =
  case p of
  |  (termn (action,_))  => SOME action
  |  (non_termn (_,p)) => rec.sem p mv
End
   

   
Inductive BDD_sem:
  
[bdd_red_leaf:]
  ( ∀ (rec: ('a,'b) decision_structure) (r:num) (edges:edges) (labels: ('a,'b) labelings) (mv:(string#bool)list) (n:num) (p:('a,'b)label).
      ALOOKUP edges n = NONE ∧
      ALOOKUP labels n  = SOME p  
      ⇒      
      BDD_sem rec (r,edges,labels) mv n (from_formula_to_action rec p mv) 
  )
  
  
[bdd_red_T:]
  ( ∀ (rec: ('a,'b) decision_structure) (root:num) (edges:edges) (labels: ('a,'b) labelings) (mv:(string#bool)list) (n:num) (l:num) (r:num)  (pred:'a) (x:string) (b': 'b option).
      ALOOKUP edges n = SOME (l,r) ∧
      ALOOKUP labels n  = SOME (non_termn (SOME x ,pred)) ∧
      ALOOKUP mv x = SOME T ∧
      BDD_sem rec (root,edges,labels) mv l b'
      ⇒      
      BDD_sem rec (root,edges,labels) mv n b'
  )
  
[bdd_red_F:]
  ( ∀ (rec: ('a,'b) decision_structure) (root:num) (edges:edges) (labels: ('a,'b) labelings) (mv:(string#bool)list) (n:num) (l:num) (r:num) (pred:'a) (x:string) (b':'b option).
      ALOOKUP edges n = SOME (l,r) ∧
      ALOOKUP labels n  = SOME (non_termn (SOME x ,pred)) ∧
      ALOOKUP mv x = SOME F ∧
      BDD_sem rec (root,edges,labels) mv r b'
      ⇒      
      BDD_sem rec (root,edges,labels) mv n b'
  )            

End  





     


(**********************************************)
(* generalised definitions for creating a BDD *)
(**********************************************)

(* get leaves definition *)
Definition get_leaves_list_def:
  get_leaves_list (edges : edges) =
  nub (FILTER (\x. ~(MEM x (MAP FST edges))) 
              (FLAT (MAP (\(k, (v1, v2)). [v1; v2]) edges)))
End

        
Definition getLeaves_def:
  getLeaves [] r = SOME [r] ∧
  getLeaves edges r =
  ( case (get_leaves_list edges) of
    | [] => NONE
    | l => SOME l
  )
End


        
(* get labels identified by the leafs *)
Definition getLabels_def:
  (getLabels (labels:('a,'b) labelings) [] = SOME [] ) ∧
  (getLabels labels (n::leaves) =
   case (getLabels labels leaves) of
   | SOME l =>
       (
       case (ALOOKUP labels n) of
       | NONE => NONE
       | SOME lbl => SOME ((n,lbl)::l)
       )
   | NONE => NONE
  )
End



(* from leaves's labels extract teh terminal ones as we wanna discard them *)        
Definition extract_nontermn_def:
  extract_nontermn [] = SOME [] ∧
  extract_nontermn ((n,l)::leaves_labels) =
  case (extract_nontermn leaves_labels) of
  | SOME l' => (
    case l of
    | termn p  => SOME l'
    | non_termn (NONE , p) => SOME ((n ,p)::l')
    | non_termn (SOME x,p) => NONE
    ) 
  | NONE => NONE
End

        

Definition leaves_pred_sub_def:
  leaves_pred_sub rec (nodes_labels) x =
  MAP
  (\(n,p).(n,x, rec.sub p x T, rec.sub p x F)) nodes_labels 
End



Definition simp_pred_list_def:
  simp_pred_list rec leaves_sub =
  MAP (\(n,x,p,p'). (n,x,rec.simp p , rec.simp p')) leaves_sub
End


        
Definition determine_termn_def:
  determine_termn rec p =
  case rec.final(p) of
  | SOME b => termn (b, p)
  | _ => non_termn (NONE,p) 
End

        

Definition determine_termn_list_def:
  determine_termn_list rec nodes_simp =
   MAP (\(n,x,p,p'). (n, x, determine_termn rec p , determine_termn rec p' )) nodes_simp
End


        
Definition mk_new_labels_def:
  mk_new_labels [] (c:num) =  [] ∧
  mk_new_labels ((n,x',(label,label'))::rest) c =  (c, label)::(c+1, label')::(mk_new_labels rest (c+2)) 
End
        


Definition mk_new_edges_def:
  mk_new_edges []                c =  [] ∧
  mk_new_edges ((n:num,x',(p,p'))::rest) (c:num) =  (n, c, c+1)::(mk_new_edges rest (c+2))     
End


        
Definition non_term_leaf_updt_def:
  non_term_leaf_updt l1 x =
    MAP (λ(n, lbl).
      case lbl of
      | termn (f,p) => (n, termn (f,p))
      | non_termn (NONE, p) => (n, non_termn (SOME x, p))
      | non_termn (SOME x', p) => (n, non_termn (SOME x', p))
        ) l1
End



Definition body_of_mk_def:
  body_of_mk rec (BDD:('a,'b) BDD) (x:string) (c:num) =
  (let (r,edges,labels) = BDD in
     (case getLeaves edges r of
      | SOME leaves =>
          (case (getLabels labels leaves) of
           | SOME leaves_labels =>
               ( case (extract_nontermn leaves_labels) of
                 | SOME leaves_nontermn =>
                     ( let leaves_sub = leaves_pred_sub rec leaves_nontermn x in
                         let simp_leaves = simp_pred_list rec leaves_sub in
                           let simp_leaves' = determine_termn_list rec simp_leaves in
                             let new_labels = mk_new_labels simp_leaves' c in
                               let new_edges = mk_new_edges simp_leaves' c in
                                 let label_leaf_updated = non_term_leaf_updt labels x
                                 in
                                   SOME (((r,  edges ++ new_edges, label_leaf_updated++new_labels):(('a,'b)BDD)),
                                         c + (LENGTH new_labels) 
                                        )             
                     )
                 | NONE => NONE
               )
           | NONE => NONE
          )
      | NONE => NONE
     )
  )
End



Definition mk_BDDPred_def:
  (mk_BDDPred rec (BDD:('a,'b) BDD) l [] c = SOME BDD) ∧
  (mk_BDDPred rec (BDD) l (x::xs) c =
   case (body_of_mk rec BDD (x:string) (c:num)) of
   | SOME (BDD',c') => mk_BDDPred rec BDD' (x::l) xs c'
   | NONE => NONE 
  )
End

        

(*
EVAL “mk_BDDPred pred_structure (0,[],[(0, non_termn (NONE, (Var "a")))]) [] ["a"] 1”;
EVAL “mk_BDDPred pred_structure (0,[],[(0, non_termn (SOME "a", (Var "a")))]) [] ["a"] 1”;
EVAL “mk_BDDPred pred_structure (0,[],[(0, non_termn (NONE, (And (Var "a") (Var "b"))))]) [] ["a";"b"] 1”;
EVAL “mk_BDDPred pred_structure (0,[],[(0, non_termn (NONE, Or (And (Var "a") (Var "b")) (Var "c")  ))]) [] ["a";"b";"c"] 1”;
EVAL “mk_BDDPred pred_structure (0,[],[(0, non_termn (NONE, Or (Var "a") (Var "b")))]) [] ["a";"b";"c"] 1”;
EVAL “mk_BDDPred pred_structure (0,[],[(0, non_termn (NONE, Or (Var "a") (Var "b")))]) [] ["a";"b";"c"] 1”;
*)

(*
val toBDD_pred_def = Define `
  toBDD_pred P vars = mk_BDDPred (0, [], [(0, non_termn ( NONE , P))]) vars 1`;
*)




(**********************************************)
(* generalised definitions for BDD WFness     *)
(**********************************************)

        

val lookup_is_some_def = Define `
    lookup_is_some l1 n =
     ? y . ALOOKUP l1 n = SOME y 
`;
        
val is_lookup_internal_def = Define `
    is_lookup_internal l1 n =
     ? x p . ALOOKUP l1 n = SOME (non_termn (SOME x, p))
`;

val is_lookup_ntl_def = Define `
    is_lookup_ntl l1 n =
     ? p . ALOOKUP l1 n = SOME (non_termn (NONE, p))
`;

        

Definition dom_range_edges_def:
  dom_range_edges edges = 
   nub (FLAT (MAP (λ(k,v1,v2). [k; v1; v2]) edges))
End


        
Definition dom_labels_def:
  dom_labels labels = 
  MAP FST labels
End

        
        
(* i decided to make it domain of edges instead of labels cause
all the proofs has split on edges and should prove labels*)

Definition BDD_WF_def:
  BDD_WF ((r,edges,labels):('a,'b)BDD) =
  (ALL_DISTINCT (MAP FST edges)  ∧ ALL_DISTINCT (MAP FST labels) ∧
   (∀ n . MEM n (dom_range_edges edges) ⇒
          (lookup_is_some edges n ⇔ is_lookup_internal labels n )) ∧
    (∀ n . MEM n (dom_range_edges edges) ⇒  
       (ALOOKUP edges n = NONE 
                ⇔   (is_lookup_ntl labels n
                     ∨ ∃ p b .ALOOKUP labels n= SOME (termn (b,p))))
    ) ∧
    (edges = [] ⇒ ∃ p . labels = [(r,p)]) ∧
    (edges ≠ [] ⇒ ∀ n . (MEM n (dom_range_edges edges) ⇔ MEM n (MAP FST labels) ) )
  )
End




(**********************************************)
(* generalised definitions for BDD order      *)
(**********************************************)

Definition is_lbl_leaf_def:
  is_lbl_leaf (non_termn(SOME x,p)) = F ∧
  is_lbl_leaf (non_termn(NONE,p)) = T ∧
  is_lbl_leaf (termn (b,p)) = T  
End


        
Definition order_hold_def:
  order_hold labels xl n n' =
  ∀ i i' x x' p p' (* lbl *).
  (ALOOKUP labels n  =  SOME (non_termn(SOME x,  p )) ∧
   ALOOKUP labels n' =  SOME (non_termn(SOME x', p')) ∧
   INDEX_OF x  xl = SOME i ∧
   INDEX_OF x' xl = SOME i' 
   ⇒ 
   i' < i)
End
           

Definition BDD_ordered_def:
  BDD_ordered ((r,edges,labels):('a,'b)BDD) xl =
  ∀ n n' n''.
    ALOOKUP edges n = SOME (n',n'') ⇒
    (order_hold labels xl n n' ∧ order_hold labels xl  n n'')
End




(******************************************************)
(*    other definitions must hold out of our control  *)
(******************************************************)

     
Definition consumed_dom_bdd_def:
  consumed_dom_bdd vars_consumed ((root,edges,labels):('a,'b)BDD) = 
  ∀ n p x.
    (ALOOKUP labels n = SOME (non_termn (SOME x,p))) ⇒
    MEM x vars_consumed
End        

(*
Definition mv_dom_bdd_def:
  mv_dom_bdd mv ((root,edges,labels):('a,'b)BDD) = 
  ∀ n p x.
    (ALOOKUP labels n = SOME (non_termn (SOME x,p))) ⇒
    lookup_is_some mv x
End
*)

Definition mv_dom_vars_def:
  mv_dom_vars mv vars = 
  ∀ x.
    MEM x vars ⇒
    lookup_is_some mv x
End

    
Definition range_c_def:
  range_c c ((r,edges,labels):('a,'b)BDD) =
   (EVERY (\n. c > n) (MAP FST labels))
End




(************************************************)
(* generalised definitions for BDD correctness  *)
(************************************************)

        
Definition op_sem_def:
  op_sem rec opp mv =
  case opp of
  | SOME p => rec.sem p mv
  | NONE => NONE
End


        
Definition get_prop_def:
  get_prop labels n =
  (case ALOOKUP labels n of
   | SOME (termn (b,p)) => SOME p
   | SOME (non_termn (x,p)) => SOME p
   | NONE => NONE
  )
End


Definition fv_in_p_def:
  fv_in_p rec p (mv:(string#bool) list) =
        (∀x. MEM x (rec.fv p) ⇒ (∃b. ALOOKUP mv x = SOME b))
End


Definition fv_in_vars_def:
  fv_in_vars rec p vars =
        (∀x. MEM x (rec.fv p) ⇒ MEM x vars)
End


Definition fv_in_labels_def:
  fv_in_labels rec labels vars =
  ∀ n opx p. (ALOOKUP labels n = SOME (non_termn (opx,p)) ⇒
         fv_in_vars rec p vars )  
End


Definition fv_in_BDD_def:
  fv_in_BDD rec (r,edges,labels) vars =
  fv_in_labels rec labels vars 
End


Definition correct_sem_def:
  correct_sem rec (BDD:('a,'b)BDD) vars =
  ∀ n mv b r edges labels.
    BDD = (r,edges,labels) ∧
    mv_dom_vars mv vars  ∧
    BDD_sem rec BDD mv n b ⇒
    b = op_sem rec (get_prop labels n) mv         
End  

(*
Definition correct_sem_def:
  correct_sem rec (BDD:('a,'b)BDD)  =
  ∀ r edges labels.
    BDD = (r,edges,labels) ==>
  ! n .
  ! mv .
    MEM n (all_edges edges)
    mv_dom_bdd mv BDD  ∧
    fv_in_vars rec (get_prop labels n) mv ==>
  !b .
    BDD_sem rec BDD mv n b ⇒
    b = op_sem rec (get_prop labels n) mv         
End  
*)

Definition valid_BDD_def:
  valid_BDD rec (BDD:('a,'b)BDD) vars vars_consumed =
    (BDD_WF BDD  ∧
    BDD_ordered BDD vars_consumed ∧
    fv_in_BDD rec BDD ((REVERSE vars)++vars_consumed) ∧
    consumed_dom_bdd vars_consumed BDD)
End  

(******************************************************)
(*                  rec  properties                   *)
(******************************************************)
        

Definition prop1_def:
  prop1 (rec:('a,'b)decision_structure) =
  ∀ mv h b p.
    ALOOKUP mv h = SOME b ∧ fv_in_p rec p mv ⇒
    (rec.sem (rec.simp (rec.sub p h b)) mv = rec.sem p mv)
End

(* version that works *)
Definition prop2_def:
  prop2 rec =
  ∀ mv h b p q.
    ALOOKUP mv h = SOME b ∧
    fv_in_p rec p mv ⇒
    rec.final (rec.simp (rec.sub p h b)) = SOME q ⇒
    (SOME q = rec.sem p mv )
End


Definition prop3_def:
  prop3 rec =
  ∀ mv h b p q.
    rec.final (rec.simp (rec.sub p h b)) = SOME q ⇒
    rec.sem (rec.simp (rec.sub p h b)) mv = SOME q
End


Definition prop4_def:
  prop4 rec =    
  ∀ varslist prop_parent p b h.
  rec.simp (rec.sub prop_parent h b) = p ∧
  fv_in_vars rec prop_parent varslist ⇒
  fv_in_vars rec p varslist
End


(******************************************************)
(*                    MERGE Def                       *)
(******************************************************)

(*        
Definition mergable_def:        
mergable ((r,edges,labels):('a,'b) BDD)  n n' = 
(n≠n' ∧ ALOOKUP edges n = ALOOKUP edges n' ∧
 ALOOKUP labels n = ALOOKUP labels n'∧ ALOOKUP labels n'  ≠ NONE )
End
*)


Definition eq_vars_in_labels_def:
  eq_vars_in_labels labels n n' =
    case (ALOOKUP labels n', ALOOKUP labels n) of
    | (SOME (termn (a,_)), SOME (termn (a',_))) => (a = a')
    | (SOME (non_termn (SOME x,_)), SOME (non_termn (SOME x',_))) => (x = x')
    | (SOME (non_termn (NONE, p)), SOME (non_termn (NONE,p'))) => (p=p')
    | _ => F
End 
           
    
Definition mergable_def:        
  mergable ((r,edges,labels):('a,'b) BDD)  n n' = 
  (n≠n' ∧ ALOOKUP edges n = ALOOKUP edges n' ∧
   eq_vars_in_labels labels n n' ∧ ALOOKUP labels n'  ≠ NONE )
End
      
       
(*
EVAL “mergable (0,[(0,1,2)],
        [(0,non_termn (SOME "a",Or (Var "a") (Not (Var "a"))));
         (1,termn (T,True)); (2,termn (F,False));
         (3,non_termn (SOME "a",Or (Var "c") (Not (Var "a"))))]) 0 3”
*)
        
        
Definition merge_edges_def:
  merge_edges (edges:edges) n n' =
   MAP (\(a,b,c). ( a, if (b=n' ∧ c=n') then (n,n)
                 else if (b=n') then (n,c)
                 else if (c=n') then (b,n)
                     else (b,c))) edges 
End



Definition merge_def:
  merge ((r,edges,labels):('a,'b) BDD) n n' =
  let edges' = merge_edges (edges:edges) n n' in
    let edges'' = ADELKEY n' edges' in
      let labels' = ADELKEY n' labels in
          (r,edges'',labels')
End
        
(*
EVAL “merge (1,[(1,2,3);(2,4,5);(3,4,5)],[]) 2 3”
*)


(* the parent ≠ n here is important 
   case we do not have ultimate root in the graph.
   assume two roots can be eliminated, this wf condition of 
    the nodes in edges being found after elminate fails
*)    

Definition has_parent_def:
  has_parent edges n n' =
  EXISTS (λ(parent, (left, right)). (left = n' ∨ right = n') 
                                    ∧ parent ≠ n' ∧ parent ≠ n) edges
End


(* TODO: remove lookup *)
Definition eliminable_def:
  eliminable ((r,edges,labels):('a,'b)BDD) n = 
    case ALOOKUP edges n of
      |SOME (n1, n2) =>
        if n1 = n2 ∧
           n1 ≠ n ∧
           ALOOKUP labels n1 ≠ NONE ∧
           ALOOKUP labels n ≠ NONE ∧
           has_parent edges n1 n
        then SOME n1
        else NONE
    | NONE => NONE
End









(*******************************************************)
(*         Optimzations and their termination          *)
(*                       proofs                        *)
(*******************************************************)



(* basic optimization application on the BDD tree *)
(* merge part *)
Definition merge_BDD_def:
  merge_BDD (BDD:('a,'b) BDD) n [] = BDD ∧
  merge_BDD (BDD:('a,'b) BDD) n (n'::nl) = 
  (case mergable BDD n n' of
   | F => merge_BDD BDD n nl
   | T => merge_BDD (merge BDD n n') n nl
  )
End


Definition operate_opt1_def:
  (operate_opt1 (BDD:('a,'b) BDD)  ([]:num list)  (all_nodes:num list) = (BDD:('a,'b) BDD)) ∧
  (operate_opt1 BDD (n::rest) all_nodes = (operate_opt1 (merge_BDD BDD n all_nodes) rest all_nodes) )   
End
        

Definition bdd_optminzation1_def:
  bdd_optminzation1 (BDD:('a,'b) BDD) =
  let (r,edges,labels) = BDD in
    let all_nodes = MAP FST labels in
        operate_opt1 BDD all_nodes all_nodes
End



(*
Definition edges_project_def:
  edges_project ((r,edges,labels):('a,'b)BDD) nl = 
    everything in nl is in the domain od edges'
End
*)


(* here we use the projection *)
        
(* eliminate part *) 
Definition eliminate_BDD_def:
  eliminate_BDD (BDD:('a,'b) BDD) [] = BDD ∧
  eliminate_BDD (BDD:('a,'b) BDD) (n::nl) = 
  (case eliminable BDD n of
   | NONE => eliminate_BDD BDD nl
   | SOME n' => eliminate_BDD (merge BDD n' n) nl
  )
End

Definition operate_opt2_def:
  (operate_opt2 (BDD:('a,'b) BDD) ([]:num list)   (all_nodes:num list) = (BDD:('a,'b) BDD)) ∧
  (operate_opt2 BDD (n::rest) (all_nodes:num list) =  (operate_opt2 (eliminate_BDD BDD all_nodes) rest) (all_nodes:num list)) 
End
  
Definition bdd_optminzation2_def:
  bdd_optminzation2 (BDD:('a,'b) BDD) =
  let (r,edges,labels) = BDD in
    let all_nodes = MAP FST labels in
        operate_opt2 BDD all_nodes all_nodes
End




(* proof of optimization 1 merge  termination *)
(* First, we need a measure function that decreases with each optimization step *)
Definition BDD_label_length_def:
  BDD_label_length (BDD:('a,'b) BDD) =
  let (r,edges,labels) = BDD in
  LENGTH labels
End





(* termination proof *)
Theorem merge_trio_extract_triv:
  ∀ r edges labels n n'.
  merge (r,edges,labels) n n' = (r, ADELKEY n' (merge_edges edges n n'), ADELKEY n' labels)
Proof
  gvs[merge_def]
QED
        

        
Theorem merge_length_labels_less:
  ∀ r edges labels n n'.
    MEM n' (MAP FST labels) ⇒
        BDD_label_length (merge (r,edges,labels) n n') < BDD_label_length (r,edges,labels)
Proof
  gvs[BDD_label_length_def, merge_def] >>
  Induct_on ‘labels’ >>
  rpt strip_tac >>
  gvs[] >|[
    PairCases_on ‘h’ >> gvs[ADELKEY_def, SUC_ADD_ONE] >>
    ‘LENGTH (FILTER (λp. FST p ≠ h0) labels) ≤ LENGTH labels’ by gvs[LENGTH_FILTER_LEQ] >>
    decide_tac
    ,
    res_tac >>
    gvs[ADELKEY_def, SUC_ADD_ONE] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
    gvs[ADELKEY_def, SUC_ADD_ONE] >>
    ‘LENGTH (FILTER (λp. FST p ≠ FST h) labels) ≤ LENGTH labels’ by gvs[LENGTH_FILTER_LEQ] >>
    decide_tac
  ]       
QED




        
        

Theorem BDD_label_length_neq:
  ∀ BDD BDD'.
    BDD_label_length BDD <  BDD_label_length BDD' ⇒  BDD ≠ BDD'
Proof
  rpt strip_tac >>
  PairCases_on ‘BDD’ >>
  PairCases_on ‘BDD'’ >>
  gvs[BDD_label_length_def] 
QED
      


Theorem merge_decrease:
  ∀ BDD n n'.
    mergable BDD n n' ⇒
    BDD_label_length (merge BDD n n') < BDD_label_length BDD
Proof
  rpt strip_tac >>
  PairCases_on ‘BDD’ >>
  rename1 ‘(r,edges,labels)’ >>
  gvs[mergable_def] >>
  ‘MEM n' (MAP FST labels)’ by gvs[ALOOKUP_NONE] >>
  gvs[merge_length_labels_less]
QED

  
Theorem merge_BDD_decrease:
  ∀ l BDD n .      
    merge_BDD BDD n l ≠ BDD ⇒
    BDD_label_length (merge_BDD BDD n l) <  BDD_label_length BDD
Proof
  Induct_on ‘l’ >>
  rpt strip_tac >>
  gvs[merge_BDD_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> rgs[]) >>
  Cases_on ‘(merge BDD n h) = BDD’ >> gvs[] >>
  first_x_assum (strip_assume_tac o (Q.SPECL [‘(merge BDD n h)’, ‘n’])) >>
  gvs[] >>
    
  ‘BDD_label_length (merge BDD n h)  < BDD_label_length BDD’ by gvs[merge_decrease] >>
  imp_res_tac BDD_label_length_neq >>
  Cases_on ‘merge_BDD (merge BDD n h) n l = merge BDD n h’ >> gvs[]                                     
QED



Theorem ADELKEY_LENGTH_BOUND:
  ∀ l c n. LENGTH l < c ⇒
           LENGTH (ADELKEY n l) < c
Proof
  Induct >>
  rw[ADELKEY_def] >>
  PairCases_on ‘h’ >> gvs[ADELKEY_def, SUC_ADD_ONE] >>
  res_tac >>                    
  ‘LENGTH (FILTER (λp. FST p ≠ n) l) ≤ LENGTH l’ by gvs[LENGTH_FILTER_LEQ] >>
  decide_tac
QED



                   
Theorem merge_less_than_const:
  ∀ BDD n n' c.
    BDD_label_length BDD < c ∧
    mergable BDD n n' ⇒
    BDD_label_length (merge BDD n n') < c
Proof        
  rpt strip_tac >>
  PairCases_on ‘BDD’ >>
  rename1 ‘(r,edges,labels)’ >>
  gvs[mergable_def] >>
  gvs[merge_trio_extract_triv, BDD_label_length_def] >>
  gvs[ADELKEY_LENGTH_BOUND]             
QED

             
Theorem eliminate_decrease:
  ∀ BDD h n.
    eliminable BDD n = SOME h ⇒
    BDD_label_length (merge BDD h n) < BDD_label_length BDD
Proof
  rpt strip_tac >>
  PairCases_on ‘BDD’ >>
  rename1 ‘(r,edges,labels)’ >>
  gvs[eliminable_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
                       
  ‘MEM n (MAP FST labels)’ by gvs[ALOOKUP_NONE] >>
  gvs[merge_length_labels_less]
QED


        
Theorem merge_BDD_less_than_const:
  ∀ l BDD n c .
    BDD_label_length BDD < c ⇒
    (BDD_label_length (merge_BDD BDD n l) < c ∧ BDD_label_length (eliminate_BDD BDD l) < c) 
Proof

  Induct >>
  rpt strip_tac >>
  gvs[merge_BDD_def, eliminate_BDD_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> rgs[]) >>
  res_tac >|[
      
    Cases_on ‘(merge BDD n h) = BDD’ >> gvs[] >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘(merge BDD n h)’, ‘n’, ‘c’])) >>
    gvs[] >>
    
    ‘BDD_label_length (merge BDD n h)  < BDD_label_length BDD’ by gvs[merge_decrease] >>
    imp_res_tac BDD_label_length_neq >>
    Cases_on ‘merge_BDD (merge BDD n h) n l = merge BDD n h’ >> gvs[]       
    ,

           
    Cases_on ‘(merge BDD h n) = BDD’ >> gvs[] >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘(merge BDD h n)’, ‘n’, ‘c’])) >>
    gvs[] >>
    
    ‘BDD_label_length (merge BDD x h)  < BDD_label_length BDD’ by gvs[eliminate_decrease] >>
    imp_res_tac BDD_label_length_neq >>
    Cases_on ‘merge_BDD (merge BDD x h) n l = merge BDD x h’ >> gvs[]   >>
             cheat
    
  ]
QED


        


        
        
        
Theorem less_imp_less_in_length_label:
  ∀ BDD (n:num) l l'.
    (BDD_label_length BDD < n ⇒
     BDD_label_length  (operate_opt1 BDD  l l') <  n ∧
     BDD_label_length  (operate_opt2 BDD  l l') <  n)
    
Proof
  Induct_on ‘l’ >>
  gvs[operate_opt1_def, operate_opt2_def] >>
  rpt strip_tac >>
  res_tac >>  cheat >>

  ‘BDD_label_length (merge_BDD BDD h l')  < n’ by gvs[merge_BDD_less_than_const] >>
  ‘BDD_label_length (eliminate_BDD BDD h l')  < n’ by gvs[merge_BDD_less_than_const] >> 

  res_tac >>
  gvs[] 
 
QED



Theorem less_imp_less_in_length_bdd_optminzation:
  ∀ BDD (n:num).
    (BDD_label_length BDD < n ⇒
     BDD_label_length  (bdd_optminzation1 BDD) <  n ∧
     BDD_label_length  (bdd_optminzation2 BDD) <  n)
    
Proof
  gvs[bdd_optminzation1_def, bdd_optminzation2_def] >>
  rpt strip_tac >>
  imp_res_tac less_imp_less_in_length_label >>
  PairCases_on ‘BDD’ >> gvs[]   
QED


    
Theorem operate_opt1_decrease:  
  ∀ BDD l l'.
    operate_opt1 BDD l l' ≠ BDD
    ⇒
    (λ(r,edges,labels). LENGTH labels) (operate_opt1 BDD l l') < BDD_label_length BDD
Proof
  Induct_on ‘l’ >> gvs[] >>
  rpt strip_tac >-
   gvs[operate_opt1_def] >>
  PairCases_on ‘BDD’ >>
  rename1 ‘(r,edges,labels)’ >>
  rw[] >>
  gvs[operate_opt1_def] >>
  res_tac >>
  Cases_on ‘merge_BDD (r,edges,labels) h l' = (r,edges,labels)’ >> gvs[] >>
  imp_res_tac merge_BDD_decrease >>
  imp_res_tac less_imp_less_in_length_label >>
  gvs[BDD_label_length_def]
QED  
      



      
Theorem bdd_optminzation1_decreases:
  ∀BDD. bdd_optminzation1 BDD ≠ BDD ⇒
        BDD_label_length (bdd_optminzation1 BDD) < BDD_label_length BDD
Proof

  rw[bdd_optminzation1_def] >>                       
  PairCases_on ‘BDD’ >>
  rename1 ‘(r,edges,labels)’ >>
  rw[] >>
  gvs[] >>
       
  imp_res_tac operate_opt1_decrease >> 
  rw[operate_opt1_def] >>
  gvs[BDD_label_length_def]
QED

        
Theorem bdd_optminzation1_decreases_verbose:
  ∀r edges labels . bdd_optminzation1 (r,edges,labels) ≠ (r,edges,labels) ⇒
        BDD_label_length (bdd_optminzation1 (r,edges,labels)) < BDD_label_length (r,edges,labels)
Proof
  metis_tac[bdd_optminzation1_decreases]
QED

        



Theorem eliminate_BDD_decrease:        
  ∀ l BDD n .      
    eliminate_BDD BDD l ≠ BDD ⇒
    BDD_label_length (eliminate_BDD BDD l) <  BDD_label_length BDD
Proof

  Induct_on ‘l’ >> cheat >>
  rpt strip_tac >>
  gvs[eliminate_BDD_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> rgs[]) >>
  Cases_on ‘(merge BDD h n) = BDD’ >> gvs[] >>
  first_x_assum (strip_assume_tac o (Q.SPECL [‘(merge BDD h n)’, ‘n’])) >>
  gvs[] >>

  
  ‘BDD_label_length (merge BDD h n) < BDD_label_length BDD’ by gvs[eliminate_decrease] >>
  imp_res_tac BDD_label_length_neq >>
  Cases_on ‘eliminate_BDD (merge BDD h n) n l = merge BDD h n’ >> gvs[] 
QED
   


Theorem operate_opt2_decrease:
  ∀BDD l l'.
    operate_opt2 BDD l l' ≠ BDD ⇒
    (λ(r,edges,labels). LENGTH labels) (operate_opt2 BDD l l') <
    BDD_label_length BDD
Proof
  Induct_on ‘l’ >> gvs[] >> cheat (* >>
  rpt strip_tac >-
   gvs[operate_opt2_def] >>
  PairCases_on ‘BDD’ >>
  rename1 ‘(r,edges,labels)’ >>
  rw[] >>
  gvs[operate_opt2_def] >>
  res_tac >>
  Cases_on ‘eliminate_BDD (r,edges,labels) h l' = (r,edges,labels)’ >> gvs[] >>
  imp_res_tac eliminate_BDD_decrease >>
  imp_res_tac less_imp_less_in_length_label >>
  gvs[BDD_label_length_def] *)
QED


     
Theorem bdd_optminzation2_decreases:
  ∀BDD. bdd_optminzation2 BDD ≠ BDD ⇒
        BDD_label_length (bdd_optminzation2 BDD) < BDD_label_length BDD
Proof
  rw[bdd_optminzation2_def] >>                       
  PairCases_on ‘BDD’ >>
  rename1 ‘(r,edges,labels)’ >>
  rw[] >>
  gvs[] >>
  imp_res_tac operate_opt2_decrease >> 
  rw[operate_opt2_def] >>
  gvs[BDD_label_length_def]
QED        


           
Theorem bdd_optminzationone_shot_decreases_verbose:
  ∀ r edges labels .
    bdd_optminzation2 (r,edges,labels) ≠ (r,edges,labels) ∧
    bdd_optminzation1 (bdd_optminzation2 (r,edges,labels)) ≠  (r,edges,labels) ⇒
    BDD_label_length (bdd_optminzation1 (bdd_optminzation2 (r,edges,labels))) < BDD_label_length (r,edges,labels)
Proof

  rpt strip_tac >>
  assume_tac bdd_optminzation2_decreases >>
  res_tac >>
  imp_res_tac less_imp_less_in_length_bdd_optminzation
QED



        
Definition bdd_one_round_def:
  bdd_one_round BDD = bdd_optminzation1 (bdd_optminzation2 BDD)
End



Theorem bdd_one_round_reduce:
  ∀ BDD.
  bdd_one_round BDD ≠ BDD ⇒
  BDD_label_length (bdd_one_round BDD) < BDD_label_length BDD
Proof
  rpt strip_tac >>
  PairCases_on ‘BDD’ >>
  rename1 ‘(r,edges,labels)’ >>
  gvs[bdd_one_round_def] >>
  Cases_on ‘bdd_optminzation2 (r,edges,labels) = (r,edges,labels)’ >> gvs[] >|[
    assume_tac bdd_optminzation1_decreases >>
    gvs[]
    ,
    
    Cases_on ‘bdd_optminzation1 (bdd_optminzation2 (r,edges,labels)) =
              bdd_optminzation2 (r,edges,labels)’  >> gvs[] >|[
        assume_tac bdd_optminzation2_decreases >>
        res_tac 
        ,
        assume_tac bdd_optminzationone_shot_decreases_verbose >>
        res_tac
      ]
  ]                  
QED
        

Definition bdd_full_optimize_def:
  bdd_full_optimize (BDD:('a,'b) BDD) =
  case bdd_one_round BDD = BDD of
  | T => BDD
  | F => bdd_full_optimize  (bdd_one_round BDD)                                      
Termination
        
  WF_REL_TAC `measure BDD_label_length` >>
  rpt strip_tac >>
      
  rename1 ‘ bdd_one_round (r,edges,labels) = (r,edges,labels)’ >>
  metis_tac[bdd_one_round_reduce]
End






(* definition of mk_BDDPred_opt, where each layer being created the tree will be fully optimized,
not one shot  *)
        
Definition mk_BDDPred_opt_def:
  (mk_BDDPred_opt rec (BDD:('a,'b) BDD) l [] c = SOME BDD) ∧
  (mk_BDDPred_opt rec (BDD) l (x::xs) c =
   case (body_of_mk rec BDD (x:string) (c:num)) of
   | SOME (BDD',c') => mk_BDDPred_opt rec (bdd_full_optimize BDD') (x::l) xs c'
   | NONE => NONE 
  )
End

(******************* new better optimized definitions ***************************)

val _ = type_abbrev("distrub_st", ``:( (string, (num list) option) alist   # num list # num list)``);







Definition eliminable_new_def:
  eliminable_new ((r,edges,labels):('a,'b)BDD) n = 
    case ALOOKUP edges n of
      |SOME (n1, n2) =>
        if n1 = n2 ∧
           n1 ≠ n ∧
           has_parent edges n1 n
        then SOME n1
        else NONE
    | NONE => NONE
End



Definition eliminable_projection_def:
  eliminable_projection edges_proj n = 
    case ALOOKUP edges_proj n of
      |SOME (n1, n2) =>
        if n1 = n2 ∧
           n1 ≠ n ∧
           n ≠ 0n ∧
           has_parent edges_proj n1 n 
        then SOME n1
        else NONE
    | NONE => NONE
End


Definition mergable_projection_def:        
  mergable_projection edges_proj labels_proj n n' = 
  (n≠n' ∧ ALOOKUP edges_proj n = ALOOKUP edges_proj n' ∧
   eq_vars_in_labels labels_proj n n' ∧ ALOOKUP labels_proj n'  ≠ NONE )
End



Definition update_internals_def:
  (update_internals pre [] n x = []) ∧    
  (update_internals pre (h::internals) n x =
   let (var, node_list_op) =  h in
     (if var ≠ x then
        update_internals (pre++[h]) internals n x 
      else
        (
        case node_list_op of
        | SOME l =>  pre++[(var, SOME (n::l))]++internals
        | NONE => pre++[(var, SOME [n])]++internals                            
        )
     )
  )
End

          
Definition distrubute_labels_def:
  (distrubute_labels [] (acc:distrub_st) = acc) ∧
  (distrubute_labels ((n,lbl)::labels) (internals, ntl, tl) =
   case lbl of
   | termn _ => distrubute_labels labels (internals, ntl, n::tl)
   | non_termn (NONE , _) => distrubute_labels labels (internals, n::ntl, tl)
   | non_termn (SOME x , _)  => distrubute_labels labels (update_internals [] internals n x, ntl, tl)
  )
End





           
Definition bdd_distribute_def:
  bdd_distribute (BDD:('a,'b) BDD) order =
  let (r,edges,labels) = BDD in
    let internals_init = MAP (\x. (x,NONE)) order in
      distrubute_labels labels (internals_init, [],[])
End



Definition merge_safe_def:
  merge_safe (BDD:('a,'b) BDD) n n' =
  if mergable BDD n n' then
    (T, merge BDD n n')
   else
    (F, BDD)
End


Definition eliminate_safe_def:
  eliminate_safe (BDD:('a,'b) BDD) n =
  case eliminable_new BDD n  of
  | SOME n' =>  (T, merge BDD n' n)
  | NONE => (F,BDD)
End





Definition optimize_node_def:
  (optimize_node edges_proj labels_proj (BDD:('a,'b) BDD) n [] = SND (eliminate_safe BDD n)) ∧
  
  (optimize_node edges_proj labels_proj BDD n (n'::nl) = 
   case eliminable_projection edges_proj n of
   | SOME n' =>  SND (eliminate_safe BDD n)
   | NONE => (
     case mergable_projection edges_proj labels_proj n' n of
     | T => ( case merge_safe BDD n' n of
              | (T, BDD') => BDD'
              | (F, BDD') => optimize_node edges_proj labels_proj BDD n nl
            )
            
     | F => optimize_node edges_proj labels_proj BDD n nl)
  )
End

        


Definition optimize_layer_def:
  (optimize_layer edges_proj labels_proj (BDD:('a,'b) BDD) [] = BDD) /\
  (optimize_layer edges_proj labels_proj BDD  (n::nl)=
   optimize_layer edges_proj labels_proj (optimize_node edges_proj labels_proj BDD n nl) nl
  )
End


Definition project_edges_to_def:
  project_edges_to ((r, edges,labels):('a,'b) BDD) nl = 
    MAP (\n. (n,THE(ALOOKUP edges n))) nl
End

Definition project_labels_to_def:
  project_labels_to ((r, edges,labels):('a,'b) BDD) nl = 
    MAP (\n. (n,THE(ALOOKUP labels n))) nl
End



Definition optimize_internals_def:
  (optimize_internals (BDD:('a,'b) BDD) [] = BDD) /\
  (optimize_internals BDD  ((var,NONE)::l) = optimize_internals BDD l) /\

  (optimize_internals BDD  ((var,SOME nl)::l)=
    let edges_proj = project_edges_to BDD nl in
     let labels_proj = project_labels_to BDD nl in
      let BDD' = optimize_layer edges_proj labels_proj BDD  nl in
         optimize_internals BDD' l
  )
End



        
Definition optimize_bdd_def:
  optimize_bdd (BDD:('a,'b) BDD) order =
  let (internals,ntl,tl) = bdd_distribute (BDD:('a,'b) BDD) order in
    let labels_proj_tl = project_labels_to BDD tl in (* for terminals *)
      let labels_proj_ntl = project_labels_to BDD ntl in (* for terminals *)
        let BDD1 = optimize_layer [] labels_proj_tl BDD tl in
          let BDD2 = optimize_layer [] labels_proj_ntl BDD1 ntl in
            optimize_internals BDD2 internals
End
                        



Definition mk_BDDPred_opt_new_def:
  (mk_BDDPred_opt_new rec (BDD:('a,'b) BDD) l [] c = SOME (optimize_bdd BDD l)) ∧
  (mk_BDDPred_opt_new rec (BDD) l (x::xs) c =
   case (body_of_mk rec BDD (x:string) (c:num)) of
   | SOME (BDD',c') => mk_BDDPred_opt_new rec (optimize_bdd BDD' (x::l)) (x::l) xs c'
   | NONE => NONE 
  )
End






                                             
val _ = export_theory ();
