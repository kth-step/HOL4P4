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


Definition eliminable_def:        
eliminable ((r,edges,labels):('a,'b)BDD)  n n' = 
(n≠n' ∧
 ALOOKUP edges n' = SOME (n,n) ∧
 ALOOKUP labels n  ≠ NONE ∧
 ALOOKUP labels n' ≠ NONE ∧
 has_parent edges n n' )
End 
                                             
val _ = export_theory ();
