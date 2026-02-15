open HolKernel Parse bossLib;

val _ = new_theory "bdd_gen";


(******************************************************)
(*   generalized types for a structure and BDD graph  *)
(******************************************************)


(* language ILR specialization definitions: 
   semantics, substitute, simplify, final, free variable check
 *)
Datatype ‘decision_structure = <| sem : 'a -> ((string,bool) alist) -> 'b option ;
                                      sub : 'a -> string -> bool -> 'a ;
                                      simp : 'a -> 'a ;
                                      final : 'a -> 'b option;
                                      fv : 'a -> string list
                                    |>’;

(* edges map *)
Type edges = “:(num , (num # num)) alist”;

(* label *)
Datatype:
   label = termn ('b # 'a )
          | non_termn (string option #  'a)
End

(* labels map *)
Type labelings = “:(num , ('a,'b) label) alist”;


(* BDD tuples *)
Type BDD = “:(num # edges # ('a,'b) labelings)”;





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



(* create one layer / one iteration in mk bdd optimized *)
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
Definition toBDD_pred_def:
  toBDD_pred P vars = mk_BDDPred (0, [], [(0, non_termn ( NONE , P))]) vars 1
End
*)




(**********************************************)
(* generalised definitions for BDD WFness     *)
(**********************************************)


Definition lookup_is_some_def:
  lookup_is_some l1 n =
     ? y . ALOOKUP l1 n = SOME y
End

Definition is_lookup_internal_def:
  is_lookup_internal l1 n =
     ? x p . ALOOKUP l1 n = SOME (non_termn (SOME x, p))
End

Definition is_lookup_ntl_def:
  is_lookup_ntl l1 n =
     ? p . ALOOKUP l1 n = SOME (non_termn (NONE, p))
End



Definition dom_range_edges_def:
  dom_range_edges edges =
   nub (FLAT (MAP (λ(k,v1,v2). [k; v1; v2]) edges))
End



Definition dom_labels_def:
  dom_labels labels =
  MAP FST labels
End



(* decided to make it domain of edges instead of labels cause
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

(* prop1: Simplification after substitution preserves semantics *)
Definition prop1_def:
  prop1 (rec:('a,'b)decision_structure) =
  ∀ mv h b p.
    ALOOKUP mv h = SOME b ∧ fv_in_p rec p mv ⇒
    (rec.sem (rec.simp (rec.sub p h b)) mv = rec.sem p mv)
End


(* prop2: Final implies semantic value (completeness of final) *)
Definition prop2_def:
  prop2 rec =
  ∀ mv h b p q.
    ALOOKUP mv h = SOME b ∧
    fv_in_p rec p mv ⇒
    rec.final (rec.simp (rec.sub p h b)) = SOME q ⇒
    (SOME q = rec.sem p mv )
End


(*prop3: Final implies simplification terminates *)
Definition prop3_def:
  prop3 rec =
  ∀ mv h b p q.
    rec.final (rec.simp (rec.sub p h b)) = SOME q ⇒
    rec.sem (rec.simp (rec.sub p h b)) mv = SOME q
End


(* prop4: Free variables are preserved under simplification *)
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
  eliminable ((r,edges,labels):('a,'b)BDD) n =
    case ALOOKUP edges n of
      |SOME (n1, n2) =>
        if n1 = n2 ∧
           n1 ≠ n ∧
           has_parent edges n1 n
        then SOME n1
        else NONE
    | NONE => NONE
End




Type distrub_st = “:( (string, (num list) option) alist   # num list # num list)”


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
  case eliminable BDD n  of
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
  (optimize_layer edges_proj labels_proj (BDD:('a,'b) BDD) [] = BDD) ∧
  (optimize_layer edges_proj labels_proj BDD  (n::nl)=
   optimize_layer edges_proj labels_proj (optimize_node edges_proj labels_proj BDD n nl) nl
  )
End


Definition project_edges_to_def:
  project_edges_to ((r, edges, labels):('a,'b) BDD) nl =
    FOLDL
      (\acc n.
        case ALOOKUP edges n of
        | NONE => acc
        | SOME e => (n, e)::acc)
      [] nl
End

Definition project_labels_to_def:
  project_labels_to ((r, edges,labels):('a,'b) BDD) nl =
    FOLDL
      (\acc n.
        case ALOOKUP labels n of
        | NONE => acc
        | SOME e => (n, e)::acc)
      [] nl
End



Definition optimize_internals_def:
  (optimize_internals (BDD:('a,'b) BDD) [] = BDD) ∧
  (optimize_internals BDD  ((var,NONE)::l) = optimize_internals BDD l) ∧

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
    let labels_proj_tl = project_labels_to BDD tl in (* projection for terminals *)
      let labels_proj_ntl = project_labels_to BDD ntl in (* projection for non-terminals *)
        let BDD1 = optimize_layer [] labels_proj_tl BDD tl in
          let BDD2 = optimize_layer [] labels_proj_ntl BDD1 ntl in
            optimize_internals BDD2 internals
End




(* Core MTBDD construction algorithm:
   
   body_of_mk: Single iteration for variable x
   - Finds all leaves (nodes without outgoing edges)
   - Extracts non-terminal leaves (ones still containing x)
   - Applies Shannon expansion: substitute T/F for x
   - Simplifies resulting predicates
   - Creates new nodes for simplified predicates
   - Updates labels (marking which variable was eliminated)
   
   mk_BDDPred: Recursively optmizes all variables in order

 *)


Definition mk_BDDPred_opt_def:
  (mk_BDDPred_opt rec (BDD:('a,'b) BDD) l [] c = SOME (optimize_bdd BDD l)) ∧
  (mk_BDDPred_opt rec (BDD) l (x::xs) c =
   case (body_of_mk rec BDD (x:string) (c:num)) of
   | SOME (BDD',c') => mk_BDDPred_opt rec (optimize_bdd BDD' (x::l)) (x::l) xs c'
   | NONE => NONE
  )
End







val _ = export_theory ();
