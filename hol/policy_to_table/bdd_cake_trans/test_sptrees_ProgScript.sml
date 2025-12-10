open HolKernel Parse boolLib bossLib;
open optionTheory pairTheory bdd_genTheory policy_specTheory pred_specTheory;
open sptreeTheory;


val _ = type_abbrev("sp_edges", ``:(num#num) spt``);
                                                                     
Type sp_labelings = ``:(('a,'b) label) spt``;
val _ = type_abbrev("sp_BDD", ``:num # sp_edges # ('a,'b) sp_labelings``);


    

Definition sp_getLabels_def:
  (sp_getLabels (labels:('a,'b) sp_labelings) [] = SOME [] ) ∧
  (sp_getLabels labels (n::leaves) =
   case (sp_getLabels labels leaves) of
   | SOME l =>
       (
       case (lookup n labels) of
       | NONE => NONE
       | SOME lbl => SOME ((n,lbl)::l)
       )
   | NONE => NONE
  )
End

  

Definition sp_determine_termn_list_def:
  sp_determine_termn_list rec x leaves_nontermn =
   MAP (\(n,p). (n, x, p, (determine_termn rec (rec.simp (rec.sub p x T))) , (determine_termn rec (rec.simp (rec.sub p x F))) )) leaves_nontermn
End


Definition sp_mk_new_labels_def:
  sp_mk_new_labels (labels:('a,'b) sp_labelings)  [] (c:num) =  labels ∧
  (sp_mk_new_labels labels ((n, x', p, (lbl,lbl'))::rest) c =
  let labels_current = insert (c+1) lbl' (insert c lbl (insert n (non_termn (SOME x', p)) labels)) in
    sp_mk_new_labels labels_current rest (c+2)
  )
End


Definition sp_mk_new_edges_def:
  sp_mk_new_edges (edges:sp_edges)  [] (c:num) =  edges ∧
  (sp_mk_new_edges edges ((n, x', p, (lbl,lbl'))::rest) c =
  let edges_current = insert n (c,c+1) edges in
    sp_mk_new_edges edges_current rest (c+2)
  )
End

        
(*
1. merge  extract_nontermn and sp_getLabels
      *)


Definition sp_body_of_mk_def:
  sp_body_of_mk rec (sp_BDD:('a,'b) sp_BDD) (x:string) (c:num) =
  (let (r,edges,labels) = sp_BDD in
     (case getLeaves (toAList edges)  r of
      | SOME leaves =>
          (case (sp_getLabels labels leaves) of
           | SOME leaves_labels =>
               ( case (extract_nontermn leaves_labels) of
                 | SOME leaves_nontermn =>
                     (
                     
                     let simp_leaves' = sp_determine_termn_list rec x leaves_nontermn in
                       let new_labels = sp_mk_new_labels labels simp_leaves' c in
                         let new_edges = sp_mk_new_edges edges simp_leaves' c in
                           
                           
                           SOME (((r, new_edges, new_labels):( ('a,'b) sp_BDD)),
                                 c + ((LENGTH leaves_nontermn)*2) 
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



Definition sp_mk_BDDPred_def:
  (sp_mk_BDDPred rec (sp_BDD:('a,'b) sp_BDD) l [] c = SOME sp_BDD) ∧
  (sp_mk_BDDPred rec (sp_BDD) l (x::xs) c =
   case (sp_body_of_mk rec sp_BDD (x:string) (c:num)) of
   | SOME (sp_BDD',c') => sp_mk_BDDPred rec sp_BDD' (x::l) xs c'
   | NONE => NONE 
  )
End

        

(*

        (0n,LN,insert 0 (non_termn (NONE, (Var "a"))) LN)
EVAL “sp_mk_BDDPred pred_structure (0n,LN,insert 0 (non_termn (NONE, And (Var "a") (Var "b"))) LN) [] ["a";"b"] 1”;
EVAL “sp_mk_BDDPred pred_structure (0n,LN,insert 0 (non_termn (NONE, Or (And (Var "a") (Var "b")) (Var "c"))) LN) [] ["a";"b"] 1”;


     
EVAL “sp_mk_BDDPred pred_structure (0,[],[(0, non_termn (NONE, Or (And (Var "a") (Var "b")) (Var "c")  ))]) [] ["a";"b";"c"] 1”;
EVAL “sp_mk_BDDPred pred_structure (0,[],[(0, non_termn (NONE, Or (Var "a") (Var "b")))]) [] ["a";"b";"c"] 1”;
EVAL “sp_mk_BDDPred pred_structure (0,[],[(0, non_termn (NONE, Or (Var "a") (Var "b")))]) [] ["a";"b";"c"] 1”;
*)








Definition sp_eq_vars_in_labels_def:
  sp_eq_vars_in_labels sp_labels n n' =
    case (lookup n sp_labels , lookup n' sp_labels) of
    | (SOME (termn (a,_)), SOME (termn (a',_))) => (a = a')
    | (SOME (non_termn (SOME x,_)), SOME (non_termn (SOME x',_))) => (x = x')
    | (SOME (non_termn (NONE, p)), SOME (non_termn (NONE,p'))) => (p=p')
    | others => F
End 
           
    
Definition sp_mergable_def:        
  sp_mergable ((r,sp_edges,sp_labels):('a,'b) sp_BDD)  n n' = 
  (n≠n' ∧ lookup n sp_edges = lookup n' sp_edges ∧
   sp_eq_vars_in_labels sp_labels n n' ∧ lookup n' sp_labels ≠ NONE )
End




Definition sp_merge_edges_def:
  sp_merge_edges (sp_edges:sp_edges) n n' =
   mapi (\a (b,c).  (if (b=n' ∧ c=n') then (n,n)
                       else if (b=n') then (n,c)
                       else if (c=n') then (b,n)
                       else (b,c))) sp_edges 
End


Definition sp_merge_def:
  sp_merge ((r,sp_edges,sp_labels):('a,'b) sp_BDD) n n' =
  let sp_edges' = sp_merge_edges sp_edges n n' in
    let sp_edges'' = delete n' sp_edges' in
      let sp_labels' = delete n' sp_labels in
          (r,sp_edges'',sp_labels')
End



        
Definition sp_eliminable_def:
  sp_eliminable ((r,sp_edges,sp_labels):('a,'b) sp_BDD) n = 
    case lookup n sp_edges of
      |SOME (n1, n2) =>
        if n1 = n2 ∧
           n1 ≠ n ∧
           n ≠ 0n
        then SOME n1
        else NONE
    | NONE => NONE
End



val _ = type_abbrev("distrub_st", ``:( (string, (num list) option) alist   # num list # num list)``);


Definition sp_bdd_distribute_def:
  sp_bdd_distribute (sp_BDD:('a,'b) sp_BDD) order =
  let (r,sp_edges,sp_labels) = sp_BDD in
    let internals_init = MAP (\x. (x,NONE)) order in
      distrubute_labels (toAList sp_labels) (internals_init, [],[])
End


Definition sp_merge_safe_def:
  sp_merge_safe (sp_BDD:('a,'b) sp_BDD) n n' =
  if sp_mergable sp_BDD n n' then
    (T, sp_merge sp_BDD n n')
   else
    (F, sp_BDD)
End



Definition sp_eliminate_safe_def:
  sp_eliminate_safe (sp_BDD:('a,'b) sp_BDD) n =
  case sp_eliminable sp_BDD n  of
  | SOME n' =>  (T, sp_merge sp_BDD n' n)
  | NONE => (F,sp_BDD)
End


        

Definition sp_optimize_node_leaf_def:
  (sp_optimize_node_leaf (sp_BDD:('a,'b) sp_BDD) n [] = sp_BDD) ∧
  
  (sp_optimize_node_leaf sp_BDD n (n'::nl) =
   ( case sp_merge_safe sp_BDD n' n of
     | (T, BDD') => BDD'
     | (F, BDD') => sp_optimize_node_leaf sp_BDD n nl
   )
  )
End

        
Definition sp_optimize_layer_leaf_def:
  (sp_optimize_layer_leaf (sp_BDD:('a,'b) sp_BDD) [] = sp_BDD) /\
  (sp_optimize_layer_leaf  sp_BDD  (n::nl)=
   sp_optimize_layer_leaf (sp_optimize_node_leaf sp_BDD n nl) nl
  )
End

        
Definition sp_optimize_node_def:
  (sp_optimize_node  (sp_BDD:('a,'b) sp_BDD) n [] = SND (sp_eliminate_safe sp_BDD n)) ∧
  
  (sp_optimize_node sp_BDD n (n'::nl) = 
       ( case sp_merge_safe sp_BDD n' n of
              | (T, BDD') => BDD'
              | (F, BDD') => sp_optimize_node sp_BDD n nl
       )
  )
End




Definition sp_optimize_layer_def:
  (sp_optimize_layer (sp_BDD:('a,'b) sp_BDD) [] = sp_BDD) /\
  (sp_optimize_layer  sp_BDD  (n::nl)=
   case (sp_eliminate_safe sp_BDD n) of
   | (T, BDD') => sp_optimize_layer  BDD'  nl
   | (F, BDD') => sp_optimize_layer  (sp_optimize_node BDD' n nl) nl
  )
End




Definition sp_optimize_internals_def:
  (sp_optimize_internals (sp_BDD:('a,'b) sp_BDD) [] = sp_BDD) /\
  (sp_optimize_internals sp_BDD ((var,NONE)::l) = sp_optimize_internals sp_BDD l) /\

  (sp_optimize_internals sp_BDD  ((var,SOME nl)::l)=
      let BDD' = sp_optimize_layer sp_BDD nl in
         sp_optimize_internals BDD' l
  )
End



Definition sp_optimize_bdd_def:
  sp_optimize_bdd (sp_BDD:('a,'b) sp_BDD) order =
  let (internals,ntl,tl) = sp_bdd_distribute (sp_BDD) order in
        let BDD1 = sp_optimize_layer_leaf sp_BDD tl in
          let BDD2 = sp_optimize_layer_leaf BDD1 ntl in
            sp_optimize_internals BDD2 internals
End
         
                        



Definition sp_mk_BDDPred_opt_def:
  (sp_mk_BDDPred_opt rec (BDD:('a,'b) sp_BDD) l [] c= SOME (sp_optimize_bdd BDD l)) ∧
  (sp_mk_BDDPred_opt rec (BDD) l (x::xs) c=
   case (sp_body_of_mk rec BDD (x:string) (c:num) ) of
   | SOME (BDD',c') => sp_mk_BDDPred_opt rec (sp_optimize_bdd BDD' (x::l)) (x::l) xs c'
   | NONE => NONE 
  )
End


Definition simp_policy2_def:
  (simp_policy2 [] = []) ∧
  (simp_policy2 ((p,a)::policy) = 
   (let p' = simp_pred p in
      ( case p' of
        | True => [(p',a)]
        | False => (simp_policy2 policy)
        | _ => (p',a)::(simp_policy2 policy)
      )
   )
  )
End


Definition final_policy2_def:
  (final_policy2 ([(True, a)]: 'a policy) = SOME a) ∧
  (final_policy2 (_) = NONE)
End




Definition policy_structure2_def:
  policy_structure2 =
  <|
    sem := sem_policy;
    sub := mk_substitute_policy;
    simp := simp_policy2;
    final := final_policy2;
    fv := fv_policy;
  |>
End


        
val arith_policy_eval = EVAL “convert_arith_to_var_policy ^arith_policy ^policy_me”;
val var_policy = optionSyntax.dest_some (rhs (concl arith_policy_eval));


val eval_policy_full_opt = EVAL “sp_mk_BDDPred_opt policy_structure (0n,LN,insert 0 (non_termn (NONE, ^var_policy)) LN) [] ^policy_order 1”;



(*
val pred = “Or (And (Var "x1") (Var "x2")) (And (Var "x3") (Var "x4"))”;
 EVAL “sp_mk_BDDPred_opt pred_structure (0n,LN,insert 0 (non_termn (NONE, ^pred)) LN) [] ["x1";"x3";"x2";"x4"] 1”;
*)

        
val policy_order =   “[
    ("is_srcPort_le_57222");
    ("is_srcPort_ge_57222");
    ("is_dstPort_le_53");
    ("is_dstPort_ge_53");
    ("is_srcNAT_le_54587");
    ("is_srcNAT_ge_54587");
    ("is_dstNAT_le_53");
    ("is_dstNAT_ge_53");
    ("is_srcPort_le_56258");
    ("is_srcPort_ge_56258");
    ("is_dstPort_le_3389");
    ("is_dstPort_ge_3389");
    ("is_srcNAT_le_56258");
    ("is_srcNAT_ge_56258");
    ("is_dstNAT_le_3389");
    ("is_dstNAT_ge_3389");
    ("is_srcPort_le_6881");
    ("is_srcPort_ge_6881");
    ("is_dstPort_le_50321");
    ("is_dstPort_ge_50321");
    ("is_srcNAT_le_43265");
    ("is_srcNAT_ge_43265");
    ("is_dstNAT_le_50321");
    ("is_dstNAT_ge_50321");
    ("is_srcPort_le_50553");
    ("is_srcPort_ge_50553");
    ("is_srcNAT_le_50553");
    ("is_srcNAT_ge_50553");
    ("is_srcPort_le_50002");
    ("is_srcPort_ge_50002");
    ("is_dstPort_le_443");
    ("is_dstPort_ge_443");
    ("is_srcNAT_le_45848");
    ("is_srcNAT_ge_45848");
    ("is_dstNAT_le_443");
    ("is_dstNAT_ge_443");
    ("is_srcPort_le_51465");
    ("is_srcPort_ge_51465");
    ("is_srcNAT_le_39975");
    ("is_srcNAT_ge_39975");
]”;













(*

val var_pred = “ Or (And (Var "x") (Not (Var "y"))) (And (Not (Var "b")) (Var "e")) ”
EVAL “sp_mk_BDDPred_opt pred_structure (0n,LN,insert 0 (non_termn (NONE, ^var_pred)) LN) [] ["b";"e";"x"; "y"] 1”;
EVAL “sp_mk_BDDPred_opt pred_structure (0n,LN,insert 0 (non_termn (NONE, ^var_pred)) LN) [] ["x";"y";"b"; "e"] 1”;



val var_pred = “ Or (And (Var "x") (Not (Var "y"))) (And (Not (Var "a")) (Var "b")) ”
val var_pred2 = “ Or (And (Var "c") (Not (Var "d"))) (And (Not (Var "e")) (Var "f")) ”
val var_pred3 = “ Or ^var_pred ^var_pred2 ”


     
EVAL “sp_mk_BDDPred_opt pred_structure (0n,LN,insert 0 (non_termn (NONE, ^var_pred)) LN) [] ["a";"b";"c"; "d"; "f"; "g"; "x"; "y"] 1”;

EVAL “sp_mk_BDDPred_opt pred_structure (0n,LN,insert 0 (non_termn (NONE, ^var_pred)) LN) [] ["a";"b";"c"; "d"; "x"; "y"; "f"; "e"] 1”;

val _ = type_abbrev("action_rule_type", “:((string# num list) action_expr) rule”);
val _ = type_abbrev("action_policy_type", “:((string# num list) action_expr) policy”);

val rule1 = “(^var_pred3 , action ("allow",[1]: num list)):action_rule_type”;
val rule2 = “((Var "k") , action ("allow",[2]: num list)):action_rule_type”;
val rule3 = “((Var "o") , action ("allow",[3]: num list)):action_rule_type”;

val arith_policy_rule_default = “(True, action ("drop", []: num list)):action_rule_type”;


val arith_policy = “[
    ^rule1;
    ^rule2;
    ^arith_policy_rule_default
]: action_policy_type”;
     
    
o -> k -> a -> b -> c -> d -> x -> y -> f -> e

  
EVAL “sp_mk_BDDPred_opt policy_structure (0n,LN,insert 0 (non_termn (NONE, ^arith_policy)) LN) []
     ["o"; "k";"a";"b";"c"; "d"; "x"; "y"; "f"; "e"]
      1”;    



EVAL “sp_mk_BDDPred_opt policy_structure (0n,LN,insert 0 (non_termn (NONE, ^arith_policy)) LN) []
     ["x"; "y";"a";"b";"c"; "d"; "e"; "f"; "k"; "o"]
      1”;    



      
*)



val _ = export_theory ();
