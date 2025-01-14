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

     
val _ = new_theory "p4_policy";

   

Type edges = ``:('a, ('a # 'a) ) alist``;
Type labels = ``:('a , 'b ) alist``;

val _ = Hol_datatype ` 
bdd = bdd_ir of ('a # 'a edges # ('a,'b) labels)
`;                                                                 



(* possible types *)
val _ = Hol_datatype ` 
ty =  (* type *)
 | ty_bit of num (* bit-string *)
 | ty_struct of (string#ty) list (* struct *)
`;
        
Type descriptor = ``:(string#ty) list``;

Type field = ``:string``;


     
val _ = Hol_datatype ` 
h =
| h_f of field
| h_acc of (field list)
| h_slice of (field list) => num => num`;



val _ = Hol_datatype ` 
aop = 
 | aop_le (* less or equal *)
 | aop_ge (* greater or equal *)
 | aop_lt (* less *)
 | aop_gt (* greater *)
 | aop_neq (* not equal *)
 | aop_eq (* equal *)
 | aop_and (* bitwise and *)
 | aop_xor (* bitwise xor *)
 | aop_or (* bitwise or *)
`;
   
(*binop as we have in P4 semantics*)
val _ = Hol_datatype ` 
exp =
exp_aop of h => aop => num  `; (*arithmetic expressions*)



(*type of conditions is generic so the proofs are applied to both semantics of rules and also the BDD translation*)        
val _ = Hol_datatype ` 
c =
c_b of bool 
|c_e of 'a  (* for the BDD this is a string, for the rules semantics it is exp ?*)     
|c_and of c => c
|c_or of c => c
|c_neg of c
`;  

Type rule = ``:('a c # string)``;


                                                                   


Definition nodes_set_def:
  nodes_set (edges:'a edges) =        
  set (MAP FST edges) ∪ set (MAP (SND o SND) edges) ∪ set (MAP (FST o SND) edges)
End



Definition mk_distinct_def:
  mk_distinct [] = [] ∧
  mk_distinct (h::l) = if (MEM h l) then
                         mk_distinct l
                       else
                         h::(mk_distinct l)       
End


Theorem mk_distinct_nub_eq:
  ∀ l . mk_distinct l = nub l
Proof
  Induct_on ‘l’ >>
  gvs[mk_distinct_def,nub_def]
QED
        


Theorem mk_distinct_mem:
  ∀ l r. MEM r l = MEM r (mk_distinct l)
Proof
  fs[mk_distinct_nub_eq]
QED

        
        
Definition nodes_list_def:
  nodes_list (edges:'a edges) =        
  let 
    parents = MAP FST edges;
    children_right = MAP (SND o SND) edges ;
    children_left  = MAP (FST o SND) edges
  in
    mk_distinct(parents ++ children_right ++ children_left)
End


Triviality UNION_APPEND_tri:
∀ l1 l2 l3. set l1 ∪ set l2 ∪ set l3 = set (l1 ++ l2 ++ l3 )
Proof
  gvs[Once UNION_APPEND]
QED
        

Theorem nodes_set_list_length_eq:
  ∀ edges . CARD (nodes_set edges) = LENGTH (nodes_list edges)
Proof
  gvs[nodes_list_def, nodes_set_def, mk_distinct_nub_eq] >>
  strip_tac >>
  assume_tac UNION_APPEND_tri  >>             
  first_x_assum $ qspecl_then [‘MAP FST edges : 'a list’,
                               ‘MAP (SND ∘ SND) edges  : 'a list’,
                               ‘MAP (FST ∘ SND) edges : 'a list’] assume_tac >>
  METIS_TAC[CARD_LIST_TO_SET_EQN]
QED

        

Theorem nodes_set_list_mem_eq:
∀ edges node. node ∈ nodes_set edges ⇔ MEM node (nodes_list edges) 
Proof
  fs[nodes_set_def,nodes_list_def, mk_distinct_def, MEM]>>
  gvs[mk_distinct_nub_eq]
QED


Theorem nodes_set_eq1:
 ∀ edges.  nodes_set edges = set (nodes_list edges)     
Proof
  fs[nodes_set_def, nodes_list_def, LIST_TO_SET_DEF] >>
  strip_tac >>
  assume_tac UNION_APPEND_tri  >>             
  first_x_assum $ qspecl_then [‘MAP FST edges : 'a list’,
                               ‘MAP (SND ∘ SND) edges  : 'a list’,
                               ‘MAP (FST ∘ SND) edges : 'a list’] assume_tac >>
  gvs[mk_distinct_nub_eq] 
QED

(*
The set of leaves are basically all nodes - (domain edges)
*)
Definition get_leaves_set_def:
  get_leaves_set (edges:'a edges)  = 
     (nodes_set edges) DIFF set (MAP FST edges)    
End

EVAL “ {(1:num);3} DIFF {(1:num);(2:num)}”;        


Definition get_list_diff_def:
  get_list_diff [] l2 = [] ∧
  get_list_diff (h::l1) l2 =
  if MEM h l2 then
    get_list_diff l1 l2
  else
    h::(get_list_diff l1 l2)    
End

        
Definition get_leaves_list_def:
  get_leaves_list (edges:'a edges)  = 
  let
    all_nodes = nodes_list edges;
    parents = MAP FST edges
  in
    get_list_diff all_nodes parents   
End


Triviality get_leaves_list_mem_imp:
  ∀ l1 l2 l a.  l = get_list_diff l1 l2 ⇒
 (MEM a l ⇔ MEM a l1 ∧ ¬MEM a l2)
Proof
  Induct >> rpt strip_tac >>
  fs[get_list_diff_def, MEM] >>      
  gvs[AllCaseEqs()] >>
  Cases_on ‘a=h’ >> gvs[]    
QED


Triviality get_list_diff_filter_eq:        
 ∀ l1 l2 .  get_list_diff l1 l2 = FILTER (λx. ¬MEM x l2) l1
Proof
  Induct >>
  rpt strip_tac  >>
  gvs[get_list_diff_def] >>
  gvs[AllCaseEqs()]
QED


        
        
Theorem get_leaves_set_list_mem_eq:
 ∀ edges node.  node ∈ (get_leaves_set edges) ⇔ MEM node (get_leaves_list edges)
Proof
  
  simp_tac bool_ss [get_leaves_set_def]>>
  gvs[list_to_set_diff]>>
  gvs[get_leaves_list_def] >>
  gvs[nodes_set_list_mem_eq] >>
  gvs[get_leaves_list_mem_imp]
QED



Definition get_label_set_def:
  get_label_set (labels: ('a,'b) labels) (nodes_set: 'a set) =
  IMAGE (λx. (ALOOKUP labels x)) nodes_set    
End



Definition get_label_list_def:
  get_label_list (labels: ('a,'b) labels) (nodes_list: 'a list) =
  MAP (λx. (ALOOKUP labels x)) nodes_list   
End



Triviality get_label_set_list_eq1:
 ∀ labels edges . get_label_set labels (nodes_set edges) = set (get_label_list labels (nodes_list edges))
Proof
  gvs[get_label_set_def, get_label_list_def]>>
  gvs[LIST_TO_SET_MAP] >>
  rpt strip_tac >>
  gvs[nodes_set_eq1]
QED



(*****************************************)


     
Definition mk_substitute_rule_def:
  (mk_substitute_rule (c_b b') (x:'a) b = c_b b') ∧
  (mk_substitute_rule (c_e (x':'a)) x b = if (x=x') then c_b b else c_e x') ∧
  (mk_substitute_rule (c_and c c' ) x b =
      (c_and (mk_substitute_rule c x b) (mk_substitute_rule c' x b ))) ∧
  (mk_substitute_rule (c_or c c') x b =
      (c_or (mk_substitute_rule c x b) (mk_substitute_rule c' x b ))) ∧
  (mk_substitute_rule (c_neg c) x b=
      (c_neg (mk_substitute_rule c x b)))
End


EVAL “mk_substitute_rule (c_and (c_e "x") (c_e "y")) "x" T”;        
EVAL “mk_substitute_rule (c_and (c_or (c_e "x") (c_e "y")) (c_e "y")) "y" T”;        

                     
Definition mk_substitute_policy_list_def:
  mk_substitute_policy_list (rules_list: 'a rule list) x b =
       MAP (λ (c,a) . (mk_substitute_rule x b, a)) rules_list
End

        

       
Definition mk_substitute_policy_set_def:
   mk_substitute_policy_set (rules_set: 'a rule set ) x b =
       IMAGE (λ (c,a) . (mk_substitute_rule x b, a)) rules_set
End


Triviality mk_substitute_policy_set_eq:
 ∀ (rule_list: 'a rule list) x b .  mk_substitute_policy_set (set rule_list) x b = set (mk_substitute_policy_list rule_list x b)
Proof
  gvs[mk_substitute_policy_set_def, mk_substitute_policy_list_def]>>
  gvs[LIST_TO_SET_MAP] 
QED



(*************************************)
Definition edges_acyclic_def:
  edges_acyclic (edges:('a#'a#'a) set) =
  let nr = IMAGE (λ(n,n',n''). (n,n'')) edges;
      nl = IMAGE (λ(n,n',n''). (n,n')) edges
  in
     acyclic(nr ∪ nl)
End
(************************************)


val _ = export_theory ();
