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

   
(*)
Type edges = ``:('a, ('a # 'a) ) alist``;
Type labels = ``:('a , 'b ) alist``;

val _ = Hol_datatype ` 
bdd = bdd_ir of ('a # 'a edges # ('a,'b) labels)
`;                                                                 
*)



 (* Predicate datatype *)
val _ = Hol_datatype `
  pred = Var of string
       | True
       | False
       | And of pred => pred
       | Or of pred => pred
       | Not of pred
       | Implies of pred => pred`;

                                      
                                        
(* BDD types *)
val _ = type_abbrev("edges", ``:(num , (num # num)) alist``);


                        
    
val _ = Hol_datatype `
  label = termn of pred
        | non_termn of ( string option #  pred)`;

               
val _ = type_abbrev("labelings", ``:(num , label) alist``);
val _ = type_abbrev("BDD", ``:num # edges # labelings``);






val get_leaves_list_def = Define `
  get_leaves_list (edges : edges) =
    nub (FILTER (\x. ~(MEM x (MAP FST edges))) 
           (FLAT (MAP (\(k, (v1, v2)). [v1; v2]) edges)))
`;


        

    
(* Helper functions *)
val getLeaves_def = Define `
   getLeaves [] r = [r] ∧
   getLeaves edges r = get_leaves_list (edges)
`;




Definition edges_acyclic_def:
  edges_acyclic (edges:edges) =
  let nl = MAP (\(n,n',n''). (n,n')) edges;
      nr = MAP (\(n,n',n''). (n,n'')) edges
  in
     acyclic(LIST_TO_SET(nl) ∪ LIST_TO_SET(nr) )
End




val is_lookup_defined_def = Define `
    is_lookup_defined l1 n =
     ? y . ALOOKUP l1 n = SOME y 
`;
        
val is_lookup_non_leaf_def = Define `
    is_lookup_non_leaf l1 n =
     ? x p . ALOOKUP l1 n = SOME (non_termn (SOME x, p))
`;

val is_lookup_leaf_def = Define `
    is_lookup_leaf l1 n =
     ? p . ALOOKUP l1 n = SOME (non_termn (NONE, p))
`;
        





        
Definition BDD_WF_def:
  BDD_WF ((r,edges,labels):BDD) =
  (ALL_DISTINCT (MAP FST edges)  ∧ ALL_DISTINCT (MAP FST labels)  ∧
    (∀ n . is_lookup_defined edges n ⇔ is_lookup_non_leaf labels n ) ∧
    (∀ n . ALOOKUP edges n = NONE  ⇔   (is_lookup_leaf labels n
                                        ∨ ALOOKUP labels n= SOME (termn True)
                                        ∨ ALOOKUP labels n= SOME (termn False))
    ))
End




Type ord = ``:(string -> string -> bool )``
        

Definition WF_o_def:
(WF_o order) =    (( !(x:ord).   (order x x) ) /\
  		 ( !x y.   order x y  ==> ~order y x ) /\
                 ( !x y z. order x y /\ order y z  ==> order x z ))
End

        
Definition ordered_el_def:
ordered_el (order:ord) el1 el2  =
   order el1 el2
End

        
Definition ordered_list_def:
ordered_list (order:ord) l  =
    ! i . i < LENGTH l - 2  ==> order (EL i l) (EL (SUC i) l)
End



Definition find_index_x_def:        
find_index_x xl x =
INDEX_OF
End
        

Definition BDD_ordered_def:
BDD_ordered ((r,edges,labels):BDD) xl =
∀ n n' n'' x x' x'' p p' p'' i i' i''.
  ALOOKUP edges n = SOME (n',n'') ⇒
  ((ALOOKUP labels n   =  SOME (non_termn(SOME x,   p   )) ∧
    ALOOKUP labels n'  =  SOME (non_termn(SOME x',  p'  )) ∧
    INDEX_OF x xl  = SOME i ∧
    INDEX_OF x' xl = SOME i' 
    ⇒ 
    i' < i 
   )
   ∧
   (ALOOKUP labels n   =  SOME (non_termn(SOME x,   p   )) ∧
    ALOOKUP labels n'' =  SOME (non_termn(SOME x'', p'' )) ∧
    INDEX_OF  x   xl = SOME i ∧
    INDEX_OF  x'' xl = SOME i''
    ⇒ 
    i'' < i
   )
  )
End
        

        
    

                                        
(* Predicate semantics *)
val Sem_rule_def = Define `
  (Sem_rule (Var x) m_v = (ALOOKUP m_v x) ) /\
  (Sem_rule True _ = SOME T) /\
  (Sem_rule False _ = SOME F) /\
  (Sem_rule (And p q) m_v = 
    case (Sem_rule p m_v, Sem_rule q m_v)  of
    | (SOME b, SOME b') => SOME (b ∧ b')
    | (_,_) => NONE
    ) /\
  (Sem_rule (Or p q) m_v = 
    case (Sem_rule p m_v, Sem_rule q m_v)  of
    | (SOME b,SOME b') => SOME (b ∨ b')
    | (_,_) => NONE
    ) /\
    (Sem_rule (Not p) m_v = 
    case (Sem_rule p m_v)  of
    | SOME b => SOME (~b)
    | _ => NONE
    ) /\
    (Sem_rule (Implies p q) m_v = 
    case (Sem_rule p m_v, Sem_rule q m_v)  of
    | (SOME b,SOME b') => SOME (b ⇒ b')
    | (_,_) => NONE
    ) `;




                                        
(* Predicate semantics *)
Definition apply_Sem_rule_def:
(apply_Sem_rule (NONE) m_v = NONE ) /\
(apply_Sem_rule (SOME p) m_v = Sem_rule p m_v ) 
End



        
(*                                                                        
EVAL “Sem_rule (Or (Var "a") (Var "b")) [("a",T);("b",F)]”
EVAL “Sem_rule (And (Var "b") (Var "b")) [("a",F);("b",F)]”
EVAL “Sem_rule (Or (Var "b") ((Implies (Var "a") (Var "b")))) [("a",F);("b",F)]”
EVAL “Sem_rule (Or (Var "a") False) []”

*)


                                                                        
   

(* P[x -> T] *)     
Definition mk_substitute_pred_def:
  (mk_substitute_pred (True) (Var x) b = True) ∧
  (mk_substitute_pred (False) (Var x) b = False) ∧
  (mk_substitute_pred (Var (x')) (Var x) b = if (x=x') then b else (Var x') ) ∧
  (mk_substitute_pred (And c c' ) (Var x) b =
      (And (mk_substitute_pred c (Var x) b) (mk_substitute_pred c' (Var x) b ))) ∧
  (mk_substitute_pred (Or c c') (Var x) b =
      (Or (mk_substitute_pred c (Var x) b) (mk_substitute_pred c' (Var x) b ))) ∧
  (mk_substitute_pred (Not c) (Var x) b=
      (Not (mk_substitute_pred c (Var x) b)))
End


(*        
EVAL “mk_substitute_pred (Or (Var "a") (Var "b")) "b" True”
EVAL “mk_substitute_pred (Or (Var "b") (Var "b")) "b" True”
EVAL “mk_substitute_pred (Or (Var "b") ((Or (Var "a") (Var "b")))) "b" True”
*)



Definition is_termn_def:
  is_termn (l:label) =
  case l of
  | termn _ => T
  | non_termn _ => F
End


Definition extract_nontermn_def:
  extract_nontermn [] = SOME [] ∧
  extract_nontermn ((n,l)::leaves_labels) =
  case (extract_nontermn leaves_labels) of
  | SOME l' => (
    case (l) of
    | termn p  => SOME l'
    | non_termn (NONE , p) => SOME ((n ,p)::l')
    | non_termn (SOME x,p) => NONE
    ) 
  | NONE => NONE
End

(*        
EVAL “extract_nontermn [(1,termn True); (2, termn False); (3,  non_termn (SOME "a",(And (Var "a") (Var "b"))) )] ”;
EVAL “extract_nontermn [(1,termn True); (2, termn False); (3,  non_termn (NONE,(And (Var "a") (Var "b"))) )] ”;
*)




     
        
Definition extract_termn_def:
  extract_termn [] = SOME [] ∧
  extract_termn ((n,l)::leaves_labels) =
  case (extract_termn leaves_labels) of
  | SOME l' => (
    case (l) of
    | termn True  => SOME ((n , termn True)::l')
    | termn False  => SOME ((n ,termn False)::l')
    | termn _  => NONE
    | non_termn _ => SOME l'
    ) 
  | NONE => NONE
End


(*        
EVAL “extract_termn [(1,termn True); (2, termn False); (3,  non_termn (SOME "a",(And (Var "a") (Var "b"))) );
                     (2, termn False)] ”;
EVAL “extract_termn [(1,termn True); (2, termn False); (3,  termn (And True True))] ”;
*)
       

Definition getLabels_def:
  (getLabels labels [] = SOME [] ) ∧
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
       
        
Definition leaves_pred_sub_def:
  leaves_pred_sub (nodes_labels:(num#pred)list) x =
  MAP
  (\(n,p).(n,x,mk_substitute_pred p (Var x) True,mk_substitute_pred p (Var x) False)) nodes_labels 
End

        

Definition mk_new_labels_def:
  mk_new_labels [] (c:num) =  [] ∧
  mk_new_labels ((n,x',(label,label'))::rest) c =  (c, label)::(c+1, label')::(mk_new_labels rest (c+2)) 
End

        

Definition mk_new_edges_def:
  mk_new_edges []                c =  [] ∧
  mk_new_edges ((n:num,x',(p,p'))::rest) (c:num) =  (n, c, c+1)::(mk_new_edges rest (c+2))     
End




        
Definition simp_pred_def:
  (simp_pred (Var x) = Var x) /\
  (simp_pred True = True) /\
  (simp_pred False = False) /\
  (simp_pred (And p q) =
    let p' = simp_pred p in
    let q' = simp_pred q in
      case (p', q') of
      |  (True, True) => True
      | (False,  _) => False
      | (_, False) => False
      | (True, q') => q'
      | (p', True) => p'
      | _ => And p' q') /\
  (simp_pred (Or p q) =
    let p' = simp_pred p in
    let q' = simp_pred q in
      case (p', q') of
      |  (False, False) => False
      | (False, q') => q'
      | (p', False) => p'
      | (True, _) => True
      | (_, True) => True
      | _ => Or p' q') /\
  (simp_pred (Not p) =
    let p' = simp_pred p in
      case p' of
      |  True => False
      | False => True
      | _ => Not p') /\
  (simp_pred (Implies p q) =
    let p' = simp_pred p in
    let q' = simp_pred q in
      case (p', q') of
      |  (True, False) => False
      | (False, _) => True
      | (True, q') => q'
      | _ => Implies p' q')
End


Definition simp_pred_list_def:
  simp_pred_list leaves_sub =
  MAP (\(n,x,p,p'). (n,x,simp_pred p , simp_pred p')) leaves_sub
End


        
   
Definition determine_termn_def:
  determine_termn (p:pred) =
  case p of
  | True => termn True
  | False => termn False
  | _ => non_termn (NONE,p) 
End

Definition determine_termn_list_def:
  determine_termn_list nodes_simp =
   MAP (\(n,x,p,p'). (n, x, determine_termn p , determine_termn p' )) nodes_simp
End
        
          




        

Definition mk_distict_labels_def:
  (mk_distict_labels [] l'= []) ∧
  (mk_distict_labels ((p,n)::l) l' =
   case (ALOOKUP l' p) of
   | SOME n' => mk_distict_labels l l'
   | NONE => (p,n)::(mk_distict_labels l ((p,n)::l') )
  )          
End


(*
EVAL “mk_distict_labels [("a",1);("b",2)] [] ”
EVAL “mk_distict_labels [("a",1);("a",2)] [] ”
EVAL “mk_distict_labels [("a",1);("a",2);("b",1);("a",3)] [] ”
EVAL  “mk_distict_labels [("p",1);("c",2)] []”
*)
        

        
Definition replace_mem_def:
(replace_mem [] m = []) ∧
(replace_mem ((p,n)::l) (p',n') =
 if p'=p then
   (p,n')::replace_mem l (p',n')
 else
   (p,n)::replace_mem l (p',n')    
)    
End



Definition replace_all_def:
  (replace_all l [] = l) ∧
  (replace_all l (h::disctict_l) =
    let replaced = replace_mem l h in
         replace_all replaced disctict_l
  )     
End

 

Definition merge_leaves_labels_def:
  (merge_leaves_labels [] = []) ∧
  (merge_leaves_labels l =
    let distinct_l = mk_distict_labels l [] in           
      replace_all l distinct_l
  )     
End
        
(*        
EVAL “merge_leaves_labels [("p",1);("c",2);("p",1)]”;
EVAL “merge_leaves_labels [("p",1);("p",2);("p",1)]”;
*)
        


Definition mirror_domain_range_def:
  mirror_domain_range l =
    MAP (\(x,y). (y,x)) l
End




Definition update_merged_edges_def:
  (update_merged_edges [] [] = [])  ∧
  (update_merged_edges ((n1,p)::(n1',p')::new_labels) ((n2,n2',n2'')::new_edges) =
     ((n2,n1,n1')::update_merged_edges new_labels new_edges))
End        


Definition segment_non_term_def:           
  segment_non_term leaves_termn labelings =
  if leaves_termn = [] then
     labelings
  else
    SEG (LENGTH leaves_termn) 0 labelings
End          

Definition merge_all_nodes_def:
  merge_all_nodes leaves_termn (new_edges:edges) (new_labels:labelings) =
              
  (* first we merge all nodes that are newly created within the same level, aka new leaves*)
  let mirrored_labeling = mirror_domain_range (leaves_termn++new_labels) in
       let merged_leaves = merge_leaves_labels mirrored_labeling in
         let mirrored_labeling = mirror_domain_range merged_leaves in
             
           let new_labels' =  segment_non_term leaves_termn mirrored_labeling in
             let new_edges'  =  update_merged_edges new_labels' new_edges in
               (new_edges',nub new_labels')
End

         

Definition update_non_term_var_def:        
  update_non_term_var leaves_nontermn x =
  MAP (\(n,p). (n, non_termn (SOME x,p))) leaves_nontermn
End




Definition non_term_leaf_updt_def:
  non_term_leaf_updt (l1:(num # label) list) (x:string) =
    MAP (λ(n, lbl).
      case lbl of
      | termn p => (n, termn p)
      | non_termn (NONE, p) => (n, non_termn (SOME x, p))
      | non_termn (SOME x', p) => (n, non_termn (SOME x', p))
        ) l1
End



Definition body_of_mk_def:
  body_of_mk (BDD:BDD) (x:string) (c:num) =
  (let (r,edges,labels) = BDD in
    (let leaves = getLeaves edges r in
       (case (getLabels labels leaves) of
        | SOME leaves_labels =>
            ( case (extract_termn leaves_labels) of
              (* this is incorrect , there can be non terminat *)
              | SOME leaves_termn =>
                  ( case (extract_nontermn leaves_labels) of
                    | SOME leaves_nontermn =>
                        ( let leaves_sub = leaves_pred_sub leaves_nontermn x in
                            let simp_leaves = simp_pred_list leaves_sub in
                              let simp_leaves' = determine_termn_list simp_leaves in
                                let new_labels = mk_new_labels simp_leaves' c in
                                  let new_edges = mk_new_edges simp_leaves' c in
                                    let label_leaf_updated = non_term_leaf_updt labels x
                                    in
                                     SOME (((r,  edges ++ new_edges, label_leaf_updated++new_labels):BDD),  (c + LENGTH leaves_nontermn + 1))             
                        )
                    | NONE => NONE
                  )
              | NONE => NONE
           )
        | NONE => NONE
       )
   ))
End


Definition mk_BDDPred_def:
  (mk_BDDPred (BDD:BDD) l [] c = SOME BDD) ∧
  (mk_BDDPred (BDD:BDD) l (x::xs) c =
   case (body_of_mk BDD (x:string) (c:num)) of
   | SOME (BDD',c') => mk_BDDPred BDD' (x::l) xs c'
   | NONE => NONE 
  )
End



        

(*
EVAL “mk_BDDPred (0,[],[(0, non_termn (NONE, (Var "a")))]) [] ["a"] 1”;
EVAL “mk_BDDPred (0,[],[(0, non_termn (SOME "a", (Var "a")))]) [] ["a"] 1”;
EVAL “mk_BDDPred (0,[],[(0, non_termn (NONE, (And (Var "a") (Var "b"))))]) [] ["a";"b"] 1”;
EVAL “mk_BDDPred (0,[],[(0, non_termn (NONE, Or (Var "a") (Var "b")))]) [] ["a";"b";"c"] 1”;
*)                


                                                                                
(*
val toBDD_pred_def = Define `
  toBDD_pred P vars = mk_BDDPred (0, [], [(0, non_termn ( HD vars , P))]) vars 1`;
*)



Definition size_of_tree_def:
  size_of_tree (edges:edges) (n:num) =
               
( case ALOOKUP edges n of
  | SOME (l,r) => 1 + size_of_tree (DELETE_ELEMENT (n,l,r) edges) l + size_of_tree (DELETE_ELEMENT (n,l,r) edges) r
  | NONE =>  (1:num)
)
Termination
WF_REL_TAC `measure (\(edges,n). LENGTH edges)` >>
REPEAT STRIP_TAC >>
gvs[LENGTH_DELETE_ELEMENT_LE, ALOOKUP_MEM]
End

                                                       
        

Definition from_pred_to_bool_def:
  from_pred_to_bool p mv =
  case p of
  |  (termn True)  => SOME T
  |  (termn False) => SOME F
  |  (termn _) => NONE
  |  (non_termn (_,p)) => Sem_rule p mv
End



        
(*
Definition Sem_BDDpred_fun_def:
  Sem_BDDpred_fun ((root,edges,labels):BDD) (m_v:(string#bool)list) n=
    case ALOOKUP edges n of
      | NONE =>
          (case ALOOKUP labels n of
             | SOME (termn True)  => SOME T
             | SOME (termn False) => SOME F
             | SOME (termn _) => NONE
             | SOME (non_termn (_,p)) => Sem_rule p m_v
             | NONE => NONE )
      | SOME (l,r) =>
          case ALOOKUP labels n of
             | SOME (non_termn (SOME x,p)) =>
                   ( case ALOOKUP m_v x of
                        | SOME T => Sem_BDDpred_fun (root,edges,labels) m_v r
                        | SOME F => Sem_BDDpred_fun (root,edges,labels) m_v l
                        | NONE => NONE )
             | _ => NONE
End
*)

        

Inductive BDD_pred_sem:
(* defn pred_red *)
  
[pred_red_leaf:]
  ( ∀ (root:num) (edges:edges) (labels:labelings) (mv:(string#bool)list) (n:num) (p:label).
      ALOOKUP edges n = NONE ∧
      ALOOKUP labels n  = SOME p 
      ⇒      
      BDD_pred_sem (r,edges,labels) mv n (from_pred_to_bool p mv) 
  )
  
  
[pred_red_internal_T:]
  ( ∀ (root:num) (edges:edges) (labels:labelings) (mv:(string#bool)list) (n:num) (l:num) (r:num) (pred:pred) (x:string) (b':bool option).
      ALOOKUP edges n = SOME (l,r) ∧
      ALOOKUP labels n  = SOME (non_termn (SOME x ,pred)) ∧
      ALOOKUP mv x = SOME T ∧
      BDD_pred_sem (root,edges,labels) mv l b'
      ⇒      
      BDD_pred_sem (root,edges,labels) mv n b'
  )
  
[pred_red_internal_F:]
  ( ∀ (root:num) (edges:edges) (labels:labelings) (mv:(string#bool)list) (n:num) (l:num) (r:num) (pred:pred) (x:string) (b':bool option).
      ALOOKUP edges n = SOME (l,r) ∧
      ALOOKUP labels n  = SOME (non_termn (SOME x ,pred)) ∧
      ALOOKUP mv x = SOME F ∧
      BDD_pred_sem (root,edges,labels) mv r b'
      ⇒      
      BDD_pred_sem (root,edges,labels) mv n b'
  )            
End


       

       
Definition get_prop_def:
  get_prop labels n =
  (case ALOOKUP labels n of
   | SOME (termn True) => SOME True
   | SOME (termn False) => SOME False
   | SOME (termn _) => NONE
   | SOME (non_termn (x,p)) => SOME p
   | NONE => NONE
  )
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
  REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) 
QED





        

(* must add free variables condition here,
   Otherwise we might need to prove something like this which is incorrect:
   Sem_rule (And True (Var x)) mv = Sem_rule (simp_pred (And True (Var x))) mv
   where the simplification will give us true, even if Var x is not in mv = NONE

   EDIT: there are many thing that can go wrong, actuallt false and none
*)       
          


Theorem simplification_correct:
  ∀p mv. (∀x. MEM x (FV p) ⇒ (∃b. ALOOKUP mv x = SOME b)) ⇒
     Sem_rule p mv = Sem_rule (simp_pred p) mv
Proof
  Induct_on `p` >-
   (rw[simp_pred_def, Sem_rule_def]) >-
   (rw[simp_pred_def, Sem_rule_def]) >-
   (rw[simp_pred_def, Sem_rule_def]) >>

  rpt strip_tac >>
  IMP_RES_TAC mem_imp_sem_rule >>

  LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘mv’])) >>
  gvs[FV_def] >>
  gvs[Sem_rule_def] >>   

  rw[Sem_rule_def, simp_pred_def] >>   
  REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  gvs[Sem_rule_def, simp_pred_def] >>
  
  FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘s’])) >>
  IMP_RES_TAC simp_pred_imp_mem >>
  gvs[]
        
QED

        
             



    

    
Theorem non_term_leaf_updt_concat:    
∀ x l1 l2.
non_term_leaf_updt (l1++l2) x = non_term_leaf_updt l1 x ++ non_term_leaf_updt l2 x
Proof    
fs[non_term_leaf_updt_def]
QED


Theorem non_term_leaf_updt_cons:        
∀ l h x . non_term_leaf_updt (h::l) x = non_term_leaf_updt [h] x ++ non_term_leaf_updt l x
Proof
fs[non_term_leaf_updt_def]
QED



        
        
Theorem non_term_leaf_updt_rec:
∀ l x x'.                                                                                
non_term_leaf_updt ( non_term_leaf_updt l x ) x' =  non_term_leaf_updt l x 
Proof
  Induct >>
  rpt strip_tac >-
   gvs[non_term_leaf_updt_def] >>

   Cases_on ‘h’ >>
   Cases_on ‘r’ >>
   gvs[non_term_leaf_updt_def] >>

   Cases_on ‘p’ >>
   Cases_on ‘q'’ >>
   gvs[non_term_leaf_updt_def]
QED
   



                                                                  
Theorem mk_BDDPred_output:
  ∀ vars vars_consumed r r' edges edges' labels labels'  c.
    vars ≠ [] ∧ 
mk_BDDPred (r, edges, labels) vars_consumed vars c = SOME (r', edges', labels') ⇒
 r = r' ∧ ∃ edges'' labels''. edges' = edges ++ edges'' ∧ labels' = (non_term_leaf_updt labels (HD vars)) ++ labels''
Proof                                                                                                                                                         
Induct_on ‘vars’ >- fs[mk_BDDPred_def] >>

Cases_on ‘vars = []’ >> gvs[] >>
rpt strip_tac >>
gvs[mk_BDDPred_def, body_of_mk_def] >> 
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>

‘∃ leaves_sub . leaves_pred_sub x' h = leaves_sub’ by gvs[] >>
‘∃ simp_leaves . simp_pred_list leaves_sub = simp_leaves’ by gvs[] >>
‘∃ simp_leaves' . determine_termn_list simp_leaves = simp_leaves'’ by gvs[] >>
    
rgs[] >>
(RES_TAC) >>

gvs[non_term_leaf_updt_rec, non_term_leaf_updt_concat]
QED                           




                     
             

Theorem SNOC_rw:
∀ l x .
SNOC x l = l ++[x]
Proof
gvs[SNOC]
QED


        
Definition get_string_in_label_def:
  get_string_in_label (labels:labelings)  vars_consumed n =
  case ALOOKUP (labels:labelings) n of
  | NONE =>  0
  | SOME lbl => (
    case lbl of
    | termn p =>  0
    | non_termn (NONE,p) =>  0
    | non_termn (SOME x,p) =>  THE (INDEX_OF x vars_consumed) 
    ) 
End



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




   
                  
(*
  measureInduct_on `get_string_in_label labels  vars_consumed n` >>
*)                   




Inductive BDD_ind:
(* defn pred_red *)
  
[BDD_ind_leaf:]
  ( ∀ (root:num) (edges:edges) (labels:labelings) (n:num) (P:(BDD -> 'a)).
      ALOOKUP edges n = NONE ∧
      ALOOKUP labels n  = SOME p 
      ⇒      
      BDD_ind (r,edges,labels) n (P (r,edges,labels)) 
  )
  
  
[BDD_ind_internal_T:]
  ( ∀ (root:num) (edges:edges) (labels:labelings) (n:num) (l:num) (r:num) (pred:pred) (x:string) (a:'a).
      ALOOKUP edges n = SOME (l,r) ∧
      ALOOKUP labels n  = SOME (non_termn (SOME x ,pred)) ∧
      BDD_ind (root,edges,labels) l a
      ⇒      
      BDD_ind (root,edges,labels) n a
  )
  
[BDD_ind_internal_F:]
  ( ∀ (root:num) (edges:edges) (labels:labelings) (n:num) (l:num) (r:num) (pred:pred) (x:string) (a:'a).
      ALOOKUP edges n = SOME (l,r) ∧
      ALOOKUP labels n  = SOME (non_termn (SOME x ,pred)) ∧
      BDD_ind (root,edges,labels) r a
      ⇒      
      BDD_ind (root,edges,labels) n a
  )           
End





Definition correct_sem_def:
  correct_sem (BDD:BDD)  =
  ∀ n mv b r edges labels lbl.
    BDD = (r,edges,labels) ∧
    ALOOKUP labels n = SOME lbl ∧
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


Definition mv_dom_bdd_def:
  mv_dom_bdd mv (root,edges,labels) = 
  ∀ n pred x.
    (ALOOKUP labels n = SOME (non_termn (SOME x,pred))) ⇔
    is_lookup_defined mv x
End


Definition consumed_dom_bdd_def:
  consumed_dom_bdd vars_consumed ((root,edges,labels):BDD) = 
  ∀ n pred x.
    (ALOOKUP labels n = SOME (non_termn (SOME x,pred))) ⇔
    MEM x vars_consumed
End        


Theorem MEM_INDEX_OF:           
∀ l x .
MEM x l ⇒
∃ i . INDEX_OF x l = SOME i
Proof                                
Induct >>                                
rpt strip_tac >>
gvs[INDEX_OF_def,  INDEX_FIND_def] >>
Cases_on ‘x=h’ >> gvs[] >>
RES_TAC >>
PairCases_on ‘z’ >>
imp_res_tac P_implies_next >>
gvs[]
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
      gvs[BDD_WF_def, is_lookup_leaf_def]
      ,
      
      PairCases_on ‘x’ >> gvs[] >>
     
      subgoal ‘∃pred x'.ALOOKUP labels n1 = SOME (non_termn (SOME x',pred))’ >-
       (
       rgs[Once BDD_WF_def, Once is_lookup_non_leaf_def, Once is_lookup_defined_def] >>
       first_x_assum (strip_assume_tac o (Q.SPECL [‘n1’])) >>
       gvs[]
       ) >>
      gvs[] >>
      
      subgoal ‘∃b . ALOOKUP mv x'' = SOME b’ >-
       (
       gvs[mv_dom_bdd_def, is_lookup_defined_def]
       ) >>
      
      ‘MEM x' vars_consumed ∧ MEM x'' vars_consumed’ by rgs[Once consumed_dom_bdd_def] >>
      imp_res_tac MEM_INDEX_OF >>
      
      subgoal ‘THE (INDEX_OF x'' vars_consumed) < THE (INDEX_OF x' vars_consumed)’ >-
       (
       
       rgs[Once BDD_ordered_def]>>
       first_x_assum (strip_assume_tac o (Q.SPECL [‘n’,‘n1’, ‘n2’,‘x'’, ‘x''’,‘x'''’,
                                                   ‘pred’, ‘pred'’,‘pred'''’,‘i'’,‘i’,‘i''’])) >>
       
       rgs[]
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
        gvs[BDD_WF_def, is_lookup_leaf_def]
        ,
        
        PairCases_on ‘x’ >> gvs[] >>

        subgoal ‘∃pred x'.ALOOKUP labels n2 = SOME (non_termn (SOME x',pred))’ >-
         (
         rgs[Once BDD_WF_def, Once is_lookup_non_leaf_def, Once is_lookup_defined_def] >>
         first_x_assum (strip_assume_tac o (Q.SPECL [‘n2’])) >>
         gvs[]
         ) >>
        gvs[] >>
        

        subgoal ‘∃b . ALOOKUP mv x'' = SOME b’ >-
         (
         gvs[mv_dom_bdd_def, is_lookup_defined_def]
         ) >>
        
        
        ‘MEM x' vars_consumed ∧ MEM x'' vars_consumed’ by rgs[Once consumed_dom_bdd_def] >>
        imp_res_tac MEM_INDEX_OF >>
       
        
        subgoal ‘THE (INDEX_OF x'' vars_consumed) < THE (INDEX_OF x' vars_consumed)’ >-
         (
         
         rgs[Once BDD_ordered_def]>>
         first_x_assum (strip_assume_tac o (Q.SPECL [‘n’,‘n1’, ‘n2’,‘x'’, ‘x'''’,‘x''’,
                                                     ‘pred’, ‘pred'''’,‘pred'’,
                                                     ‘i'’,‘i''’,‘i’])) >>
         
         rgs[]
         ) >>
        
        first_x_assum (strip_assume_tac o (Q.SPECL [‘INDEX_OF (x'':string) (vars_consumed: string list)’])) >>
        gvs[] >>
        first_x_assum (strip_assume_tac o (Q.SPECL [‘x''’, ‘vars_consumed’])) >>
        gvs[] >>
        METIS_TAC[]
      ]
                                           
    ]          
QED



        
Theorem BDD_pred_sem_exsists:
  ∀ BDD mv n vars_consumed.
    BDD_ordered BDD vars_consumed ∧
    mv_dom_bdd mv BDD  ∧
    consumed_dom_bdd vars_consumed BDD ∧
    BDD_WF BDD ⇒
  ∃ b . BDD_pred_sem BDD mv n b
Proof
 rgs[Once BDD_pred_sem_cases] >>
 rpt strip_tac >>

 PairCases_on ‘BDD’ >>
 rename1 ‘(root,edges,labels)’ >>

 rgs[] >>

 Cases_on ‘ALOOKUP edges n’ >> gvs[] >| [
    gvs[BDD_WF_def, is_lookup_leaf_def]
    ,
    PairCases_on ‘x’ >> gvs[] >>
    subgoal ‘∃pred x'.ALOOKUP labels n = SOME (non_termn (SOME x',pred))’ >-
     (
     gvs[BDD_WF_def, is_lookup_non_leaf_def, is_lookup_defined_def] >>
     last_x_assum (strip_assume_tac o (Q.SPECL [‘n’])) >>
     gvs[]
     ) >>
    gvs[] >>

    subgoal ‘∃b . ALOOKUP mv x' = SOME b’ >-
     (
     gvs[mv_dom_bdd_def, is_lookup_defined_def]
     ) >>

    METIS_TAC[BDD_pred_sem_exsists_inter]
  ]
QED






 (**********)     

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

    RES_TAC >>

    

            
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

        






        
Theorem lookup_labels_in_updt:
∀ labels n x p h.
ALOOKUP labels n = SOME (non_termn (SOME x,p)) ⇒
ALOOKUP (non_term_leaf_updt labels h) n = SOME (non_termn (SOME x,p))
Proof
Induct >>
rpt strip_tac >>
simp[non_term_leaf_updt_def] >>
PairCases_on ‘h’ >> gvs[ALOOKUP_def] >>
gvs[AllCaseEqs()] >>
Cases_on ‘h1’ >> gvs[] >>
last_x_assum (strip_assume_tac o (Q.SPECL [‘n’, ‘x’, ‘p’, ‘h'’])) >>
gvs[non_term_leaf_updt_def] >>
Cases_on ‘p'’ >> gvs[] >>
Cases_on ‘q’ >> gvs[]
QED
    




        
Theorem lookup_labels_in_updt_none:
∀ labels n x p h.
ALOOKUP labels n = SOME (non_termn (NONE,p)) ⇒
ALOOKUP (non_term_leaf_updt labels h) n = SOME (non_termn (SOME h,p))
Proof
Induct >>
rpt strip_tac >>
gvs[ALOOKUP_def] >>

gvs[Once non_term_leaf_updt_cons] >>
rgs[ALOOKUP_APPEND]>>
gvs[AllCaseEqs()] >>

PairCases_on ‘h’ >> 
gvs[AllCaseEqs()] >>
simp[non_term_leaf_updt_def] >>


Cases_on ‘h1’ >> gvs[] >>
Cases_on ‘p'’ >> gvs[] >>
Cases_on ‘q’ >> gvs[]
QED
    



        
Theorem WF_imp_non_leaf_lbl:
∀ r edges labels n n' n'' h.      
BDD_WF (r,edges,labels) ∧
ALOOKUP edges n = SOME (n',n'') ⇒
∃ x p . ALOOKUP labels n = SOME (non_termn (SOME x,p))
Proof
gvs[BDD_WF_def] >>
rpt strip_tac >>
last_x_assum (strip_assume_tac o (Q.SPECL [‘n’])) >> gvs[is_lookup_defined_def, is_lookup_non_leaf_def] 
QED


Theorem wf_lookup_if_edges_label:    
∀ r edges labels n n' n'' h.      
BDD_WF (r,edges,labels) ∧
ALOOKUP edges n = SOME (n',n'') ⇒
∃ x p . ALOOKUP (non_term_leaf_updt labels h) n = SOME (non_termn (SOME x,p))
Proof
rpt strip_tac >>                                                                  
IMP_RES_TAC WF_imp_non_leaf_lbl >>
IMP_RES_TAC lookup_labels_in_updt >>                      
gvs[]
QED












Theorem lookup_new_edges_simp_exists:
∀ simp_leaves' new_edges nn n c.
  ALOOKUP new_edges n = SOME nn ∧
  mk_new_edges simp_leaves' c = new_edges ⇒
∃ sll . ALOOKUP simp_leaves' n = SOME sll
Proof
Induct >> 
rgs[mk_new_edges_def]>>         
rpt strip_tac >>
PairCases_on ‘h’ >>
rgs[mk_new_edges_def] >>
rgs[AllCaseEqs()] >>
RES_TAC >> gvs[]
QED


Theorem lookup_simp_leaves_determine_exists:
∀ simp_leaves simp_leaves' n sll.        
ALOOKUP simp_leaves' n = SOME sll ∧        
determine_termn_list simp_leaves = simp_leaves' ⇒
∃ sll' . ALOOKUP simp_leaves n = SOME sll'
Proof
Induct >> 
rgs[determine_termn_list_def]>>         
rpt strip_tac >>
PairCases_on ‘h’ >>
rgs[determine_termn_def] >>
rgs[AllCaseEqs()] >>
RES_TAC >> gvs[]
QED



Theorem  lookup_simp_pred_leaves_sub_exists:      
∀ leaves_sub simp_leaves n sll.
ALOOKUP simp_leaves n = SOME sll ∧        
simp_pred_list leaves_sub = simp_leaves ⇒
∃ sll' . ALOOKUP leaves_sub n = SOME sll'
Proof
Induct >> 
rgs[simp_pred_list_def]>>         
rpt strip_tac >>
PairCases_on ‘h’ >>
rgs[AllCaseEqs()]
QED


Theorem lookup_leaves_sub_pred_exists:
∀ ntl  leaves_sub sll n h.       
ALOOKUP leaves_sub n = SOME sll ∧
leaves_pred_sub ntl h = leaves_sub ⇒
∃ p . ALOOKUP ntl n = SOME p
Proof
Induct >> 
rgs[leaves_pred_sub_def]>>         
rpt strip_tac >>
PairCases_on ‘h’ >>
rgs[AllCaseEqs()] >>
RES_TAC >> gvs[]
QED                



Theorem extract_nontermn_not_inner_node:                   
∀ leaves ntl n .                            
extract_nontermn leaves = SOME ntl ⇒
∃ x p' . ALOOKUP leaves n ≠ SOME (non_termn (SOME x,p'))
Proof
Induct >-
rgs[extract_nontermn_def]>>         
rpt strip_tac >>
PairCases_on ‘h’ >>
gvs[]>>
Cases_on ‘h0=n’ >> gvs[] >> rgs[extract_nontermn_def] >>                   
Cases_on ‘h1’ >> rgs[AllCaseEqs()]
QED



        
Theorem lookup_ntl_updt_none:
∀ labels h n .
ALOOKUP (non_term_leaf_updt labels h) n = NONE ⇒
ALOOKUP labels n = NONE
Proof
Induct >- gvs[non_term_leaf_updt_def] >>                        
rpt strip_tac >>
gvs[Once non_term_leaf_updt_cons] >>
gvs[] >>

PairCases_on ‘h’>>
rgs[AllCaseEqs()] >>
                        
gvs[ALOOKUP_APPEND] >>
rgs[AllCaseEqs()] >>

RES_TAC >> 
gvs[non_term_leaf_updt_def] >>          
Cases_on ‘h1’ >> gvs[] >>
Cases_on ‘p’ >> gvs[] >>
Cases_on ‘q’ >> gvs[]
QED


        
Theorem mk_body_map1:
∀ leaves labels leaves_labels .        
getLabels labels leaves = SOME leaves_labels ⇒
(leaves = MAP FST  leaves_labels)
Proof
  Induct >>
  rpt strip_tac >>
  gvs[getLabels_def] >>
  REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  RES_TAC 
QED


Theorem mk_body_map2:
  ∀ ntl leaves_sub h.
    leaves_pred_sub ntl h = leaves_sub ⇒
    MAP FST ntl = MAP FST leaves_sub 
Proof
  Induct >>
  gvs[leaves_pred_sub_def] >>
  rpt strip_tac >>
  PairCases_on ‘h’ >> gvs[] 
QED

        
Theorem mk_body_map3:
  ∀ leaves_sub simp_leaves h.
    simp_pred_list leaves_sub = simp_leaves ⇒
    MAP FST leaves_sub = MAP FST simp_leaves 
Proof
  Induct >>
  gvs[simp_pred_list_def] >>
  rpt strip_tac >>
  PairCases_on ‘h’ >> gvs[] 
QED


Theorem mk_body_map4:
  ∀ leaves_simp leaves_simp' h.
    determine_termn_list leaves_simp = leaves_simp' ⇒
    MAP FST leaves_simp = MAP FST leaves_simp' 
Proof
  Induct >>
  gvs[determine_termn_list_def] >>
  rpt strip_tac >>
  PairCases_on ‘h’ >> gvs[] 
QED

        
Theorem mk_body_map5:
  ∀ leaves_simp' new_edges c.
    mk_new_edges leaves_simp' c = new_edges ⇒
    MAP FST leaves_simp' = MAP FST new_edges
Proof
  Induct >>
  gvs[mk_new_edges_def] >>
  rpt strip_tac >>
  PairCases_on ‘h’ >> gvs[mk_new_edges_def] 
QED



Theorem mk_body_map6:
  ∀ labels updated_labels x.
    non_term_leaf_updt labels x = updated_labels ⇒
    MAP FST labels = MAP FST updated_labels
Proof
  Induct >>
  gvs[non_term_leaf_updt_def] >>
  rpt strip_tac >>
  PairCases_on ‘h’ >>
  gvs[AllCaseEqs()] >>                      
  Cases_on ‘h1’ >> gvs[] >>
  Cases_on ‘p’ >> gvs[] >>
  Cases_on ‘q’ >> gvs[]
QED





        
        
        
Theorem extract_nonterm_mem_neg:        
∀ leaves_labels ntl h.
¬MEM h (MAP FST leaves_labels) ∧
extract_nontermn leaves_labels = SOME ntl ⇒
¬MEM h (MAP FST ntl)
Proof
  Induct >>
  rpt strip_tac >>
  gvs[extract_nontermn_def] >>
  PairCases_on ‘h’ >> gvs[] >>
  gvs[extract_nontermn_def] >>
  gvs[AllCaseEqs()]                      
QED


        
  

Theorem all_distinct_leaves:
∀ edges r leaves .        
ALL_DISTINCT (MAP FST edges) ∧
getLeaves edges r = leaves ⇒
ALL_DISTINCT leaves
Proof
Induct >>
gvs[getLeaves_def] >>
rpt strip_tac >>
gvs[AllCaseEqs()] >>
PairCases_on ‘h’ >>
gvs[get_leaves_list_def]
QED



Theorem all_distinct_leaves_labels:
∀ leaves labels leaves_labels .        
ALL_DISTINCT leaves ∧
getLabels labels leaves = SOME leaves_labels ⇒
ALL_DISTINCT (MAP FST leaves_labels)
Proof
rpt strip_tac >>
imp_res_tac mk_body_map1 >>
gvs[]
QED

        
 
        
Theorem all_distinct_ntl:
  ∀ leaves_labels ntl .
  ALL_DISTINCT (MAP FST leaves_labels) ∧
  extract_nontermn leaves_labels = SOME ntl ⇒
  ALL_DISTINCT (MAP FST ntl)                  
Proof
  Induct >>
  rpt strip_tac >>
  gvs[extract_nontermn_def] >>
  PairCases_on ‘h’ >> gvs[] >>
  gvs[extract_nontermn_def] >>
  gvs[AllCaseEqs()] >>
  imp_res_tac extract_nonterm_mem_neg
QED   





Theorem all_distinct_sub:
  ∀ ntl leaves_sub h.
    ALL_DISTINCT (MAP FST ntl) ∧
    leaves_pred_sub ntl h = leaves_sub ⇒
    ALL_DISTINCT (MAP FST leaves_sub) 
Proof
  rpt strip_tac >>
  imp_res_tac mk_body_map2 >>
  gvs[] 
QED


        
Theorem all_distinct_simp:
  ∀ simp_leaves leaves_sub h.
    ALL_DISTINCT (MAP FST leaves_sub) ∧
    simp_pred_list leaves_sub = simp_leaves ⇒
         ALL_DISTINCT (MAP FST simp_leaves)               
Proof
  rpt strip_tac >>
  imp_res_tac mk_body_map3 >>
  gvs[]  
QED



Theorem all_distinct_determine:
  ∀ simp_leaves simp_leaves' h.
    ALL_DISTINCT (MAP FST simp_leaves) ∧
    determine_termn_list simp_leaves = simp_leaves' ⇒
         ALL_DISTINCT (MAP FST simp_leaves')               
Proof
  rpt strip_tac >>
  imp_res_tac mk_body_map4 >>
  gvs[]  
QED



        
Theorem all_distinct_mk_edges:
  ∀ simp_leaves' new_edges c.
    ALL_DISTINCT (MAP FST simp_leaves') ∧
    mk_new_edges simp_leaves' c = new_edges ⇒
    ALL_DISTINCT (MAP FST new_edges)               
Proof
  rpt strip_tac >>
  imp_res_tac mk_body_map5 >>
  gvs[]  
QED



        
Theorem all_distinct_non_term_leaf_updt:        
∀ labels updated_labels h.
  ALL_DISTINCT (MAP FST labels) ∧
  non_term_leaf_updt labels h = updated_labels ⇒
  ALL_DISTINCT (MAP FST updated_labels)
Proof
  rpt strip_tac >>
  imp_res_tac mk_body_map6 >>
  gvs[]
QED





Triviality mk_new_label_idx_mem:
  ∀ simp_leaves n c.
    n>0 ⇒
    ¬MEM c (MAP FST (mk_new_labels simp_leaves (c + n))) 
Proof
Induct >>
gvs[mk_new_labels_def] >>
rpt gen_tac >>
PairCases_on ‘h’ >>
simp[mk_new_labels_def]
QED



       

Theorem all_distinct_mk_labels:      
  ∀ simp_leaves' new_labels c.
    ALL_DISTINCT (MAP FST simp_leaves') ∧
    mk_new_labels simp_leaves' c = new_labels ⇒
    ALL_DISTINCT (MAP FST new_labels)               
Proof
  Induct >>
  rgs[Once mk_new_labels_def] >>
  rpt strip_tac >>
  rgs[Once mk_new_labels_def] >>
  PairCases_on ‘h’ >>
  simp[Once mk_new_labels_def] >>
  gvs[mk_new_label_idx_mem] >>
  assume_tac mk_new_label_idx_mem >>
  first_x_assum (strip_assume_tac o (Q.SPECL [‘simp_leaves'’,‘1’,‘c+1’])) >>
  gvs[]           
QED






 
Theorem get_leaves_list_domain:
  ∀ edges leaves n.     
    MEM n (MAP FST edges) ∧
    get_leaves_list edges = leaves
    ⇒
    ~ MEM n leaves
Proof
  Induct >>
  rpt strip_tac >- gvs[get_leaves_list_def] >>
  PairCases_on ‘h’ >>
  rgs[] >>
  res_tac >>
  rgs[Once get_leaves_list_def] >>
  gvs[get_leaves_list_def] >>
  REPEAT (BasicProvers.FULL_CASE_TAC >> rgs[]) >>
  rgs[MEM_FILTER]
QED


Triviality getLeaves_list_eq:      
∀ l h r .
getLeaves (h::l) r = get_leaves_list (h::l)
Proof                                        
gvs[getLeaves_def, get_leaves_list_def]
QED




        
Theorem leaves_are_not_parents:         
∀ edges leaves n r.     
  MEM n (MAP FST edges) ∧
  getLeaves edges r = leaves ⇒
  ~ MEM n leaves
Proof
  Cases_on ‘edges’ >>
  rpt strip_tac >-
   gvs[getLeaves_def] >>
  imp_res_tac get_leaves_list_domain >>
  rgs[Once getLeaves_list_eq]          
QED




                     
   (*   

        
Theorem WFness_translation:
  ∀ vars vars_consumed BDD BDD' c.
    BDD_WF BDD ⇒
    (SOME BDD' = mk_BDDPred BDD vars_consumed vars c) ⇒
    BDD_WF BDD' 
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
    gvs[body_of_mk_def] >>
    REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>

    
    ‘∃ leaves_sub . leaves_pred_sub x' h = leaves_sub’ by gvs[] >>
    ‘∃ simp_leaves . simp_pred_list leaves_sub = simp_leaves’ by gvs[] >>
    ‘∃ simp_leaves' . determine_termn_list simp_leaves = simp_leaves'’ by gvs[] >>
    ‘∃ new_edges . mk_new_edges simp_leaves' c = new_edges’ by gvs[] >>
    ‘∃ new_labels . mk_new_labels simp_leaves' c = new_labels’ by gvs[] >>
    
    rgs[] >>


    subgoal ‘ALL_DISTINCT (MAP FST edges ⧺ MAP FST new_edges)’ >- (
            
      ‘ALL_DISTINCT (MAP FST edges)’ by rgs[Once BDD_WF_def] >>
      ‘∃ leaves. getLeaves edges r = leaves’ by gvs[] >>

      imp_res_tac all_distinct_leaves >>
      ‘ALL_DISTINCT (MAP FST x)’ by (imp_res_tac all_distinct_leaves_labels >> gvs[]) >>
      imp_res_tac all_distinct_ntl >>       
      imp_res_tac all_distinct_sub >>
      imp_res_tac all_distinct_simp >>
      ‘ALL_DISTINCT (MAP FST simp_leaves')’ by (imp_res_tac all_distinct_determine >> gvs[]) >>        
      ‘ALL_DISTINCT (MAP FST new_edges)’ by (imp_res_tac all_distinct_mk_edges >> gvs[]) >>
                  
      simp[ALL_DISTINCT_APPEND]>>
      strip_tac >> strip_tac >>
      imp_res_tac leaves_are_not_parents>>

      imp_res_tac mk_body_map1 >>
      imp_res_tac mk_body_map2 >>
      imp_res_tac mk_body_map3 >>
      imp_res_tac mk_body_map4 >>
      imp_res_tac mk_body_map5 >>
      rgs[] >>

      imp_res_tac extract_nonterm_mem_neg >>   
      gvs[ALOOKUP_NONE]
      ) >>





    subgoal ‘ALL_DISTINCT (MAP FST (non_term_leaf_updt labels h) ⧺ MAP FST new_labels)’ >-(

      ‘ALL_DISTINCT (MAP FST labels)’ by rgs[Once BDD_WF_def] >>
      ‘ALL_DISTINCT (MAP FST (non_term_leaf_updt labels h))’ by (imp_res_tac all_distinct_non_term_leaf_updt >> gvs[]) >>




      (* same as before *)
      ‘ALL_DISTINCT (MAP FST edges)’ by rgs[Once BDD_WF_def] >>
      ‘∃ leaves. getLeaves edges r = leaves’ by gvs[] >>

      imp_res_tac all_distinct_leaves >>
      ‘ALL_DISTINCT (MAP FST x)’ by (imp_res_tac all_distinct_leaves_labels >> gvs[]) >>
      imp_res_tac all_distinct_ntl >>       
      imp_res_tac all_distinct_sub >>
      imp_res_tac all_distinct_simp >>
      ‘ALL_DISTINCT (MAP FST simp_leaves')’ by (imp_res_tac all_distinct_determine >> gvs[]) >>        
      ‘ALL_DISTINCT (MAP FST new_edges)’ by (imp_res_tac all_distinct_mk_edges >> gvs[]) >>
      (*end*)
                    
      ‘ALL_DISTINCT (MAP FST new_labels)’ by (imp_res_tac all_distinct_mk_labels >> gvs[]) >>        
      simp[ALL_DISTINCT_APPEND]>>

      strip_tac >> strip_tac >>
      imp_res_tac leaves_are_not_parents>>
      (*if in labels changed, then in labels, then from efness in *)



      imp_res_tac mk_body_map1 >>
      imp_res_tac mk_body_map2 >>
      imp_res_tac mk_body_map3 >>
      imp_res_tac mk_body_map4 >>
      imp_res_tac mk_body_map5 >>
      imp_res_tac mk_body_map6 >>

      rgs[] >>

      imp_res_tac extract_nonterm_mem_neg >>   
      rgs[ALOOKUP_NONE] >>

      (* here ? *)   


      ‘MEM e (MAP FST (labels))’ by cheat >>
      ‘MEM e (MAP FST (edges))’ by cheat >>

      gvs[ALOOKUP_NONE] >>
      ‘¬MEM e (MAP FST x)’ by res_tac >>
      ‘¬MEM e (MAP FST new_edges)’ by res_tac >>
      cheat
      ) >>








      
          
    subgoal ‘BDD_WF (r,edges ⧺ new_edges,non_term_leaf_updt labels h ⧺ new_labels)’ >-  (
      simp[BDD_WF_def] >> CONJ_TAC >> rpt strip_tac  >| [
                       
          (* internal nodes *)
             
          rgs[is_lookup_defined_def, is_lookup_non_leaf_def] >>
          rgs[ALOOKUP_APPEND] >>
          
          Cases_on ‘ALOOKUP edges n’ >> rgs[] >|[
                   
            (* if not in old edges, and in the new edges , ALOOKUP edges n = NONE*)
            
            Cases_on ‘ALOOKUP (non_term_leaf_updt labels h) n’ >>
            REPEAT (BasicProvers.FULL_CASE_TAC >> rgs[]) >|[
              (* this is false *)
              rgs[BDD_WF_def] >>
              rgs[is_lookup_leaf_def] >>
              imp_res_tac lookup_ntl_updt_none >>
              gvs[]
              ,
              (* this was a leaf in edges, and then it became a parent in BDD''*)
              (* Cases_on ‘x''''’ >> rgs[] >>*)
              
              rgs[BDD_WF_def] >|[
                  
                  rgs[is_lookup_leaf_def]>>
                  imp_res_tac lookup_labels_in_updt_none >>
                  ‘x'⁴' = non_termn (SOME h,p)’ by gvs[] >>
                  rgs[is_lookup_non_leaf_def, is_lookup_defined_def] >>
                  ‘ALOOKUP edges n = NONE’ by res_tac >>
                  rgs[ALL_DISTINCT_APPEND]>>
                  cheat
                  ,
                  cheat
                  ,
                  cheat
                  
                ]                                   
            ]                                
            ,
          (* if not in new edges, and in old edges i.e. ALOOKUP edges n = SOME x'³'*)
          
          Cases_on ‘ALOOKUP (non_term_leaf_updt labels h) n’ >> rgs[] >|[
                rgs[BDD_WF_def] >>
                rgs[is_lookup_leaf_def] >>
                imp_res_tac lookup_ntl_updt_none >>
                rgs[is_lookup_defined_def, is_lookup_non_leaf_def] >>
                res_tac >>
                gvs[]
                ,
                imp_res_tac wf_lookup_if_edges_label >>
                PairCases_on ‘x'''’ >>
                ‘∃x p. ALOOKUP (non_term_leaf_updt labels h) n =
                       SOME (non_termn (SOME x,p))’ by (res_tac >> gvs[]) >>
                gvs[]
              ]
          ] 
                                                
          ,
                
          (* leafs*)


          rgs[is_lookup_leaf_def] >>
          rgs[ALOOKUP_APPEND] >>

          Cases_on ‘ALOOKUP edges n’ >> rgs[] >|[
              


            ]
          
          

                              
          cheat
        ]                                           
      ) >>
    RES_TAC
QED

     

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
    RES_TAC >> METIS_TAC[]
  ]
QED

*)


(*****************************)
(*********   MERGE    ********)
(*****************************)


Definition mergable_def:        
mergable ((r,edges,labels):BDD)  n n' = 
(ALOOKUP edges n = ALOOKUP edges n' ∧
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








(*


                
(*Lemma 3*)

∀ labels vars_consumed n'' r edges n' n mv.
BDD_ordered (r,edges,labels) vars_consumed ∧
mergable (r,edges,labels) n n' ⇒
Sem_BDDpred (r,edges,labels) mv n'' = Sem_BDDpred (r,merge (r,edges,labels) n n',labels) mv n''


 NTAC 3 strip_tac >>
  measureInduct_on `get_string_in_label labels  vars_consumed n''` >>
                                                                   
rpt strip_tac >>
simp[Sem_BDDpred_def]>>
simp[Once Sem_BDDpred_fun_def] >|[
    Cases_on ‘¬MEM n'' (nodes_list edges)’ >> gvs[] >|[
      ‘~ MEM n'' (nodes_list (point_parents (r,edges,labels) n n'))’ by cheat >>
      simp[Once Sem_BDDpred_fun_def]
      ,
      Cases_on ‘ALOOKUP edges n''’ >> gvs[] >|[
          Cases_on ‘ALOOKUP labels n''’ >> gvs[] >|[
            cheat
            ,
            cheat
           (* Cases_on ‘x’ >> gvs[] >|[
                (* if termin*)
                ‘p = True ∨ p = False’ by cheat >> gvs[] >>
                simp[Once EQ_SYM_EQ, Once Sem_BDDpred_fun_def] >>
                Cases_on ‘ALOOKUP (point_parents (r,edges,labels) n n') n''’ >> gvs[] >>
                ‘n'' ≠ n'’ by cheat >> (* again incorrect theorem *)
                cheat
                Cases_on ‘x’ >> gvs[] >>
                cheat
                ,
                Cases_on ‘p’ >> gvs[] >>

                simp[Once EQ_SYM_EQ, Once Sem_BDDpred_fun_def] >>
                ‘MEM n'' (nodes_list (point_parents (r,edges,labels) n n'))’ by cheat >> gvs[] >>
                ‘ALOOKUP (point_parents (r,edges,labels) n n') n'' = NONE’ by cheat >> gvs[]
                Cases
              ]                                      
                                    
          ]*)
        ]
          ,

          PairCases_on ‘x’ >> gvs[] >>
          Cases_on ‘ALOOKUP labels n''’ >> gvs[] >|[
              cheat
              ,
              Cases_on ‘x’ >> gvs[] >| [
                  cheat
                  ,
                  Cases_on ‘p’ >> gvs[] >> Cases_on ‘q’ >> gvs[] >|[
                      cheat
                      ,
                      Cases_on ‘ALOOKUP mv x’ >> gvs[] >| [
                          cheat
                          ,
                          Cases_on ‘x'’ >> gvs[] >| [
                              simp[Once EQ_SYM_EQ, Once Sem_BDDpred_fun_def] >>
                              Cases_on ‘¬MEM n'' (nodes_list (point_parents (r,edges,labels) n n'))’ >> gvs[]  >|[
                                (* if we do not find it, then it must have been merged, thus, n'' = n' *)
                                   ‘n'' = n'’ by cheat >>
                                   gvs[] >>
                                      (* this is an incorrect theorem as the merged node actually disappears..
                                      thus in the onld one it had semantics, and in the new one it does not*)
                                   cheat >> (*problem *)
                                   ,
                                   Cases_on ‘ALOOKUP (point_parents (r,edges,labels) n n') n''’ >> gvs[]  >| [
                                       gvs[ALOOKUP_MEM]
                                   cheat    
                                   ,
                                   Cases_on ‘x'’ >> gvs[] >>
                                   (* we check if these are parents or not of merged, they are parents if their
                                      indexes changed in teh graph*)
                                   Cases_on ‘ALOOKUP (point_parents (r,edges,labels) n n') n'' =
                                             ALOOKUP edges n''’ >> gvs[] >| [
                                       (* not a changed parent *)
                                       
                                       subgoal ‘get_string_in_label labels vars_consumed r'' <
                                                get_string_in_label labels vars_consumed n''’ >-(
                                       rgs[Once BDD_ordered_def] >>
                                       first_x_assum (strip_assume_tac o (Q.SPECL [‘n''’,‘q’,‘r''’,‘x’,‘x'’,‘’])) >>
                                       gvs[get_string_in_label_def] >>
                                       Cases_on ‘ALOOKUP labels r''’ >> gvs[]

                                                
                                       )

                                          
                                       ‘get_string_in_label labels vars_consumed r'' <
                                        get_string_in_label labels vars_consumed n''’ by cheat >>

                                       first_x_assum (strip_assume_tac o (Q.SPECL [‘r''’])) >>
                                       gvs[] >>
                                        
                                       first_x_assum (strip_assume_tac o (Q.SPECL [‘r’,
                                                                                   ‘edges’,
                                                                                   ‘n'’, ‘n’, ‘mv’])) >>
                                        
                                       gvs[] >>
                                       rgs[Sem_BDDpred_def] >>
                                       cheat
                                       ,
                                       (* this means that teh parent has changed and
                                       rerouted to new choldren*)


                                       Cases_on ‘q=x0’ >> gvs[] >|[
                                            ‘x1=n'’ by cheat >> gvs[] >>                    
                                            ‘r''=n’ by cheat >> gvs[] >>
                                            gvs[mergable_def]

                                        
                                     ]
                                           

                                     ]
                                   
                              ]
                            ]

                        ]

                    ] 
                  
                ]

            ]                                         
          
                                                   
        ]
                                              

                                              
                                              
                                              
    ]






  ]



*)








                                                                   




        
Theorem merge_correct:        
  ∀ r edges labels vars_consumed n n'.
    BDD_WF (r,edges,labels) ∧
    consumed_dom_bdd vars_consumed (r,edges,labels) ∧
    correct_sem (r,edges,labels) ∧
    BDD_ordered (r,edges,labels) vars_consumed ∧           
    mergable (r,edges,labels) n n'
    ==>
    correct_sem (merge (r,edges,labels) n n')
Proof

  rpt strip_tac >>   
  simp[Once correct_sem_def] >>
  rpt strip_tac >>
  gvs[correct_sem_def] >>


  gvs[merge_def] >>

                       
  simp[Once get_prop_def] >>

  Cases_on‘lbl’ >> gvs[] >|[
    (* termin *)
    Cases_on ‘p’ >> gvs[] >>
    gvs[apply_Sem_rule_def] >>
    rgs[Once BDD_pred_sem_cases, from_pred_to_bool_def]>>
    rgs[Sem_rule_def]
    ,
    (* non termin *)
    Cases_on ‘p’ >> gvs[] >>
    gvs[apply_Sem_rule_def] >>
    ‘n''≠ n'’ by cheat >>
    gvs[ALOOKUP_ADELKEY] >>
    
    
    ‘BDD_pred_sem
     (r,ADELKEY n' (merge_edges edges n n'),ADELKEY n' labels) mv n'' b =
     BDD_pred_sem
     (r,edges, labels) mv n'' b’ by cheat >>
    rgs[] >>
    
    first_x_assum (strip_assume_tac o (Q.SPECL [‘n''’,‘mv’,‘b’,‘(non_termn (q,r'))’])) >>
    gvs[] >>
    gvs[get_prop_def] >>
    gvs[apply_Sem_rule_def] 
       
  ]
QED
        
   
        


val _ = export_theory ();

    
