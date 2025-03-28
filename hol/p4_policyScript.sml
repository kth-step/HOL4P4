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

   
(*
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


        

val no_children_check_def = Define `
   no_children_check edges leaves = 
   EVERY (\n. ~ MEM n (MAP FST edges)) leaves
`;


   
val getLeaves_def = Define `
   getLeaves [] r = SOME [r] ∧
   getLeaves edges r =
   ( case no_children_check edges (get_leaves_list edges)  of
   | T => SOME (get_leaves_list edges)
   | F => NONE
   )
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
  (ALL_DISTINCT (MAP FST edges)  ∧ ALL_DISTINCT (MAP FST labels) ∧
    (∀ n . is_lookup_defined edges n ⇔ is_lookup_non_leaf labels n ) ∧
    (∀ n . ALOOKUP edges n = NONE  ⇔   (is_lookup_leaf labels n
                                        ∨ ALOOKUP labels n= SOME (termn True)
                                        ∨ ALOOKUP labels n= SOME (termn False))
    ) ∧
   (edges = [] ⇒ ∃ p . labels = [(r,p)])   
  )
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
     (case getLeaves edges r of
      | SOME leaves =>
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
                                         SOME (((r,  edges ++ new_edges, label_leaf_updated++new_labels):BDD),
                                               c + (LENGTH new_labels) 
                                              )             
                           )
                       | NONE => NONE
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
  (mk_BDDPred (BDD:BDD) l [] c = SOME BDD) ∧
  (mk_BDDPred (BDD:BDD) l (x::xs) c =
   case (body_of_mk BDD (x:string) (c:num)) of
   | SOME (BDD',c') => mk_BDDPred BDD' (x::l) xs c'
   | NONE => NONE 
  )
End



        
val body_of_mk_pred_tac =       
( rename1 ‘getLeaves edges r = SOME leaves’ >>
  rename1 ‘getLabels labels leaves = SOME leaves_labels’ >>
  rename1 ‘extract_nontermn leaves_labels = SOME ntl’ >>
  rename1 ‘extract_termn leaves_labels = SOME tl’ >>

  
  ‘∃ leaves_sub . leaves_pred_sub ntl h = leaves_sub’ by gvs[] >>
  ‘∃ simp_leaves . simp_pred_list leaves_sub = simp_leaves’ by gvs[] >>
  ‘∃ simp_leaves' . determine_termn_list simp_leaves = simp_leaves'’ by gvs[] >>
  ‘∃ new_edges . mk_new_edges simp_leaves' c = new_edges’ by gvs[] >>
  ‘∃ new_labels . mk_new_labels simp_leaves' c = new_labels’ by gvs[] >>
  rgs[] );
        

(*
EVAL “mk_BDDPred (0,[],[(0, non_termn (NONE, (Var "a")))]) [] ["a"] 1”;
EVAL “mk_BDDPred (0,[],[(0, non_termn (SOME "a", (Var "a")))]) [] ["a"] 1”;
EVAL “mk_BDDPred (0,[],[(0, non_termn (NONE, (And (Var "a") (Var "b"))))]) [] ["a";"b"] 1”;
EVAL “mk_BDDPred (0,[],[(0, non_termn (NONE, (And (Var "a") (Var "b"))))]) [] ["a";"b"] 1”;
EVAL “mk_BDDPred (0,[],[(0, non_termn (NONE, Or (And (Var "a") (Var "b")) (Var "c")  ))]) [] ["a";"b";"c"] 1”;
EVAL “mk_BDDPred (0,[],[(0, non_termn (NONE, Or (Var "a") (Var "b")))]) [] ["a";"b";"c"] 1”;
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

‘∃ leaves_sub . leaves_pred_sub x'' h = leaves_sub’ by gvs[] >>
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
    


Theorem lookup_labels_in_updt_term:
∀ labels n p h.
ALOOKUP labels n = SOME (termn p) ⇒
ALOOKUP (non_term_leaf_updt labels h) n = SOME (termn p)
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




        
  

Theorem all_distinct_leaves:
∀ edges r leaves .        
ALL_DISTINCT (MAP FST edges) ∧
getLeaves edges r = SOME leaves ⇒
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



(*        
Triviality getLeaves_list_eq:      
∀ l h r .
getLeaves (h::l) r = SOME (get_leaves_list (h::l))
Proof                                        
gvs[getLeaves_def, get_leaves_list_def]
QED
*)



        
Theorem leaves_are_not_parents:         
∀ edges leaves n r.     
  MEM n (MAP FST edges) ∧
  getLeaves edges r = SOME leaves ⇒
  ~ MEM n leaves
Proof
  Cases_on ‘edges’ >>
  rpt strip_tac >-
   gvs[getLeaves_def] >>
  imp_res_tac get_leaves_list_domain >>
  rgs[Once getLeaves_def]          
QED


     



    
Definition range_c_def:
  range_c c ((r,edges,labels):BDD) =
   (
   EVERY (\n. c > n) (MAP FST labels))
End
       

Theorem length_new_labels:
∀ simp_leaves' new_labels c.       
  mk_new_labels simp_leaves' c = new_labels ⇒
  LENGTH new_labels = (LENGTH simp_leaves' + LENGTH simp_leaves')
Proof
Induct >>
gvs[mk_new_labels_def] >>
rpt strip_tac >>
PairCases_on ‘h’ >>
gvs[mk_new_labels_def]
QED
                

Theorem counter_range_in_new_labels:
∀ simp_leaves' new_labels c n .       
MEM n (MAP FST new_labels) ∧                        
mk_new_labels simp_leaves' c = new_labels ⇒
(n >= c ∧ n < (c + LENGTH new_labels)) 
Proof
Induct >>
gvs[mk_new_labels_def] >>
rpt strip_tac >>
PairCases_on ‘h’ >>
gvs[mk_new_labels_def] >>
res_tac >>
decide_tac
QED


(*
EVAL “mk_new_labels [(a,b,c,d);(a,b,c,d);(a,b,c,d)] 2”
*)

        

Theorem counter_range_in_new_exists:
∀ simp_leaves' new_labels c n .       
MEM n (MAP FST new_labels) ∧                        
mk_new_labels simp_leaves' c = new_labels ⇒
(∃ i . n = c + i ∧ i < LENGTH new_labels) 
Proof
Induct >>
gvs[mk_new_labels_def] >>
rpt strip_tac >>
PairCases_on ‘h’ >>
gvs[mk_new_labels_def] >| [
    qexists_tac ‘0’ >> gvs[]
    ,
    res_tac >>
    qexists_tac ‘2+i’ >> gvs[]
  ]
QED

        

Triviality get_labels_empty_labels:        
∀ leaves l. getLabels [] leaves = SOME l ⇒
            (l = [])
Proof
  Induct >>
  rpt strip_tac >>
  gvs[getLabels_def] >>
  gvs[AllCaseEqs()]
QED
        
        
Theorem WFness_range_c_inter:
 ∀ BDD BDD'' c c' h.
range_c c BDD ∧
body_of_mk BDD h c = SOME (BDD'',c') ⇒
range_c c' BDD''
Proof
  rpt strip_tac >>
  PairCases_on ‘BDD’ >>
  rename1 ‘(r,edges,labels)’ >>
          
  gvs[body_of_mk_def] >>
  REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  body_of_mk_pred_tac >>

  rgs[range_c_def] >>
  rpt strip_tac >>
      
  imp_res_tac mk_body_map1 >>
  imp_res_tac mk_body_map2 >>
  imp_res_tac mk_body_map3 >>
  imp_res_tac mk_body_map4 >>
  imp_res_tac mk_body_map5 >>
  ‘∃old_updated .non_term_leaf_updt labels h = old_updated’ by gvs[] >>              
  imp_res_tac mk_body_map6 >>
  
  rgs[EVERY_MEM] >>
  rpt strip_tac >| [
    first_x_assum (strip_assume_tac o (Q.SPECL [‘n’])) >>
    rgs[] >> metis_tac[]
    ,
    
    ‘LENGTH simp_leaves' = LENGTH ntl’ by metis_tac[LENGTH_MAP] >>
    imp_res_tac length_new_labels >>
    ‘LENGTH new_labels = LENGTH ntl + LENGTH ntl’ by gvs[] >>                                             
    imp_res_tac counter_range_in_new_labels >>
    rgs[] >>

    imp_res_tac counter_range_in_new_exists >>
    rgs[] 
  ]
QED



  

Theorem WFness_distinct_edges_labels:
  ∀ BDD r'' edges'' labels'' c c' h.
    range_c c BDD ∧
    BDD_WF BDD ∧
    body_of_mk BDD h c = SOME ((r'',edges'',labels''),c') ⇒
    (ALL_DISTINCT (MAP FST edges'') ∧ ALL_DISTINCT (MAP FST labels''))
Proof
  rpt strip_tac >>
  PairCases_on ‘BDD’ >>
  rename1 ‘(r,edges,labels)’ >>
          
  gvs[body_of_mk_def] >>
  REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  body_of_mk_pred_tac >|[

    ‘ALL_DISTINCT (MAP FST edges)’ by rgs[Once BDD_WF_def] >>
    ‘∃ leaves. getLeaves edges r = leaves’ by gvs[] >>
    
    imp_res_tac all_distinct_leaves >>
    ‘ALL_DISTINCT (MAP FST leaves_labels)’ by (imp_res_tac all_distinct_leaves_labels >> gvs[]) >>
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
    ,
    
    
    ‘ALL_DISTINCT (MAP FST labels)’ by rgs[Once BDD_WF_def] >>
    ‘ALL_DISTINCT (MAP FST (non_term_leaf_updt labels h))’ by (imp_res_tac all_distinct_non_term_leaf_updt >> gvs[]) >>
    
    
    
    
    (* same as before *)
    subgoal ‘ALL_DISTINCT (MAP FST new_labels)’ >- (
      ‘ALL_DISTINCT (MAP FST edges)’ by rgs[Once BDD_WF_def] >>
      ‘∃ leaves. getLeaves edges r = leaves’ by gvs[] >>
      
      imp_res_tac all_distinct_leaves >>
      ‘ALL_DISTINCT (MAP FST leaves_labels)’ by (imp_res_tac all_distinct_leaves_labels >> gvs[]) >>
      imp_res_tac all_distinct_ntl >>       
      imp_res_tac all_distinct_sub >>
      imp_res_tac all_distinct_simp >>
      ‘ALL_DISTINCT (MAP FST simp_leaves')’ by (imp_res_tac all_distinct_determine >> gvs[]) >>        
      ‘ALL_DISTINCT (MAP FST new_edges)’ by (imp_res_tac all_distinct_mk_edges >> gvs[]) >>
      (*end*)
      
      ‘ALL_DISTINCT (MAP FST new_labels)’ by (imp_res_tac all_distinct_mk_labels >> gvs[])
      )>>        
    simp[ALL_DISTINCT_APPEND]>>
    
    strip_tac >> strip_tac >>
    ‘∃ updated_labels . non_term_leaf_updt labels h = updated_labels’ by gvs[] >>          
    imp_res_tac leaves_are_not_parents >>
    (*if in labels changed, then in labels, then from efness in *)
    
    
    
    imp_res_tac mk_body_map1 >>
    imp_res_tac mk_body_map2 >>
    imp_res_tac mk_body_map3 >>
    imp_res_tac mk_body_map4 >>
    imp_res_tac mk_body_map5 >>
    imp_res_tac mk_body_map6 >>
    
    
    ‘MEM e (MAP FST labels)’ by gvs[] >>
    rgs[range_c_def] >>
    imp_res_tac EVERY_MEM >>
    ‘c > e’ by gvs[EVERY_MEM] >>
    imp_res_tac counter_range_in_new_labels >>
    strip_tac >>
    res_tac >>
    DECIDE_TAC
  ]
                        
QED



Triviality alookup_map_local_thm:
∀ l l' n x.
  ALOOKUP l n = SOME x ∧
  MAP FST l = MAP FST l' ⇒
  ∃ x'.  ALOOKUP l' n = SOME x'  
Proof
  Induct >>
  gvs[] >>
  rpt strip_tac >>
  PairCases_on ‘h’ >> gvs[] >>
  gvs[AllCaseEqs()]>>
  Cases_on ‘l'’ >> gvs[] >>
  PairCases_on ‘h’ >> gvs[]
QED


        
Theorem alookup_nonterm_exsists:                          
∀ leaves_labels ntl n p.
ALOOKUP ntl n = SOME p ∧        
extract_nontermn leaves_labels = SOME ntl ⇒
∃ lbl. ALOOKUP leaves_labels n = SOME lbl 
Proof
Induct >>                                        
gvs[extract_nontermn_def] >>
rpt strip_tac >>
PairCases_on ‘h’ >>
gvs[] >>
rpt (BasicProvers.full_case_tac >> gvs[]) >>
gvs[extract_nontermn_def] >>
rpt (BasicProvers.full_case_tac >> gvs[])
QED


Theorem lbl_pred_rel_extract_nontermn:
∀ leaves_labels ntl n p lbl.
 ALL_DISTINCT (MAP FST leaves_labels) ∧
extract_nontermn leaves_labels = SOME ntl ∧
ALOOKUP leaves_labels n = SOME lbl ∧
ALOOKUP ntl n = SOME p ⇒
(lbl = non_termn (NONE,p))
Proof
Induct >>                                        
gvs[extract_nontermn_def] >>
rpt strip_tac >>

PairCases_on ‘h’ >>
gvs[] >>
rpt (BasicProvers.full_case_tac >> gvs[]) >>
gvs[extract_nontermn_def] >>
rpt (BasicProvers.full_case_tac >> gvs[]) >>
res_tac >>
imp_res_tac alookup_nonterm_exsists >>
res_tac >>
gvs[] >>
imp_res_tac ALOOKUP_MEM >>
imp_res_tac mem_fst_snd >>
gvs[]
QED            






Theorem lookup_labels_of_leaves_same:
∀ leaves labels  leaves_labels n lbl.
getLabels labels leaves = SOME leaves_labels ∧
ALOOKUP leaves_labels n = SOME lbl ⇒
ALOOKUP labels n = SOME lbl
Proof
Induct >>
rpt strip_tac >>
gvs[getLabels_def] >>
rpt (BasicProvers.full_case_tac >> gvs[])
QED




Triviality determine_termn_list_cons:
∀ h simp_leaves.        
determine_termn_list (h::simp_leaves) = (determine_termn_list [h]++(determine_termn_list simp_leaves))     
Proof
  gvs[determine_termn_list_def]
QED



Theorem determine_term_never_internal:        
∀p p' x. determine_termn p ≠ non_termn (SOME x,p')
Proof
  rpt strip_tac >>
  gvs[determine_termn_def] >>
  gvs[AllCaseEqs()]
QED




Theorem determine_term_list_never_internal1:
∀ simp_leaves simp_leaves' n.             
determine_termn_list simp_leaves = simp_leaves'  ⇒
(~ ∃ lbl lbl' x x' x'' p p' .
     ALOOKUP simp_leaves' n = SOME (x , lbl, lbl') ∧
     lbl = (non_termn (SOME x',p)) ∧
     lbl' = (non_termn (SOME x'',p')))
Proof
Induct >>
rpt strip_tac >>
 gvs[determine_termn_list_def] >>
imp_res_tac mk_body_map4 >>
PairCases_on ‘h’ >> gvs[] >>
gvs[AllCaseEqs()] >>
imp_res_tac determine_term_never_internal
QED




Theorem determine_term_list_never_internal_r:
∀ simp_leaves simp_leaves' n x lbl lbl'.             
  determine_termn_list simp_leaves = simp_leaves'  ⇒
  ALOOKUP simp_leaves' n = SOME (x , lbl, lbl') ⇒
(~ ∃  x' x'' p p' .
     lbl = (non_termn (SOME x',p)))
Proof
Induct >>
rpt strip_tac >>
 gvs[determine_termn_list_def] >>
imp_res_tac mk_body_map4 >>
PairCases_on ‘h’ >> gvs[] >>
gvs[AllCaseEqs()] >>
imp_res_tac determine_term_never_internal >>
res_tac >>
metis_tac []
QED



Theorem determine_term_list_never_internal_l:
∀ simp_leaves simp_leaves' n x lbl lbl'.             
  determine_termn_list simp_leaves = simp_leaves'  ⇒
  ALOOKUP simp_leaves' n = SOME (x , lbl, lbl') ⇒
(~ ∃  x' x'' p p' .
     lbl' = (non_termn (SOME x'',p')))
Proof
Induct >>
rpt strip_tac >>
 gvs[determine_termn_list_def] >>
imp_res_tac mk_body_map4 >>
PairCases_on ‘h’ >> gvs[] >>
gvs[AllCaseEqs()] >>
imp_res_tac determine_term_never_internal >>
res_tac >>
metis_tac []
QED


        

        
Triviality mk_new_labels_cons_imp:
∀ simp_leaves' h h1 h2 t c.
mk_new_labels (h::simp_leaves') c = h1::h2::t ⇒
mk_new_labels (simp_leaves') (c+2) = t
Proof
  rpt strip_tac >> 
  PairCases_on ‘h’ >> gvs[] >>
  PairCases_on ‘h1’ >> gvs[] >>
  PairCases_on ‘h2’ >> gvs[] >>
  gvs[mk_new_labels_def]
QED

                   


                                                                

        
Theorem mk_new_labels_range_exsists:
  ∀   simp_leaves' new_labels  lbl n c.
    ALL_DISTINCT (MAP FST simp_leaves') ∧
    mk_new_labels simp_leaves' c = new_labels ∧
    ALOOKUP new_labels n = SOME (lbl) ⇒
    (∃ n' x lbl' . (ALOOKUP simp_leaves' n' = SOME (x,lbl,lbl') ∨
                   ALOOKUP simp_leaves' n' = SOME (x,lbl',lbl) ∨
                   ALOOKUP simp_leaves' n' = SOME (x,lbl,lbl))
                   )
Proof
   
  Induct >-
  rgs[mk_new_labels_def] >>
  Induct_on ‘new_labels’ >-
   rgs[mk_new_labels_def] >>
  rpt strip_tac >>

  PairCases_on ‘h’ >> gvs[] >>
  PairCases_on ‘h'’ >> gvs[] >>
  
  gvs[AllCaseEqs()] >| [
    gvs[mk_new_labels_def] >>
    qexistsl_tac [‘h'0’,‘h'1’,‘h'3’] >>
    gvs[]
    ,
    
    Cases_on ‘new_labels’ >> gvs[] >>
    PairCases_on ‘h’ >> rgs[] >>
    gvs[mk_new_labels_def] >>
    gvs[AllCaseEqs()] >|[
        qexistsl_tac [‘h'0’,‘h'1’,‘h'2’] >>
             gvs[]
             ,
             rgs[] >>
             last_x_assum (strip_assume_tac o (Q.SPECL [‘lbl’, ‘n’, ‘c+2’])) >>
             gvs[] >>
             (qexistsl_tac [‘n'’, ‘x’, ‘lbl'’] >>
                  gvs[] >>
                  strip_tac >>
                  imp_res_tac ALOOKUP_MEM >>
                  imp_res_tac mem_triple_map_fst >>
                  gvs[])
      ]
  ]
QED








Theorem new_labels_are_not_internal:      
∀ simp_leaves' (simp_leaves: (num # string # pred # pred)list) new_labels c n.
  ALL_DISTINCT (MAP FST simp_leaves') ∧  
determine_termn_list simp_leaves = simp_leaves' ∧
mk_new_labels simp_leaves' c = new_labels ⇒
~ ∃ x p . ALOOKUP new_labels n = SOME (non_termn (SOME x,p))
Proof
 rpt strip_tac >>

 assume_tac (INST_TYPE [“:'a” |-> “:num” ,
                        “:'b” |-> “:string” ,
                        “:'c” |-> “:label”  ] mk_new_labels_range_exsists)  >>

 first_x_assum (strip_assume_tac o (Q.SPECL [‘simp_leaves'’, ‘new_labels’, ‘(non_termn (SOME x,p))’, ‘n’, ‘c’])) >>
 rgs[] >|[
    
    assume_tac (INST_TYPE [“:'a” |-> “:num” , “:'b” |-> “:string” ] determine_term_list_never_internal_r)  >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘simp_leaves’, ‘simp_leaves'’, ‘n'’])) >>
    rgs[]
    ,
    assume_tac (INST_TYPE [“:'a” |-> “:num” , “:'b” |-> “:string” ] determine_term_list_never_internal_l)  >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘simp_leaves’, ‘simp_leaves'’, ‘n'’])) >>
    rgs[]
    ,
      assume_tac (INST_TYPE [“:'a” |-> “:num” , “:'b” |-> “:string” ] determine_term_list_never_internal_r)  >>
    first_x_assum (strip_assume_tac o (Q.SPECL [‘simp_leaves’, ‘simp_leaves'’, ‘n'’])) >>
    rgs[]
  ]               
QED

        



Theorem lookup_non_term_leaf_updt_internal:        
∀ labels h n x p.
ALOOKUP (non_term_leaf_updt labels h) n = SOME (non_termn (SOME x,p)) ⇒
(( ALOOKUP labels n = SOME (non_termn (NONE,p)) ∧ (x=h)) ∨
  ALOOKUP labels n = SOME (non_termn (SOME x,p) ))
Proof
  Induct >>
  rpt strip_tac >>
  gvs[non_term_leaf_updt_def] >>
  PairCases_on ‘h’ >> gvs[] >>
  rgs[AllCaseEqs()] >>
  gvs[AllCaseEqs()] >>
  rpt(BasicProvers.FULL_CASE_TAC >> gvs[])
QED








Definition get_all_nodes_from_edges_def:
  get_all_nodes_from_edges edges = 
   (FLAT (MAP (λ(k,v1,v2). [k; v1; v2]) edges))
End


Definition get_all_nodes_from_labels_def:
  get_all_nodes_from_labels labels = 
  MAP FST labels
End

          

(*
HERE
BDD_WF (r,edges,labels) ∧
ALOOKUP edges n = NONE ∧
ALOOKUP labels n = SOME (non_termn (NONE,p)) ∧
getLeaves edges r = SOME leaves  ⇒
MEM n leaves

rpt strip_tac >>












          





          
BDD_WF (r,edges,labels) ∧
ALOOKUP edges n = NONE ∧
ALOOKUP labels n = SOME (non_termn (NONE,p)) ∧
getLeaves edges r = SOME leaves ∧
getLabels labels leaves = SOME leaves_labels ⇒
ALOOKUP leaves_labels n = SOME (non_termn (NONE,p))

rpt strip_tac >>
Cases_on ‘edges = []’ >|[
    gvs[BDD_WF_def] >>
    gvs[getLeaves_def, getLabels_def]
    ,
    Cases_on ‘leaves = []’ >> gvs[getLabels_def] >>
    gvs[getLeaves_def] >>
    Cases_on ‘edges’ >> gvs[getLeaves_def] >> gvs[get_leaves_list_def] >>
    PairCases_on ‘h’ >> gvs[] >>
    gvs[AllCaseEqs()]>>
    gvs[BDD_WF_def] >|[
        first_x_assum (strip_assume_tac o (Q.SPECL [‘h0’])) >>
        gvs[is_lookup_leaf_def]
        last_x_assum (strip_assume_tac o (Q.SPECL [‘h0’])) >>
        gvs[is_lookup_defined_def, is_lookup_non_leaf_def]


      ]

  ]

gvs[BDD_WF_def]

cheat











                                          
                        

Theorem WFness_lookup_edges:
∀ r edges labels r'' edges'' labels'' h c c' n.
BDD_WF (r,edges,labels) ∧
body_of_mk (r,edges,labels) h c = SOME ((r'',edges'',labels''),c') ∧
ALL_DISTINCT (MAP FST edges'') ∧
ALL_DISTINCT (MAP FST labels'')
⇒
(is_lookup_defined edges'' n ⇔ is_lookup_non_leaf labels'' n)
Proof
  rpt strip_tac >>
  rgs[is_lookup_defined_def, is_lookup_non_leaf_def] >>                      
  
  EQ_TAC >>
  rpt strip_tac >|[
    (* if it has edges then indeed the label (x,p)*)
    
    gvs[body_of_mk_def] >>
    gvs[AllCaseEqs()]>>
    body_of_mk_pred_tac >>
    rgs[ALOOKUP_APPEND] >>
    rgs[AllCaseEqs()] >| [
      (*if in the newly created layer edges *)
      PairCases_on ‘y’ >> rgs[] >>
      Cases_on ‘ALOOKUP (non_term_leaf_updt labels h) n’ >>
      REPEAT (BasicProvers.FULL_CASE_TAC >> rgs[]) >> rgs[] >|[
        (* this is false *)
        rgs[BDD_WF_def] >>
        rgs[is_lookup_leaf_def] >>
        imp_res_tac lookup_ntl_updt_none >>  
        gvs[]
        ,
        rgs[BDD_WF_def] >-
         (rgs[is_lookup_leaf_def]>>
          imp_res_tac lookup_labels_in_updt_none >>
          first_x_assum (strip_assume_tac o (Q.SPECL [‘h’])) >>
          rgs[]                 
         ) >>
        (* case terminal, we do not pick it up really, so it shouldn't satisfy the result,
           we should show this subgoal by proving that in new_edges when looking up for n, then teh result should be none.
         *)
        (* we should show that n it is in leaves_labels , but not in ntl *)
        (
        rgs[is_lookup_non_leaf_def, is_lookup_defined_def] >>
        ‘ALOOKUP edges n = NONE’ by res_tac >>
        
        imp_res_tac lookup_labels_in_updt_term >>
        first_x_assum (strip_assume_tac o (Q.SPECL [‘h’])) >>
        rgs[] >>
        
        (* since n in new edges, then indeed it was in ntl*)
        subgoal ‘ ∃ p . ALOOKUP ntl n = SOME p’ >-
         (
         imp_res_tac mk_body_map1 >>
         imp_res_tac mk_body_map2 >>
         imp_res_tac mk_body_map3 >>
         imp_res_tac mk_body_map4 >>
         imp_res_tac mk_body_map5 >>
         rgs[] >>
         
         assume_tac (INST_TYPE [“:'a” |-> “:num” , “:'b” |-> “:(num#num)” , “:'c” |-> “:pred” ] alookup_map_local_thm)  >>
         first_x_assum (strip_assume_tac o (Q.SPECL [‘new_edges’,‘ntl’,‘n’,‘(y0,y1)’])) >>
         gvs[]
         ) >>
        
        ‘∃ lbl . ALOOKUP leaves_labels n = SOME lbl’ by (imp_res_tac alookup_nonterm_exsists >> gvs[]) >>
        imp_res_tac mk_body_map2 >>
        ‘ALL_DISTINCT (MAP FST leaves_labels)’ by cheat >>
        ‘lbl = non_termn (NONE,p)’ by imp_res_tac lbl_pred_rel_extract_nontermn >>
        rgs[] >>
        
        imp_res_tac mk_body_map1 >>
        rgs[] >>
        ‘ALOOKUP labels n = SOME (non_termn (NONE,p))’ by imp_res_tac lookup_labels_of_leaves_same >>
        gvs[]
        ) 
      ]
            
      ,
      (*if in the old edges *)
      PairCases_on ‘y’ >> rgs[] >>
      Cases_on ‘ALOOKUP (non_term_leaf_updt labels h) n’ >>
      REPEAT (BasicProvers.FULL_CASE_TAC >> rgs[]) >> rgs[] >|[
          (* This is imposisble *)
          rgs[BDD_WF_def] >>
          rgs[is_lookup_defined_def, is_lookup_non_leaf_def] >>
          ‘∃ x p . ALOOKUP labels n = SOME (non_termn (SOME x,p))’ by (res_tac >> gvs[]) >>
          imp_res_tac lookup_ntl_updt_none >>  
          gvs[]
          ,
          imp_res_tac wf_lookup_if_edges_label >>
          imp_res_tac WF_imp_non_leaf_lbl >>
          rgs[] >>
          first_x_assum (strip_assume_tac o (Q.SPECL [‘h’])) >>
          rgs[]
             
        ]                                                
    ]
                         
    ,
    (* second part of implication *)
    
    gvs[body_of_mk_def] >>
    gvs[AllCaseEqs()]>>
    body_of_mk_pred_tac >>
    rgs[ALOOKUP_APPEND] >>
    rgs[AllCaseEqs()] >| [
        (* n here is in teh newly created labels and edges, basically from c *)     
        imp_res_tac new_labels_are_not_internal >>
        ‘ALL_DISTINCT (MAP FST simp_leaves')’ by cheat >>            
        gvs[]
        ,

        Cases_on ‘ALOOKUP edges n’ >> rgs[] >>
        imp_res_tac lookup_non_term_leaf_updt_internal >|[
            rgs[] >>

            rgs[BDD_WF_def] >>
            rgs[is_lookup_leaf_def]
                  
                  
            subgoal  ‘∃ lbl. ALOOKUP simp_leaves' n = lbl’ >-
             (
                      imp_res_tac mk_body_map1 >>
         imp_res_tac mk_body_map2 >>
         imp_res_tac mk_body_map3 >>
         imp_res_tac mk_body_map4 >>
         imp_res_tac mk_body_map5 >>
         rgs[] >>
             )
            


                    
            ,
            rgs[BDD_WF_def] >>
            gvs[is_lookup_leaf_def]
          ]
       
              

      ]

]
QED                



*)


Theorem wf_edges_root_mkbody:
∀ r edges labels r'' edges'' labels'' c c' h.       
BDD_WF (r,edges,labels) ∧
body_of_mk (r,edges,labels) h c = SOME ((r'',edges'',labels''),c') ∧
edges'' = [] ⇒
∃p. labels'' = [(r'',p)]
Proof
rpt strip_tac >>        
gvs[body_of_mk_def] >>
rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
gvs[BDD_WF_def] >>
gvs[getLeaves_def, getLabels_def] >>
Cases_on ‘p’ >>
gvs[non_term_leaf_updt_def] >>
gvs[is_lookup_leaf_def,is_lookup_defined_def,is_lookup_non_leaf_def] >>
gvs[extract_nontermn_def, extract_termn_def] >>
Cases_on ‘p'’ >> 
gvs[leaves_pred_sub_def,simp_pred_list_def] >>
gvs[determine_termn_list_def,mk_new_labels_def, mk_new_edges_def] 
QED




                                                          
      
        
Theorem WFness_translation_inter:
  ∀ BDD BDD'' c c' h.
    range_c c BDD ∧
    BDD_WF BDD  ∧
    body_of_mk BDD h c = SOME (BDD'',c') ⇒
    BDD_WF BDD''
Proof
  rpt strip_tac >>

  PairCases_on ‘BDD’ >>
  rename1 ‘(r,edges,labels)’ >>
  
  PairCases_on ‘BDD''’ >>
  rename1 ‘(r'',edges'',labels'')’ >>

  imp_res_tac WFness_distinct_edges_labels >>
              
(*  imp_res_tac WFness_range_c_inter >>
*)  
  simp[BDD_WF_def] >> CONJ_TAC >> rpt strip_tac >|[
    cheat
    ,
    cheat
    ,
    metis_tac[wf_edges_root_mkbody]
    
  ]

QED













                                   
        
Theorem WFness_translation:
  ∀ vars vars_consumed BDD BDD' c.
    (*BDD_ordered BDD vars_consumed ∧*)
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
    REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>           
    PairCases_on ‘q’ >>
    ‘BDD_WF (q0,q1,q2)’ by cheat >> (* this should be for intermidate, lemma above*)
    res_tac
]
           
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
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
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
    gvs[is_lookup_leaf_def]
    ) >>
    
  gvs[] >>
  
  simp[Once BDD_pred_sem_cases] >>
  gvs[] >>
  gvs[ALOOKUP_ADELKEY]        
QED



Triviality merge_edges_same:
∀ edges n n.        
merge_edges edges n n = edges
Proof
Induct >>
rpt strip_tac>>
gvs[merge_edges_def]>>
PairCases_on ‘h’ >> rgs[]>>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[])
QED


Triviality merge_edges_list_cons:        
∀ edges h n n'.
merge_edges (h::edges) n n' = (merge_edges [h] n n')++(merge_edges (edges) n n')
Proof
rpt strip_tac>>
gvs[Once merge_edges_def] >>
PairCases_on ‘h’ >> gvs[merge_edges_def]
QED



Triviality merge_edges_res_sing:
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


           
Triviality alookup_defined_append1:
∀ l l' n a b.
ALOOKUP (l ++ l') n = SOME (a,b) ⇒
ALOOKUP l n = NONE ⇒
∃ a' b' . ALOOKUP l' n = SOME (a',b') ∧ a' = a ∧  b' = b 
Proof
gvs[ALOOKUP_APPEND] >>
rpt strip_tac >>
fs[AllCaseEqs()]
QED


Triviality alookup_defined_append2:
∀ l l' n a b a' b'.
ALOOKUP (l ++ l') n = SOME (a,b) ∧
ALOOKUP l n = SOME (a',b') ⇒
 a' = a ∧  b' = b 
Proof
gvs[ALOOKUP_APPEND] >>
rpt strip_tac >>
fs[AllCaseEqs()]
QED


        
Triviality merge_triviality1:
(ALOOKUP (merge_edges [(h0,h1,h2)] n n') n'' = NONE ⇒
 h0 ≠ n'') ∧
(ALOOKUP (merge_edges [(h0,h1,h2)] n n') n'' = SOME x ⇒
h0 = n'')
Proof
gvs[merge_edges_def]
QED

        
Triviality alookup_triviality1:
  ALOOKUP ((h0,h1,h2)::edges) n'' = SOME (nr,nl) ∧
  h0 = n'' ⇒
  (nr = h1 ∧ nl = h2)
Proof
  rpt strip_tac >>
fs[AllCaseEqs()]
QED
     

Triviality lookup_merge_uni_bs:
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
      
      imp_res_tac merge_triviality1 >>
      
      qpat_x_assum ‘ALOOKUP (h::edges) n'' = SOME (nr,nl)’ (fn thm => assume_tac (SIMP_RULE (srw_ss()) [Once ALOOKUP_def] thm)) >>
      
      ‘ALOOKUP edges n'' = SOME (nr,nl)’ by  rgs[] >>
      metis_tac[]
      ,
      
      PairCases_on ‘h’ >>
      imp_res_tac merge_triviality1 >>
      PairCases_on ‘x’ >>
      ‘x0 = nr'’ by (imp_res_tac alookup_defined_append2 >> metis_tac []) >>
      ‘x1 = nl'’ by (imp_res_tac alookup_defined_append2 >> metis_tac []) >>
      
      subgoal ‘ (nr = h1 ∧ nl = h2)’  >-           
       (imp_res_tac alookup_triviality1 >>
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
gvs[is_lookup_defined_def, is_lookup_non_leaf_def] >>
 res_tac >> gvs[]) >|[

gvs[BDD_ordered_def] >>
first_x_assum (strip_assume_tac o (Q.SPECL [‘n’, ‘n’, ‘nl’])) >>
gvs[] >>
first_x_assum (strip_assume_tac o (Q.SPECL [‘x’, ‘x’, ‘x’])) >>
gvs[] >>
first_x_assum (strip_assume_tac o (Q.SPECL [‘p’, ‘p’, ‘p’])) >>
gvs[] >>

gvs[consumed_dom_bdd_def] >>
imp_res_tac MEM_INDEX_OF >>
first_x_assum (strip_assume_tac o (Q.SPECL [‘i’, ‘i’, ‘i’])) >>
gvs[]
,
       
gvs[BDD_ordered_def] >>
first_x_assum (strip_assume_tac o (Q.SPECL [‘n’, ‘nr’, ‘n’])) >>
gvs[] >>
first_x_assum (strip_assume_tac o (Q.SPECL [‘x’, ‘x’, ‘x’])) >>
gvs[] >>
first_x_assum (strip_assume_tac o (Q.SPECL [‘p’, ‘p’, ‘p’])) >>
gvs[] >>

gvs[consumed_dom_bdd_def] >>
imp_res_tac MEM_INDEX_OF >>
first_x_assum (strip_assume_tac o (Q.SPECL [‘i’, ‘i’, ‘i’])) >>
gvs[] 
]
QED


Triviality merge_replaces_stays_same_singular:
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
    imp_res_tac merge_triviality1 >>
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
      imp_res_tac merge_triviality1 >>
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
  BDD_pred_sem
  (r,ADELKEY n' (merge_edges edges n n'),ADELKEY n' labels) mv n'' b)
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
             gvs[is_lookup_defined_def, is_lookup_non_leaf_def] >>
             res_tac >>
             srw_tac [SatisfySimps.SATISFY_ss][]
             ) >>
            
            
            
            gvs[] >>
            
            
            subgoal ‘THE (INDEX_OF x' vars_consumed) < THE (INDEX_OF x vars_consumed)’ >-(
              rgs[Once BDD_ordered_def] >>
              first_x_assum (strip_assume_tac o (Q.SPECL [‘n''’,‘nr’,‘nl’,‘x’,‘x'’,‘x''’, ‘pred’, ‘pred'’, ‘pred'’])) >>
              gvs[] >>
              
              gvs[consumed_dom_bdd_def] >>
              imp_res_tac MEM_INDEX_OF >>
              res_tac>>
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
                               first_x_assum (strip_assume_tac o (Q.SPECL [‘n''’,‘n'’,‘nl’,‘x’,‘x'’,‘x''’, ‘pred’, ‘r'’, ‘pred'’])) >>
                               gvs[] >>
                               
                               gvs[consumed_dom_bdd_def] >>
                               imp_res_tac MEM_INDEX_OF >>
                               res_tac>>
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
     gvs[is_lookup_defined_def, is_lookup_non_leaf_def] >>
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

    
