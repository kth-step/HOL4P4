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
     
val _ = new_theory "pred_spec";


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

Definition sem_pred_def:
  (sem_pred (Var x) mv = (ALOOKUP mv x) ) /\
  (sem_pred True _ = SOME T) /\
  (sem_pred False _ = SOME F) /\
  (sem_pred (And p q) mv = 
   case (sem_pred p mv, sem_pred q mv)  of
   | (SOME b, SOME b') => SOME (b ∧ b')
   | (_,_) => NONE
  ) /\
  (sem_pred (Or p q) mv = 
   case (sem_pred p mv, sem_pred q mv)  of
   | (SOME b,SOME b') => SOME (b ∨ b')
   | (_,_) => NONE
  ) /\
  (sem_pred (Not p) mv = 
   case (sem_pred p mv)  of
   | SOME b => SOME (~b)
   | _ => NONE
  ) /\
  (sem_pred (Implies p q) mv = 
   case (sem_pred p mv, sem_pred q mv)  of
   | (SOME b,SOME b') => SOME (b ⇒ b')
   | (_,_) => NONE
  ) 
End


(* predicates substitute *)
Definition mk_substitute_pred_def:
  (mk_substitute_pred (True) x b = True) ∧
  (mk_substitute_pred (False) x b = False) ∧
  (mk_substitute_pred (Var x') x b = 
   if (x=x') then (if b then True else False) else (Var x')) ∧
  (mk_substitute_pred (And c c' ) x b =
   (And (mk_substitute_pred c x b) (mk_substitute_pred c' x b ))) ∧
  (mk_substitute_pred (Or c c') x b =
   (Or (mk_substitute_pred c x b) (mk_substitute_pred c' x b ))) ∧
  (mk_substitute_pred (Not c) x b=
   (Not (mk_substitute_pred c x b))) ∧
  (mk_substitute_pred (Implies c c') x b =
   (Implies (mk_substitute_pred c x b) (mk_substitute_pred c' x b )))
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



   


Definition final_pred_def:
  final_pred p = 
  case p of
  | True => SOME T
  | False => SOME F
  | _ => NONE
End



Definition fv_pred_def:
  fv_pred (Var x) = [x] ∧
  fv_pred True = [] ∧
  fv_pred False = [] ∧
  fv_pred (And p q) = nub (fv_pred p ++ fv_pred q) ∧
  fv_pred (Or p q) = nub (fv_pred p ++ fv_pred q) ∧
  fv_pred (Not p) = fv_pred p ∧
  fv_pred (Implies p q) = nub (fv_pred p ++ fv_pred q)
End

        
                                                         
Definition pred_structure_def:
  pred_structure =
  <|
    sem := sem_pred;
    sub := mk_substitute_pred;
    simp := simp_pred;
    final := final_pred;
    fv := fv_pred;
  |>
End            

               
(*
     EVAL “mk_BDDPred pred_structure (0,[],[(0, non_termn (NONE, (Or (Var "a") (Not (Var "a")))))]) [] ["a"] 1”;
     EVAL “mk_BDDPred pred_structure (0,[],[(0, non_termn (NONE, True))]) [] ["a"] 1”;
*)

        
Theorem simp_pred_imp_mem:          
  ∀ p x .
    simp_pred p = Var x ⇒
    MEM x (fv_pred p)
Proof
  Induct >>
  rw[simp_pred_def, fv_pred_def] >> gvs[AllCaseEqs()]
QED



        
Theorem mem_imp_sem_pred:        
  ∀p mv. (∀x. MEM x (fv_pred p) ⇒ (∃b. ALOOKUP mv x = SOME b)) ⇒
         sem_pred p mv ≠ NONE ∧ ∃ b' . sem_pred p mv = SOME b'
Proof
  Induct >>
  rw[simp_pred_def, fv_pred_def] >> gvs[AllCaseEqs()] >>
  gvs[sem_pred_def, simp_pred_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) 
QED




Theorem simplification_correct:
  ∀p mv. (∀x. MEM x (fv_pred p) ⇒ (∃b. ALOOKUP mv x = SOME b)) ⇒
         sem_pred p mv = sem_pred (simp_pred p) mv
Proof
  Induct_on `p` >-
   (rw[simp_pred_def, sem_pred_def]) >-
   (rw[simp_pred_def, sem_pred_def]) >-
   (rw[simp_pred_def, sem_pred_def]) >>
  
  rpt strip_tac >>
  imp_res_tac mem_imp_sem_pred >>
  
  LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘mv’])) >>
  gvs[fv_pred_def] >>
  gvs[sem_pred_def] >>   

  rw[sem_pred_def, simp_pred_def] >>   
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  gvs[sem_pred_def, simp_pred_def] >>
  
  first_x_assum (strip_assume_tac o (Q.SPECL [‘s’])) >>
  imp_res_tac simp_pred_imp_mem >>
  gvs[]
QED



Theorem fv_in_sub_indeed_in_p:   
  ∀ p h b s.
    MEM s (fv_pred (mk_substitute_pred p h b)) ⇒
    MEM s (fv_pred p)
Proof
  Induct_on ‘p’ >>
  (* T, F and Var cases *)
  gvs[fv_pred_def, mk_substitute_pred_def] >>
  rpt strip_tac >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  gvs[fv_pred_def] >>
  
  (* rest of cases *)
  rpt strip_tac >>
  gvs[mk_substitute_pred_def] >>
  Cases_on ‘p’ >>
  gvs[mk_substitute_pred_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  gvs[fv_pred_def] >>
  gvs[mk_substitute_pred_def] >>
  res_tac >>
  gvs[]
QED
        

        


Theorem pred_fv_mem_decomposition:        
  ∀ p p' mv.
    ((∀x. MEM x (fv_pred (And p p')) ⇒ ∃b. ALOOKUP mv x = SOME b) ∨
     (∀x. MEM x (fv_pred (Or p p')) ⇒ ∃b. ALOOKUP mv x = SOME b) ∨
     (∀x. MEM x (fv_pred (Implies p p')) ⇒ ∃b. ALOOKUP mv x = SOME b))⇒
    ((∀x. MEM x (fv_pred p) ⇒ ∃b'. ALOOKUP mv x = SOME b') ∧
     (∀x. MEM x (fv_pred p') ⇒ ∃b''. ALOOKUP mv x = SOME b'')) 
Proof
  rpt strip_tac >>
  gvs[fv_pred_def]
QED




Theorem pred_not_fv_mem_decomposition:        
  ∀ p p' mv.
    (∀x. MEM x (fv_pred (Not p)) ⇒ ∃b. ALOOKUP mv x = SOME b )⇒
    (∀x. MEM x (fv_pred p) ⇒ ∃b'. ALOOKUP mv x = SOME b') 
Proof
  rpt strip_tac >>
  gvs[fv_pred_def]
QED

        


Theorem sem_pred_subst_congruence:
  ∀ mv p p' x x' b h.
    ALOOKUP mv h = SOME b ∧
    sem_pred p mv = SOME x ∧
    sem_pred p' mv = SOME x' ∧        
    sem_pred (simp_pred (mk_substitute_pred p' h b)) mv = sem_pred p' mv ∧
    sem_pred (simp_pred (mk_substitute_pred p h b)) mv = sem_pred p mv ⇒
    (sem_pred (simp_pred (mk_substitute_pred (And p p') h b)) mv = SOME (x ∧ x') ∧
     sem_pred (simp_pred (mk_substitute_pred (Or p p') h b)) mv = SOME (x ∨ x') ∧
     sem_pred (simp_pred (mk_substitute_pred (Implies p p') h b)) mv = SOME (x ⇒ x') ∧
     sem_pred (simp_pred (mk_substitute_pred (Not p) h b)) mv = SOME (~x)
    )
Proof
  rpt strip_tac >>
  gvs[mk_substitute_pred_def] >>
  gvs[simp_pred_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  gvs[sem_pred_def]
QED



Theorem sem_pred_not_subst_congruence:
  ∀ mv p p' x x' b h.
    ALOOKUP mv h = SOME b ∧
    sem_pred p mv = SOME x ∧  
    sem_pred (simp_pred (mk_substitute_pred p h b)) mv = sem_pred p mv ⇒
    (sem_pred (simp_pred (mk_substitute_pred (Not p) h b)) mv = SOME (~x))
Proof
  rpt strip_tac >>
  gvs[mk_substitute_pred_def] >>
  gvs[simp_pred_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  gvs[sem_pred_def]
QED

       

Theorem prop1_pred:
  prop1 pred_structure
Proof
  gvs[prop1_def] >>
  gvs[fv_in_p_def, pred_structure_def] >>
  Induct_on ‘p’ >>
  rpt strip_tac >>~-([‘sem_pred (Var s) mv’],
                     (gvs[mk_substitute_pred_def] >>
                      Cases_on ‘h=s’ >> 
                      gvs[simp_pred_def, sem_pred_def] >>
                      Cases_on ‘b’ >> gvs[simp_pred_def, sem_pred_def])
                    ) >>~- ([‘sem_pred True mv’],
                            gvs[mk_substitute_pred_def] >>
                            gvs[simp_pred_def]
                           ) >>~- ([‘sem_pred False mv’],
                                   gvs[mk_substitute_pred_def] >>
                                   gvs[simp_pred_def]
                                  ) >>
  
  
  simp[sem_pred_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  imp_res_tac mem_imp_sem_pred >>
  rgs[sem_pred_def] >>
  gvs[] >>
  
  imp_res_tac pred_fv_mem_decomposition >>
  imp_res_tac pred_not_fv_mem_decomposition >>
  
  res_tac >>
  gvs[sem_pred_subst_congruence, sem_pred_not_subst_congruence]
QED



                
Theorem final_pred_imp_sem:           
  ∀ p q mv.
    final_pred p = SOME q ⇒
    sem_pred p mv = SOME q
Proof
Induct >>
rpt strip_tac >>
rgs[final_pred_def] >>
rgs[sem_pred_def]
QED
        

       
Theorem prop2_pred:
  prop2 pred_structure
Proof 
  gvs[prop2_def] >>
  gvs[fv_in_p_def, pred_structure_def] >>
  Induct_on ‘p’ >>
  rpt strip_tac >>

  imp_res_tac final_pred_imp_sem >>
  first_x_assum (strip_assume_tac o (Q.SPECL [‘mv’])) >>
  assume_tac prop1_pred >>
  rgs[prop1_def, fv_in_p_def, pred_structure_def]
QED

          
         
Theorem prop3_pred:
  prop3 pred_structure
Proof
gvs[prop3_def, pred_structure_def, fv_in_p_def] >>
rpt strip_tac >>
gvs[final_pred_imp_sem]
QED




Theorem pred_fv_vars_mem_decomposition:        
  ∀ p p' mv varslist.
    ((∀x. MEM x (fv_pred (And p p')) ⇒ MEM x varslist) ∨
     (∀x. MEM x (fv_pred (Or p p')) ⇒ MEM x varslist) ∨
     (∀x. MEM x (fv_pred (Implies p p')) ⇒ MEM x varslist))⇒
    ((∀x. MEM x (fv_pred p) ⇒ MEM x varslist) ∧
     (∀x. MEM x (fv_pred p') ⇒ MEM x varslist)) 
Proof
  rpt strip_tac >>
  gvs[fv_pred_def]
QED




Theorem pred_not_fv_vars_mem_decomposition:        
  ∀ p p' mv varslist.
    (∀x. MEM x (fv_pred (Not p)) ⇒ MEM x varslist )⇒
    (∀x. MEM x (fv_pred p) ⇒ MEM x varslist) 
Proof
  rpt strip_tac >>
  gvs[fv_pred_def]
QED
            



Theorem fv_subst_simp_distributes_over_connectives:             
  ∀ x p p' b h.
    (MEM x (fv_pred (simp_pred (mk_substitute_pred (And p p') h b))) ⇒
     MEM x (fv_pred (simp_pred (mk_substitute_pred p h b))) ∨
     MEM x (fv_pred (simp_pred (mk_substitute_pred p' h b))))
    ∧
    (MEM x (fv_pred (simp_pred (mk_substitute_pred (Or p p') h b))) ⇒
     MEM x (fv_pred (simp_pred (mk_substitute_pred p h b))) ∨
     MEM x (fv_pred (simp_pred (mk_substitute_pred p' h b))))
    ∧
    (MEM x (fv_pred (simp_pred (mk_substitute_pred (Implies p p') h b))) ⇒
     MEM x (fv_pred (simp_pred (mk_substitute_pred p h b))) ∨
     MEM x (fv_pred (simp_pred (mk_substitute_pred p' h b))))
    ∧
    (MEM x (fv_pred (simp_pred (mk_substitute_pred (Not p) h b))) ⇒
     MEM x (fv_pred (simp_pred (mk_substitute_pred p h b))))
Proof
  rpt strip_tac >>
  gvs[mk_substitute_pred_def] >>
  gvs[simp_pred_def, fv_pred_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  gvs[fv_pred_def]
QED


 
            

Theorem prop4_pred:
  prop4 pred_structure
Proof
  rgs[prop4_def, pred_structure_def, fv_in_vars_def] >>
  Induct_on ‘prop_parent’ >>
  rpt strip_tac >-
   (gvs[mk_substitute_pred_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
    gvs[simp_pred_def, fv_pred_def]) >-
   gvs[mk_substitute_pred_def,simp_pred_def, fv_pred_def] >-
   gvs[mk_substitute_pred_def,simp_pred_def, fv_pred_def] >>
  
  imp_res_tac pred_fv_vars_mem_decomposition >>
  imp_res_tac pred_not_fv_vars_mem_decomposition >>
  res_tac >>
  imp_res_tac fv_subst_simp_distributes_over_connectives >>
  res_tac
QED



        

val _ = export_theory ();

    
