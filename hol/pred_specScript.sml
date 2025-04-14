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
    sem := sem_pred;
    sub := mk_substitute_pred;
    simp := simp_pred;
    final := pred_final;
  |>
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


Theorem mem_imp_sem_pred:        
  ∀p mv. (∀x. MEM x (FV p) ⇒ (∃b. ALOOKUP mv x = SOME b)) ⇒
         sem_pred p mv ≠ NONE ∧ ∃ b' . sem_pred p mv = SOME b'
Proof
  Induct >>
  rw[simp_pred_def, FV_def] >> gvs[AllCaseEqs()] >>
  gvs[sem_pred_def, simp_pred_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) 
QED




Theorem simplification_correct:
  ∀p mv. (∀x. MEM x (FV p) ⇒ (∃b. ALOOKUP mv x = SOME b)) ⇒
         sem_pred p mv = sem_pred (simp_pred p) mv
Proof
  Induct_on `p` >-
   (rw[simp_pred_def, sem_pred_def]) >-
   (rw[simp_pred_def, sem_pred_def]) >-
   (rw[simp_pred_def, sem_pred_def]) >>

  rpt strip_tac >>
  imp_res_tac mem_imp_sem_pred >>

  LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘mv’])) >>
  gvs[FV_def] >>
  gvs[sem_pred_def] >>   

  rw[sem_pred_def, simp_pred_def] >>   
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  gvs[sem_pred_def, simp_pred_def] >>
  
  first_x_assum (strip_assume_tac o (Q.SPECL [‘s’])) >>
  imp_res_tac simp_pred_imp_mem >>
  gvs[]
QED
           

val _ = export_theory ();

    
