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

Definition Sem_rule_def:
  (Sem_rule (Var x) mv = (ALOOKUP mv x) ) /\
  (Sem_rule True _ = SOME T) /\
  (Sem_rule False _ = SOME F) /\
  (Sem_rule (And p q) mv = 
   case (Sem_rule p mv, Sem_rule q mv)  of
   | (SOME b, SOME b') => SOME (b ∧ b')
   | (_,_) => NONE
  ) /\
  (Sem_rule (Or p q) mv = 
   case (Sem_rule p mv, Sem_rule q mv)  of
   | (SOME b,SOME b') => SOME (b ∨ b')
   | (_,_) => NONE
  ) /\
  (Sem_rule (Not p) mv = 
   case (Sem_rule p mv)  of
   | SOME b => SOME (~b)
   | _ => NONE
  ) /\
  (Sem_rule (Implies p q) mv = 
   case (Sem_rule p mv, Sem_rule q mv)  of
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



   


(* move to other file the specialized *)
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
    sem := Sem_rule;
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


Theorem mem_imp_sem_rule:        
  ∀p mv. (∀x. MEM x (FV p) ⇒ (∃b. ALOOKUP mv x = SOME b)) ⇒
         Sem_rule p mv ≠ NONE ∧ ∃ b' . Sem_rule p mv = SOME b'
Proof
  Induct >>
  rw[simp_pred_def, FV_def] >> gvs[AllCaseEqs()] >>
  gvs[Sem_rule_def, simp_pred_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) 
QED




Theorem simplification_correct:
  ∀p mv. (∀x. MEM x (FV p) ⇒ (∃b. ALOOKUP mv x = SOME b)) ⇒
         Sem_rule p mv = Sem_rule (simp_pred p) mv
Proof
  Induct_on `p` >-
   (rw[simp_pred_def, Sem_rule_def]) >-
   (rw[simp_pred_def, Sem_rule_def]) >-
   (rw[simp_pred_def, Sem_rule_def]) >>

  rpt strip_tac >>
  imp_res_tac mem_imp_sem_rule >>

  LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘mv’])) >>
  gvs[FV_def] >>
  gvs[Sem_rule_def] >>   

  rw[Sem_rule_def, simp_pred_def] >>   
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  gvs[Sem_rule_def, simp_pred_def] >>
  
  first_x_assum (strip_assume_tac o (Q.SPECL [‘s’])) >>
  imp_res_tac simp_pred_imp_mem >>
  gvs[]
QED
           

val _ = export_theory ();

    
