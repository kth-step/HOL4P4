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
open pred_specTheory;     
open policy_specTheory;     
     


val _ = new_theory "tables_spec";


(* atomic variable based predicates predicates*)
val _ = Hol_datatype `
     atom_var = True
               | False 
               | Var of string
               | Not of atom_var`;

val _ = Hol_datatype `action_expr = action of 'a | state of num`;


Type line = “:(atom_var list # num # 'a action_expr)”;
Type table = “: ('a line) list”
Type table_list = “: ('a table) list”
   



(***************************************************)
(* some work for the variable based atoms          *)
(***************************************************)



Definition sem_atom_def:
  (sem_atom ((Var x): atom_var) mv = (ALOOKUP mv x) ) /\
  (sem_atom True _ = SOME T) /\
  (sem_atom False _ = SOME F) /\
  (sem_atom (Not p) mv = 
   case (sem_atom p mv)  of
   | SOME b => SOME (~b)
   | _ => NONE
  ) 
End


Definition mk_substitute_atom_def:
  (mk_substitute_atom ((True):atom_var) x b = True) ∧
  (mk_substitute_atom (False) x b = False) ∧
  (mk_substitute_atom (Var x') x b = 
   if (x=x') then (if b then True else False) else (Var x')) ∧
  (mk_substitute_atom (Not c) x b= (Not (mk_substitute_atom c x b))) 
End

   
Definition simp_atom_def:
  (simp_atom ((Var x):atom_var) = Var x) /\
  (simp_atom True = True) /\
  (simp_atom False = False) /\
  (simp_atom (Not p) =
   let p' = simp_atom p in
     case p' of
     | True => False
     | False => True
     | _ => Not p')
End


Definition final_atom_def:
  final_atom (p:atom_var) = 
  case p of
  | True => SOME T
  | False => SOME F
  | _ => NONE
End


Definition fv_atom_def:
  fv_atom (Var x) = [x] ∧
  fv_atom True = [] ∧
  fv_atom False = [] ∧
  fv_atom (Not p) = fv_pred p
End

        
Definition fv_atom_def:
  fv_atom (Var x) = [x] ∧
  fv_atom True = [] ∧
  fv_atom False = [] ∧
  fv_atom (Not p) = fv_atom p 
End
                        
                
(***************************************************)
(* specialized definitions for a predicate record. *)
(*   here 'a would be policy and 'b would be       *) 
(*          action wrt record data type            *)
(***************************************************)

           

(* Check if all predicates in list evaluate to true *)
Definition is_atoml_true_def:
  is_atoml_true atoml mv = 
  EVERY (\minipred. sem_atom minipred mv = SOME T) atoml
End

        
(* Check if row matches current state and guard conditions *)
Definition is_match_row_def:
  is_match_row st_in st_num atoml mv = 
    ((st_in = st_num) ∧ is_atoml_true atoml mv ∧ atoml ≠ [])
End


Definition check_all_rows_match_def:
  check_all_rows_match st_in tbl mv =
  MAP (\(atoml,st_num,res). (is_match_row st_in st_num atoml mv, res)) tbl
End



(* Find first matching line in a single table *)
Definition match_tbl_def:
  match_tbl (tbl: 'a table) mv st_in =
  let lines_res = (check_all_rows_match st_in tbl mv) in
    case min_idx_till lines_res T of
    | SOME (idx, line) => SOME (SND line)
    | NONE => NONE
End

        
        
(* Process table list with state propagation *) 
Definition match_tbll_def:
  match_tbll ([]: 'a table_list) mv st_in = NONE ∧
  match_tbll [tbl] mv st_in =
  ( case match_tbl tbl mv st_in of
    | SOME (action a) => SOME (action a)
    | _ => NONE       
  )∧
  match_tbll (tbl::tbls) mv st_in =
  ( case match_tbl tbl mv st_in of
    | SOME (state n) => match_tbll tbls mv n
    | _ => NONE
  )
End

 
(* Top-level table semantics *)       
Definition sem_tbll_def:
  sem_tbll (tbll: 'a table_list) mv =
   match_tbll tbll mv 0
End




      
(* table substitute *)
                          
Definition mk_substitute_row_def:
  mk_substitute_row atoml x b =
    MAP (\atom. mk_substitute_atom atom x b) atoml
End
   
Definition mk_substitute_tbl_def:
  mk_substitute_tbl (tbl: 'a table) x b =
  ((MAP (\(atoml,st_num,res). (mk_substitute_row atoml x b, st_num, res)) tbl) :'a table)
End

   
Definition mk_substitute_tbll_def:
  mk_substitute_tbll (tbll: 'a table_list) x b =
  MAP (\(tbl). mk_substitute_tbl (tbl: 'a table) x b) tbll 
End



        
(* table simplifications *)

Definition simp_row_def:
  simp_row atoml =
  MAP (\atom. simp_atom atom) atoml
End


Definition simp_tbl_def:
  simp_tbl (tbl: 'a table) =
  MAP (\(atoml,st_num,res). simp_row atoml,st_num,res) tbl
End


Definition simp_tbll_def:
  simp_tbll (tbll: 'a table_list) =
  MAP (\tbl. simp_tbl tbl) tbll
End




(* table final *)

Definition all_true_def:
  all_true atoml =
  EVERY (\atom. atom = True) atoml
End

       
Definition is_hit_def:
  is_hit st_in st_num atoml = 
    ((st_in = st_num) ∧ all_true atoml ∧ atoml ≠ [])
End


Definition is_hit_tbl_check_def:
  is_hit_tbl_check (tbl: 'a table) st_in =
  MAP (\(atoml, st_num, res). is_hit st_in st_num atoml, st_num, res) tbl
End



Definition pre_lines_are_fail_def:
  pre_lines_are_fail (tbl: 'a table) idx =
  EVERY (\(atoml, st_num, res). ~ all_true atoml) (SEG idx 0 tbl)
End

        
Definition final_tbl_def:
  final_tbl (tbl: 'a table) st_in =
  let lines_res = is_hit_tbl_check tbl st_in in
    case min_idx_till lines_res T of
    | SOME (idx, b, st_num, res) =>
        ( case pre_lines_are_fail tbl idx of
          | T => SOME res
          | F => NONE
        )
    | _ => NONE
End
 
        
Definition final_tbll_def:
  final_tbll ([]: 'a table_list) st_in = NONE ∧
  final_tbll [tbl] st_in =
  ( case final_tbl tbl st_in of
    | SOME (action a) => SOME (action a)
    | _ => NONE       
  )∧
  final_tbll (tbl::tbls) st_in =
  ( case final_tbl tbl st_in of
    | SOME (state n) => final_tbll tbls n
    | _ => NONE
  )
End




        
Definition final_tbll_ete_def:
  final_tbll_ete tbll =
  final_tbll tbll 0
End

        


(*  free variables tables *)

        
Definition fv_row_def:
  fv_row atoml =
  let fv_in_row = MAP (\atom. fv_atom atom) atoml in
    nub(FLAT fv_in_row)
End



Definition fv_tbl_def:
  fv_tbl (tbl: 'a table) =
  let fv_in_tbl = MAP (\(atoml, st_num, res). fv_row atoml) tbl in
    nub(FLAT fv_in_tbl)
End

        

    
Definition fv_tbll_def:
  fv_tbll (tbll: 'a table_list) =
  let fv_in_tbll = MAP (\tbl. fv_tbl tbl) tbll in
    nub(FLAT fv_in_tbll)
End

                                                                 
Definition table_structure_def:
  table_structure =
  <|
    sem := sem_tbll;
    sub := mk_substitute_tbll;
    simp := simp_tbll;
    final := final_tbll_ete;
    fv := fv_tbll;
  |>
End            

               

Theorem fv_mem_table_thm:
  ∀ h p mv.
    (∀x. MEM x (fv_tbll (h::p)) ⇒ ∃b. ALOOKUP mv x = SOME b) ⇒
    (∀x. MEM x (fv_tbll p) ⇒ ∃b. ALOOKUP mv x = SOME b)
Proof
  gvs[fv_tbll_def]  
QED

             
        
           
val _ = export_theory ();

    
