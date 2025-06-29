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
  fv_atom ((Var x):atom_var) = [x] ∧
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

 
(* Top-level table semantics, return the starting state as well*)       
Definition sem_tables_def:
  sem_tables ((tbll: 'a table_list),st_in) mv =
   match_tbll tbll mv st_in
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


Definition mk_substitute_tables_def:
  mk_substitute_tables ((tbll: 'a table_list), st_in) x b =
   (mk_substitute_tbll tbll x b, st_in:num)
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


Definition simp_tables_def:
  simp_tables ((tbll: 'a table_list), st_in) =
   (simp_tbll tbll, st_in:num)
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



Definition final_tables_def:
  final_tables (tbll, st_in) =
  final_tbll tbll st_in
End

        


(*  free variables tables *)

        
Definition fv_row_def:
  fv_row atoml =
  let fv_in_row = MAP (\atom. fv_atom atom) atoml in
    nub(FLAT fv_in_row)
End


Definition fv_tbl_def:
  fv_tbl (tbl: 'a table) =
  (let fv_in_tbl = MAP(\(atom,st_num,res). fv_row atom) tbl in
      nub (FLAT fv_in_tbl))
End
        
        

    
Definition fv_tbll_def:
  fv_tbll (tbll: 'a table_list) =
  let fv_in_tbll = MAP (\tbl. fv_tbl tbl) tbll in
    nub(FLAT fv_in_tbll)
End


        
Definition fv_tables_def:
  fv_tables (tbll, st_in) =
  fv_tbll tbll
End



        
                                                                 
Definition table_structure_def:
  table_structure =
  <|
    sem := sem_tables;
    sub := mk_substitute_tables;
    simp := simp_tables;
    final := final_tables;
    fv := fv_tables;
  |>
End            



               
Theorem fv_mem_tbll_thm:
  ∀ tbll tbl mv.
    (∀x. MEM x (fv_tbll (tbl::tbll)) ⇒ ∃b. ALOOKUP mv x = SOME b) ⇒
    (∀x. MEM x (fv_tbll  tbll) ⇒ ∃b. ALOOKUP mv x = SOME b)
Proof
  gvs[fv_tbll_def]
QED

        
Theorem fv_mem_tbll_hd_thm:
  ∀ tbll tbl mv.
    (∀x. MEM x (fv_tbll (tbl::tbll)) ⇒ ∃b. ALOOKUP mv x = SOME b) ⇒
    (∀x. MEM x (fv_tbl  tbl) ⇒ ∃b. ALOOKUP mv x = SOME b)
Proof
  gvs[fv_tbll_def, fv_tbl_def]
QED
        

Theorem fv_mem_tbl_thm:
  ∀ tbl h mv.
    (∀x. MEM x (fv_tbl (h::tbl)) ⇒ ∃b. ALOOKUP mv x = SOME b) ⇒
    (∀x. MEM x (fv_tbl  tbl) ⇒ ∃b. ALOOKUP mv x = SOME b)
Proof
  gvs[fv_tbl_def]
QED


Theorem fv_mem_tbl_h_thm:
  ∀ tbl h mv.
    (∀x. MEM x (fv_tbl (h::tbl)) ⇒ ∃b. ALOOKUP mv x = SOME b) ⇒
    (∀x. MEM x (fv_tbl  [h]) ⇒ ∃b. ALOOKUP mv x = SOME b)
Proof
  gvs[fv_tbl_def]
QED        



Theorem fv_mem_row_thm:
  ∀ atoml h mv.
    (∀x. MEM x (fv_row (h::atoml)) ⇒ ∃b. ALOOKUP mv x = SOME b) ⇒
    (∀x. MEM x (fv_row atoml) ⇒ ∃b. ALOOKUP mv x = SOME b)
Proof
  gvs[fv_row_def]
QED 



Theorem fv_mem_row_h_thm:
  ∀ atoml h mv.
    (∀x. MEM x (fv_row (h::atoml)) ⇒ ∃b. ALOOKUP mv x = SOME b) ⇒
    (∀x. MEM x (fv_row [h]) ⇒ ∃b. ALOOKUP mv x = SOME b)
Proof
  gvs[fv_row_def]
QED


Theorem fv_mem_atom_not_thm:        
  ∀ atom mv.
    (∀x. MEM x (fv_row [Not atom]) ⇒ ∃b. ALOOKUP mv x = SOME b) ⇒
    (∀x. MEM x (fv_row [atom]) ⇒ ∃b. ALOOKUP mv x = SOME b)
Proof     
  gvs[fv_row_def, fv_atom_def]
QED


          
Theorem mk_substitute_tbl_normalize1:
  ∀h rows x b.
       mk_substitute_tbl (h::rows) x b =
       mk_substitute_tbl [h] x b ⧺ mk_substitute_tbl rows x b
Proof
  gvs[mk_substitute_tbl_def]
QED


Theorem mk_substitute_tbl_normalize2:
  ∀atoml st_num res rows x b.
       mk_substitute_tbl ((atoml,st_num,res)::rows) x b =
       (mk_substitute_row atoml x b,st_num,res)::mk_substitute_tbl rows x b
Proof
  gvs[mk_substitute_tbl_def]
QED


Theorem simp_tbl_normalize1:
  ∀atoml st_num res rows x b.
       simp_tbl ((atoml,st_num,res)::rows) =
       (simp_row atoml,st_num,res)::simp_tbl rows
Proof
  gvs[simp_tbl_def]
QED


        
Theorem sub_then_simp_answer_indeed_in_fv:
  ∀ atom h' b s.                      
    (simp_atom (mk_substitute_atom atom h' b) = Var s) ⇒
    MEM s (fv_atom atom)
Proof
  Induct >>
  rpt strip_tac >>
  gvs[fv_atom_def, mk_substitute_atom_def, simp_atom_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  gvs[fv_atom_def, mk_substitute_atom_def, simp_atom_def] 
QED


Triviality simp_fv_not_triv1:
  ∀ atom h' b x a.
    simp_atom (mk_substitute_atom atom h' b) = Not a ∧
    MEM x (fv_atom a) ⇒
    MEM x (fv_atom (simp_atom (mk_substitute_atom atom h' b)))
Proof
  gvs[fv_atom_def, mk_substitute_atom_def, simp_atom_def] 
QED
        

Triviality mem_fv_sub_simp_tbl_triv1:
  ∀ atom h' b x.        
    MEM x (fv_atom (simp_atom (mk_substitute_atom atom h' b))) ⇒
    MEM x (fv_atom atom)
Proof
  Induct >>
  rpt strip_tac >>
  gvs[fv_atom_def, mk_substitute_atom_def, simp_atom_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  gvs[fv_atom_def, mk_substitute_atom_def, simp_atom_def] >>
  imp_res_tac sub_then_simp_answer_indeed_in_fv >>
  imp_res_tac simp_fv_not_triv1 >>
  res_tac 
QED
             

Theorem sub_then_simp_not_answer_indeed_in_fv:
  ∀ atom atom' h' b mv.                      
    (∀x. MEM x (fv_atom atom) ⇒ ∃b. ALOOKUP mv x = SOME b) ∧
    simp_atom (mk_substitute_atom atom h' b) = Not atom'
    ⇒
    (∀x. MEM x (fv_atom atom') ⇒ ∃b. ALOOKUP mv x = SOME b)
Proof
  Induct >>
  rpt strip_tac >>
  gvs[fv_atom_def, mk_substitute_atom_def, simp_atom_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  gvs[fv_atom_def, mk_substitute_atom_def, simp_atom_def] >>
  assume_tac sub_then_simp_answer_indeed_in_fv >>
  first_x_assum (strip_assume_tac o (Q.SPECL [‘atom’, ‘h'’, ‘b’, ‘s’])) >>
  gvs[] >>
  imp_res_tac mem_fv_sub_simp_tbl_triv1 >> res_tac >> gvs[]
QED
      

Theorem mem_imp_sem_tbl:
  ∀ atom mv.
    (∀x. MEM x (fv_atom atom) ⇒ ∃b. ALOOKUP mv x = SOME b) ⇒
    sem_atom atom mv ≠ NONE ∧ ∃ b' . sem_atom atom mv = SOME b'
Proof
  Induct >>
  rw[fv_atom_def] >> gvs[AllCaseEqs()] >>
  gvs[sem_atom_def, simp_atom_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) 
QED


Triviality non_empty_line_simp_not_empty:
  ∀ atoml h' b.
    atoml ≠ [] ⇔  simp_row (mk_substitute_row atoml h' b) ≠ []
Proof
  Induct >> gvs[mk_substitute_row_def, simp_row_def]
QED



Theorem lookup_implies_sem_atoms_same:
  ∀ atom h' b bool mv.
    ALOOKUP mv h' = SOME b  ⇒
    (sem_atom atom mv = SOME bool ⇔
       sem_atom (simp_atom (mk_substitute_atom atom h' b)) mv = SOME bool)
Proof
  Induct >>
  rpt strip_tac >>
  rpt (gvs[mk_substitute_atom_def, simp_atom_def, sem_atom_def] >>
       BasicProvers.FULL_CASE_TAC >>
       res_tac >>               
       gvs[]) >>
  gvs[mk_substitute_atom_def, simp_atom_def, sem_atom_def] >>
  metis_tac[]
QED
           

Theorem lookup_implies_sem_atoml_same1:
  ∀ atoml h' b mv.
    ALOOKUP mv h' = SOME b ∧
    EVERY (λminipred. sem_atom minipred mv = SOME T) atoml ⇒
    EVERY ((λminipred. sem_atom minipred mv = SOME T)) (simp_row (mk_substitute_row atoml h' b))
Proof
  Induct >>
  rpt strip_tac >>            
  gvs[mk_substitute_row_def, simp_row_def] >>
  imp_res_tac lookup_implies_sem_atoms_same
QED


Theorem lookup_implies_sem_atoml_same2:
  ∀ atoml h' b mv.
    ALOOKUP mv h' = SOME b ∧
    EVERY ((λminipred. sem_atom minipred mv = SOME T)) (simp_row (mk_substitute_row atoml h' b)) ⇒
    EVERY (λminipred. sem_atom minipred mv = SOME T) atoml
Proof
  Induct >>
  rpt strip_tac >> 
  gvs[mk_substitute_row_def, simp_row_def] >>
  imp_res_tac lookup_implies_sem_atoms_same >> gvs[] >> res_tac 
QED


         
Theorem  sem_hd_line_imp_is_match_row:
  ∀ atoml st_num res h' b s_in mv.
    ALOOKUP mv h' = SOME b ∧
    sem_tables ([simp_tbl (mk_substitute_tbl [(atoml,st_num,res)] h' b)],s_in) mv =
    sem_tables ([[(atoml,st_num,res)]],s_in) mv  ⇒
    is_match_row s_in st_num atoml mv =
    is_match_row s_in st_num (simp_row (mk_substitute_row atoml h' b)) mv
Proof
  rpt strip_tac >>
  gvs[sem_tables_def, match_tbll_def] >>
  
  Cases_on ‘match_tbl (simp_tbl (mk_substitute_tbl [(atoml,st_num,res)] h' b)) mv s_in’ >>
  gvs[] >>
  Cases_on ‘match_tbl [(atoml,st_num,res)] mv s_in’ >>
  gvs[] >>
  
  
  (gvs[match_tbl_def, min_idx_till_def] >>
   rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 
   gvs[check_all_rows_match_def] >>
                    
   imp_res_tac INDEX_FIND_NONE_EXISTS >>
   gvs[] >>
   gvs[mk_substitute_tbl_def, simp_tbl_def] >>
   
   imp_res_tac P_holds_on_curent >>
   PairCases_on ‘r’ >>
   gvs[]) >>
  
  
  gvs[is_match_row_def] >>
  rpt strip_tac >>
  gvs[is_atoml_true_def] >>
  gvs[INDEX_FIND_EQ_SOME_0] >>
  gvs[is_match_row_def] >>
  gvs[is_atoml_true_def] >|[
    
    imp_res_tac lookup_implies_sem_atoml_same1 >> gvs[] >>
    imp_res_tac NOT_EVERY
    ,
    imp_res_tac non_empty_line_simp_not_empty
    ,
    
    imp_res_tac lookup_implies_sem_atoml_same2 >> gvs[] >>
    imp_res_tac NOT_EVERY
    ,
    
    imp_res_tac non_empty_line_simp_not_empty >> gvs[]
  ]
QED



Theorem is_match_row_substitute_preserve1:
  ∀ atoml mv h' b s_in st_num.        
    ALOOKUP mv h' = SOME b ∧
    is_match_row s_in st_num atoml mv ⇒
    is_match_row s_in st_num (simp_row (mk_substitute_row atoml h' b)) mv
Proof
  Induct >>
  gvs[is_match_row_def] >>
  rpt strip_tac >>
  gvs[is_atoml_true_def] >>
  (
  imp_res_tac lookup_implies_sem_atoml_same1 >> gvs[] >>
  gvs[mk_substitute_row_def, simp_row_def] >>
  imp_res_tac lookup_implies_sem_atoms_same
  )
QED



Theorem is_match_row_substitute_preserve2:
  ∀ atoml mv h' b s_in st_num.        
    ALOOKUP mv h' = SOME b ∧
    is_match_row s_in st_num (simp_row (mk_substitute_row atoml h' b)) mv ⇒
    is_match_row s_in st_num atoml mv
Proof
  Induct >>
  gvs[is_match_row_def] >>
  rpt strip_tac >>
  gvs[is_atoml_true_def] >>
  (
  imp_res_tac lookup_implies_sem_atoml_same2 >> 
  gvs[mk_substitute_row_def, simp_row_def] 
  )
QED



Theorem is_match_row_substitute_preserve:
  ∀ atoml mv h' b (s_in:num) st_num.        
    ALOOKUP mv h' = SOME b ⇒
    (is_match_row s_in st_num (simp_row (mk_substitute_row atoml h' b)) mv =
    is_match_row s_in st_num atoml mv)
Proof
  rpt strip_tac >>
  EQ_TAC >>
  metis_tac[is_match_row_substitute_preserve1, is_match_row_substitute_preserve2]
QED



Theorem exists_is_match_row_after_subst_simp:        
  ∀ tbl s_in h' b mv.
    ALOOKUP mv h' = SOME b ∧
    EXISTS (λ(p,a). p) (MAP (λ(atoml,st_num,res). (is_match_row s_in st_num atoml mv,res)) tbl) ⇒
    EXISTS (λ(p,a). p) (MAP (λ(atoml,st_num,res). (is_match_row s_in st_num atoml mv,res))
                            (simp_tbl (mk_substitute_tbl tbl h' b)))
Proof
  Induct >-
   gvs[mk_substitute_tbl_def, simp_tbl_def] >>
  rpt strip_tac >>
  simp[mk_substitute_tbl_def, simp_tbl_def] >>
  gvs[] >|[
  
    PairCases_on ‘h’ >>
    rename1 ‘(atoml, st_num, res)’ >>
    gvs[MAP_MAP_o] >>
    gvs[EXISTS_MAP] >>
    imp_res_tac is_match_row_substitute_preserve1 >> gvs[]
    ,
    res_tac >>
    gvs[mk_substitute_tbl_def, simp_tbl_def]
  ]    
QED


Theorem exists_is_match_row_before_subst_simp:        
  ∀ tbl s_in h' b mv.
    ALOOKUP mv h' = SOME b ∧
    EXISTS (λ(p,a). p) (MAP (λ(atoml,st_num,res). (is_match_row s_in st_num atoml mv,res))
                            (simp_tbl (mk_substitute_tbl tbl h' b))) ⇒
    EXISTS (λ(p,a). p) (MAP (λ(atoml,st_num,res). (is_match_row s_in st_num atoml mv,res)) tbl)
Proof
  Induct >-
   gvs[mk_substitute_tbl_def, simp_tbl_def] >>
  rpt strip_tac >>
  gvs[mk_substitute_tbl_def, simp_tbl_def] >>
  gvs[] >|[
  
    PairCases_on ‘h’ >>
    rename1 ‘(atoml, st_num, res)’ >>
    gvs[MAP_MAP_o] >>
    gvs[EXISTS_MAP] >>
    imp_res_tac is_match_row_substitute_preserve2 >> gvs[]
    ,
    res_tac >>
    gvs[mk_substitute_tbl_def, simp_tbl_def]
  ]    
QED




Theorem is_match_row_lists_subst_simp_eq:        
∀tbl h' b mv s_in.
       ALOOKUP mv h' = SOME b ⇒
       MAP (λ(atoml,st_num,res). (is_match_row s_in st_num atoml mv,res))
         (simp_tbl (mk_substitute_tbl tbl h' b)) =
       MAP (λ(atoml,st_num,res). (is_match_row s_in st_num atoml mv,res)) tbl 
Proof
  Induct >>
  rpt strip_tac >>
  gvs[mk_substitute_tbl_def,simp_tbl_def] >>
  PairCases_on ‘h’ >>
  rename1 ‘(atoml, st_num, res)’ >>
  gvs[MAP_MAP_o] >>
  gvs[EXISTS_MAP] >>
  
  imp_res_tac is_match_row_substitute_preserve >>
  gvs[]
QED




Theorem subst_simp_sem_tables_INDEX_FIND_congruence:
  ∀ tbl mv s_in h' b i.
    ALOOKUP mv h' = SOME b  ⇒
    INDEX_FIND i (λ(p,a). p)
               (MAP (λ(atoml,st_num,res). (is_match_row s_in st_num atoml mv,res)) (simp_tbl (mk_substitute_tbl tbl h' b))) =
    INDEX_FIND i (λ(p,a). p)
               (MAP (λ(atoml,st_num,res). (is_match_row s_in st_num atoml mv,res)) tbl)

Proof
  rpt strip_tac >>
  imp_res_tac is_match_row_lists_subst_simp_eq >>
  gvs[]
QED



Theorem subst_check_rows_sem_tables_INDEX_FIND_congruence:
  ∀ tbl mv s_in h' b.
    ALOOKUP mv h' = SOME b  ⇒
    (check_all_rows_match s_in(simp_tbl (mk_substitute_tbl tbl h' b)) mv) =
    (check_all_rows_match s_in tbl mv)
Proof
  gvs[check_all_rows_match_def] >>
  rpt strip_tac >>
  imp_res_tac is_match_row_lists_subst_simp_eq >>
  gvs[]
QED
                      

Theorem min_idx_till_subst_simp_invariant1:
  ∀ tbl mv s_in h' b atoml st_num res .
      ALOOKUP mv h' = SOME b  ⇒
      min_idx_till (check_all_rows_match s_in (simp_tbl (mk_substitute_tbl ((atoml,st_num,res)::tbl) h' b)) mv) T =
      min_idx_till (check_all_rows_match s_in ((atoml,st_num,res)::tbl) mv) T
Proof
  rpt strip_tac >> 
  gvs[min_idx_till_def] >>
  imp_res_tac subst_check_rows_sem_tables_INDEX_FIND_congruence >>
  gvs[]  
QED


Theorem min_idx_till_subst_simp_invariant2:
  ∀ tbl mv s_in h' b  .
      ALOOKUP mv h' = SOME b  ⇒
      min_idx_till (check_all_rows_match s_in (simp_tbl (mk_substitute_tbl (tbl) h' b)) mv) T =
      min_idx_till (check_all_rows_match s_in (tbl) mv) T
Proof
  rpt strip_tac >> 
  gvs[min_idx_till_def] >>
  imp_res_tac subst_check_rows_sem_tables_INDEX_FIND_congruence >>
  gvs[]  
QED


Theorem sem_tables_subst_simp_invariant:
  ∀ tbl mv s_in h' b row .
    ALOOKUP mv h' = SOME b   ⇒
    sem_tables ([simp_tbl (mk_substitute_tbl (row::tbl) h' b)],s_in) mv =
    sem_tables ([row::tbl],s_in) mv
Proof
  rpt strip_tac >>
  PairCases_on ‘row’ >> rename1 ‘(atoml,st_num,res)’ >>
  gvs[] >>
        
  simp[sem_tables_def, match_tbll_def] >>
  gvs[match_tbl_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  
  imp_res_tac min_idx_till_subst_simp_invariant1 >> gvs[] 
QED
  

     
Theorem prop1_var_single_tbl_verbose:
  ∀ tbl mv h' b s_in.
    ALOOKUP mv h' = SOME b ⇒
    sem_tables (simp_tbll (mk_substitute_tbll [tbl] h' b),s_in) mv =
    sem_tables ([tbl],s_in) mv
Proof
  Cases >-
   (gvs[fv_tbll_def, mk_substitute_tbll_def, simp_tbll_def] >> 
   gvs[fv_tbl_def, mk_substitute_tbl_def, simp_tbl_def]) >> 

  rpt strip_tac >>
  gvs[mk_substitute_tbll_def, simp_tbll_def] >> 
  imp_res_tac sem_tables_subst_simp_invariant >>
  gvs[]  
QED
            


            
Theorem prop1_var_tables_verbose:
  ∀ tbls h b mv s_in.
    ALOOKUP mv h = SOME b 
    ⇒
    sem_tables (simp_tbll (mk_substitute_tbll tbls h b),s_in) mv =
    sem_tables (tbls,s_in) mv
Proof

  Induct_on ‘tbls’ >> rpt strip_tac >-
   gvs[fv_tbll_def, mk_substitute_tbll_def, simp_tbll_def] >> 
  rename1 ‘(tbl::tbll)’ >>

  imp_res_tac prop1_var_single_tbl_verbose >>
  first_x_assum (strip_assume_tac o (Q.SPECL [‘tbl’, ‘s_in’])) >>
                
  Cases_on ‘tbll’ >> gvs[] >> 
  rename1 ‘(tbl::nexttbl::tbll)’ >>

  gvs[sem_tables_def, match_tbll_def] >>
  Cases_on ‘match_tbl tbl mv s_in’ >> gvs[] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>

  gvs[mk_substitute_tbll_def, simp_tbll_def] >>
  gvs[match_tbll_def] >>     
  Cases_on ‘match_tbl (simp_tbl (mk_substitute_tbl tbl h' b)) mv s_in’ >> gvs[] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>

  gvs[match_tbl_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  imp_res_tac min_idx_till_subst_simp_invariant2 >> gvs[]
QED

                          
               
Theorem prop1_var_tables:
  prop1 table_structure
Proof
  rgs[prop1_def, table_structure_def, fv_in_p_def] >>

  rpt strip_tac >>
  Cases_on ‘p’ >>
  rename1 ‘(tbls, s_in)’ >>

  gvs[fv_tables_def, mk_substitute_tables_def, simp_tables_def] >>
  imp_res_tac prop1_var_tables_verbose >> gvs[]    
QED


        
           
val _ = export_theory ();

    
